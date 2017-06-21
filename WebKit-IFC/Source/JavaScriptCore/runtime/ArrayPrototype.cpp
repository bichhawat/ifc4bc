/*
 *  Copyright (C) 1999-2000 Harri Porten (porten@kde.org)
 *  Copyright (C) 2003, 2007, 2008, 2009, 2011 Apple Inc. All rights reserved.
 *  Copyright (C) 2003 Peter Kelly (pmk@post.com)
 *  Copyright (C) 2006 Alexey Proskuryakov (ap@nypop.com)
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301
 *  USA
 *
 */

#include "config.h"
#include "ArrayPrototype.h"

#include "CachedCall.h"
#include "CodeBlock.h"
#include "Interpreter.h"
#include "JIT.h"
#include "JSStringBuilder.h"
#include "JSStringJoiner.h"
#include "Lookup.h"
#include "ObjectPrototype.h"
#include "Operations.h"
#include "StringRecursionChecker.h"
#include <algorithm>
#include <wtf/Assertions.h>
#include <wtf/HashSet.h>

namespace JSC {

ASSERT_CLASS_FITS_IN_CELL(ArrayPrototype);

static JSValue JSC_HOST_CALL arrayProtoFuncToString(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncToLocaleString(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncConcat(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncJoin(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncPop(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncPush(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncReverse(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncShift(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncSlice(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncSort(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncSplice(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncUnShift(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncEvery(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncForEach(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncSome(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncIndexOf(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncFilter(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncMap(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncReduce(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncReduceRight(ExecState*);
static JSValue JSC_HOST_CALL arrayProtoFuncLastIndexOf(ExecState*);
}

#include "ArrayPrototype.lut.h"

namespace JSC {

static inline bool isNumericCompareFunction(ExecState* exec, CallType callType, const CallData& callData)
{
    if (callType != CallTypeJS)
        return false;

    FunctionExecutable* executable = callData.js.functionExecutable;

    JSObject* error = executable->compileForCall(exec, callData.js.scopeChain);
    if (error)
        return false;

    return executable->generatedBytecodeForCall().isNumericCompareFunction();
}

// ------------------------------ ArrayPrototype ----------------------------

const ClassInfo ArrayPrototype::s_info = {"Array", &JSArray::s_info, 0, ExecState::arrayPrototypeTable, CREATE_METHOD_TABLE(ArrayPrototype)};

/* Source for ArrayPrototype.lut.h
@begin arrayPrototypeTable 16
  toString       arrayProtoFuncToString       DontEnum|Function 0
  toLocaleString arrayProtoFuncToLocaleString DontEnum|Function 0
  concat         arrayProtoFuncConcat         DontEnum|Function 1
  join           arrayProtoFuncJoin           DontEnum|Function 1
  pop            arrayProtoFuncPop            DontEnum|Function 0
  push           arrayProtoFuncPush           DontEnum|Function 1
  reverse        arrayProtoFuncReverse        DontEnum|Function 0
  shift          arrayProtoFuncShift          DontEnum|Function 0
  slice          arrayProtoFuncSlice          DontEnum|Function 2
  sort           arrayProtoFuncSort           DontEnum|Function 1
  splice         arrayProtoFuncSplice         DontEnum|Function 2
  unshift        arrayProtoFuncUnShift        DontEnum|Function 1
  every          arrayProtoFuncEvery          DontEnum|Function 1
  forEach        arrayProtoFuncForEach        DontEnum|Function 1
  some           arrayProtoFuncSome           DontEnum|Function 1
  indexOf        arrayProtoFuncIndexOf        DontEnum|Function 1
  lastIndexOf    arrayProtoFuncLastIndexOf    DontEnum|Function 1
  filter         arrayProtoFuncFilter         DontEnum|Function 1
  reduce         arrayProtoFuncReduce         DontEnum|Function 1
  reduceRight    arrayProtoFuncReduceRight    DontEnum|Function 1
  map            arrayProtoFuncMap            DontEnum|Function 2
@end
*/

// ECMA 15.4.4
ArrayPrototype::ArrayPrototype(JSGlobalObject* globalObject, Structure* structure)
    : JSArray(globalObject->globalData(), structure)
{
}

void ArrayPrototype::finishCreation(JSGlobalObject* globalObject)
{
    Base::finishCreation(globalObject->globalData());
    ASSERT(inherits(&s_info));
}

bool ArrayPrototype::getOwnPropertySlot(JSCell* cell, ExecState* exec, PropertyName propertyName, PropertySlot& slot)
{
    return getStaticFunctionSlot<JSArray>(exec, ExecState::arrayPrototypeTable(exec), jsCast<ArrayPrototype*>(cell), propertyName, slot);
}

bool ArrayPrototype::getOwnPropertyDescriptor(JSObject* object, ExecState* exec, PropertyName propertyName, PropertyDescriptor& descriptor)
{
    return getStaticFunctionDescriptor<JSArray>(exec, ExecState::arrayPrototypeTable(exec), jsCast<ArrayPrototype*>(object), propertyName, descriptor);
}

// ------------------------------ Array Functions ----------------------------

// Helper function
static JSValue getProperty(ExecState* exec, JSObject* obj, unsigned index)
{
    PropertySlot slot(obj);
    if (!obj->getPropertySlot(exec, index, slot))
        return JSValue();
    return slot.getValue(exec, index);
}

static void putProperty(ExecState* exec, JSObject* obj, PropertyName propertyName, JSValue value)
{
    PutPropertySlot slot;
    obj->methodTable()->put(obj, exec, propertyName, value, slot);
}

static unsigned argumentClampedIndexFromStartOrEnd(ExecState* exec, int argument, unsigned length, unsigned undefinedValue = 0)
{
    JSValue value = exec->argument(argument);
    if (value.isUndefined())
        return undefinedValue;

    double indexDouble = value.toInteger(exec);
    if (indexDouble < 0) {
        indexDouble += length;
        return indexDouble < 0 ? 0 : static_cast<unsigned>(indexDouble);
    }
    return indexDouble > length ? length : static_cast<unsigned>(indexDouble);
}


// The shift/unshift function implement the shift/unshift behaviour required
// by the corresponding array prototype methods, and by splice. In both cases,
// the methods are operating an an array or array like object.
//
//  header  currentCount  (remainder)
// [------][------------][-----------]
//  header  resultCount  (remainder)
// [------][-----------][-----------]
//
// The set of properties in the range 'header' must be unchanged. The set of
// properties in the range 'remainder' (where remainder = length - header -
// currentCount) will be shifted to the left or right as appropriate; in the
// case of shift this must be removing values, in the case of unshift this
// must be introducing new values.
static inline void shift(ExecState* exec, JSObject* thisObj, unsigned header, unsigned currentCount, unsigned resultCount, unsigned length)
{
    ASSERT(currentCount > resultCount);
    unsigned count = currentCount - resultCount;

    ASSERT(header <= length);
    ASSERT(currentCount <= (length - header));

    if (!header && isJSArray(thisObj) && asArray(thisObj)->shiftCount(exec, count))
        return;

    for (unsigned k = header; k < length - currentCount; ++k) {
        unsigned from = k + currentCount;
        unsigned to = k + resultCount;
        PropertySlot slot(thisObj);
        if (thisObj->getPropertySlot(exec, from, slot)) {
            JSValue value = slot.getValue(exec, from);
            if (exec->hadException())
                return;
            thisObj->methodTable()->putByIndex(thisObj, exec, to, value, true);
            if (exec->hadException())
                return;
        } else if (!thisObj->methodTable()->deletePropertyByIndex(thisObj, exec, to)) {
            throwTypeError(exec, "Unable to delete property.");
            return;
        }
    }
    for (unsigned k = length; k > length - count; --k) {
        if (!thisObj->methodTable()->deletePropertyByIndex(thisObj, exec, k - 1)) {
            throwTypeError(exec, "Unable to delete property.");
            return;
        }
    }
}
static inline void unshift(ExecState* exec, JSObject* thisObj, unsigned header, unsigned currentCount, unsigned resultCount, unsigned length)
{
    ASSERT(resultCount > currentCount);
    unsigned count = resultCount - currentCount;

    ASSERT(header <= length);
    ASSERT(currentCount <= (length - header));

    // Guard against overflow.
    if (count > (UINT_MAX - length)) {
        throwOutOfMemoryError(exec);
        return;
    }

    if (!header && isJSArray(thisObj) && asArray(thisObj)->unshiftCount(exec, count))
        return;

    for (unsigned k = length - currentCount; k > header; --k) {
        unsigned from = k + currentCount - 1;
        unsigned to = k + resultCount - 1;
        PropertySlot slot(thisObj);
        if (thisObj->getPropertySlot(exec, from, slot)) {
            JSValue value = slot.getValue(exec, from);
            if (exec->hadException())
                return;
            thisObj->methodTable()->putByIndex(thisObj, exec, to, value, true);
        } else if (!thisObj->methodTable()->deletePropertyByIndex(thisObj, exec, to)) {
            throwTypeError(exec, "Unable to delete property.");
            return;
        }
        if (exec->hadException())
            return;
    }
}

JSValue JSC_HOST_CALL arrayProtoFuncToString(ExecState* exec)
{
    JSValue thisValue = exec->hostThisValue();

    // 1. Let array be the result of calling ToObject on the this value.
    JSObject* thisObject = thisValue.toObject(exec);
    if (exec->hadException())
        return (jsUndefined());
    
    // 2. Let func be the result of calling the [[Get]] internal method of array with argument "join".
    JSValue function = JSValue(thisObject).get(exec, exec->propertyNames().join);

    // 3. If IsCallable(func) is false, then let func be the standard built-in method Object.prototype.toString (15.2.4.2).
    if (!function.isCell())
        return (jsMakeNontrivialString(exec, "[object ", thisObject->methodTable()->className(thisObject), "]"));
    CallData callData;
    CallType callType = getCallData(function, callData);
    if (callType == CallTypeNone)
        return (jsMakeNontrivialString(exec, "[object ", thisObject->methodTable()->className(thisObject), "]"));

    // 4. Return the result of calling the [[Call]] internal method of func providing array as the this value and an empty arguments list.
    if (!isJSArray(thisObject) || callType != CallTypeHost || callData.native.function != arrayProtoFuncJoin)
        return (call(exec, function, callType, callData, thisObject, exec->emptyList()));

    ASSERT(isJSArray(thisValue));
    JSArray* thisObj = asArray(thisValue);
    
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (jsUndefined());

    StringRecursionChecker checker(exec, thisObj);
    if (JSValue earlyReturnValue = checker.earlyReturnValue())
        return (earlyReturnValue);

    unsigned totalSize = length ? length - 1 : 0;
    Vector<RefPtr<StringImpl>, 256> strBuffer(length);
    bool allStrings8Bit = true;

    for (unsigned k = 0; k < length; k++) {
        JSValue element;
        if (thisObj->canGetIndex(k))
            element = thisObj->getIndex(k);
        else
            element = thisObj->get(exec, k);
        
        if (element.isUndefinedOrNull())
            continue;
        
        UString str = element.toUString(exec);
        strBuffer[k] = str.impl();
        totalSize += str.length();
        allStrings8Bit = allStrings8Bit && str.is8Bit();
        
        if (!strBuffer.data()) {
            throwOutOfMemoryError(exec);
        }
        
        if (exec->hadException())
            break;
    }
    if (!totalSize)
        return (jsEmptyString(exec));

    if (allStrings8Bit) {
        Vector<LChar> buffer;
        buffer.reserveCapacity(totalSize);
        if (!buffer.data())
            return (throwOutOfMemoryError(exec));
        
        for (unsigned i = 0; i < length; i++) {
            if (i)
                buffer.append(',');
            if (RefPtr<StringImpl> rep = strBuffer[i])
                buffer.append(rep->characters8(), rep->length());
        }
        ASSERT(buffer.size() == totalSize);
        return (jsString(exec, UString::adopt(buffer)));        
    }

    Vector<UChar> buffer;
    buffer.reserveCapacity(totalSize);
    if (!buffer.data())
        return (throwOutOfMemoryError(exec));
        
    for (unsigned i = 0; i < length; i++) {
        if (i)
            buffer.append(',');
        if (RefPtr<StringImpl> rep = strBuffer[i])
            buffer.append(rep->characters(), rep->length());
    }
    ASSERT(buffer.size() == totalSize);
    return (jsString(exec, UString::adopt(buffer)));
}

JSValue JSC_HOST_CALL arrayProtoFuncToLocaleString(ExecState* exec)
{
    JSValue thisValue = exec->hostThisValue();

    if (!thisValue.inherits(&JSArray::s_info))
        return throwVMTypeError(exec);
    JSObject* thisObj = asArray(thisValue);

    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (jsUndefined());

    StringRecursionChecker checker(exec, thisObj);
    if (JSValue earlyReturnValue = checker.earlyReturnValue())
        return (earlyReturnValue);

    UString separator(",");
    JSStringJoiner stringJoiner(separator, length);
    for (unsigned k = 0; k < length; k++) {
        JSValue element = thisObj->get(exec, k);
        if (exec->hadException())
            return (jsUndefined());
        if (!element.isUndefinedOrNull()) {
            JSObject* o = element.toObject(exec);
            JSValue conversionFunction = o->get(exec, exec->propertyNames().toLocaleString);
            if (exec->hadException())
                return (jsUndefined());
            UString str;
            CallData callData;
            CallType callType = getCallData(conversionFunction, callData);
            if (callType != CallTypeNone)
                str = call(exec, conversionFunction, callType, callData, element, exec->emptyList()).toUString(exec);
            else
                str = element.toUString(exec);
            if (exec->hadException())
                return (jsUndefined());
            stringJoiner.append(str);
        }
    }

    return (stringJoiner.build(exec));
}

JSValue JSC_HOST_CALL arrayProtoFuncJoin(ExecState* exec)
{
    JSObject* thisObj = exec->hostThisValue().toObject(exec);
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (jsUndefined());

    JSValue ret;
    JSLabel eLabel;
    StringRecursionChecker checker(exec, thisObj);
    if (JSValue earlyReturnValue = checker.earlyReturnValue()) {
        ret = (earlyReturnValue);
        ret.setValueLabel(thisObj->joinObjectLabel(JSLabel(JSLabel::argLabel[0])));
        return ret;
    }

    UString separator;
    if (!exec->argument(0).isUndefined())
        separator = exec->argument(0).toUString(exec);
    if (separator.isNull())
        separator = UString(",");

    JSStringJoiner stringJoiner(separator, length);

    unsigned k = 0;
    if (isJSArray(thisObj)) {
        JSArray* array = asArray(thisObj);

        for (; k < length; k++) {
            if (!array->canGetIndex(k))
                break;

            JSValue element = array->getIndex(k);
            eLabel = eLabel.Join(element.getValueLabel());
            if (!element.isUndefinedOrNull())
                stringJoiner.append(element.toUStringInline(exec));
            else
                stringJoiner.append(UString());
        }
    }

    for (; k < length; k++) {
        JSValue element = thisObj->get(exec, k);
        if (!element.isUndefinedOrNull())
            stringJoiner.append(element.toUStringInline(exec));
        else
            stringJoiner.append(UString());
    }

    JSLabel retLabel = thisObj->joinObjectLabel(JSLabel(JSLabel::argLabel[0]).Join(JSLabel(JSLabel::argLabel[1])).Join(eLabel));
    ret = (stringJoiner.build(exec));
    ret.setValueLabel(retLabel);
    return ret;
}

JSValue JSC_HOST_CALL arrayProtoFuncConcat(ExecState* exec)
{
    JSValue thisValue = exec->hostThisValue();
    JSArray* arr = constructEmptyArray(exec);
    unsigned n = 0;
    JSValue curArg = thisValue.toObject(exec);
    // IFC4BC - setting the label
    JSLabel finalLabel = thisValue.getValueLabel();
    if (exec->hadException())
        return (jsUndefined());
    size_t i = 0;
    size_t argCount = exec->argumentCount();
    while (1) {
        if (curArg.inherits(&JSArray::s_info)) {
            unsigned length = curArg.get(exec, exec->propertyNames().length).toUInt32(exec);
            JSObject* curObject = curArg.toObject(exec);
            for (unsigned k = 0; k < length; ++k) {
                JSValue v = getProperty(exec, curObject, k);
                finalLabel = finalLabel.Join(v.getValueLabel());
                if (exec->hadException())
                    return (jsUndefined());
                if (v)
                    arr->putDirectIndex(exec, n, v);
                n++;
            }
        } else {
            arr->putDirectIndex(exec, n, curArg);
            n++;
        }
        if (i == argCount)
            break;
        curArg = (exec->argument(i));
        finalLabel = finalLabel.Join(curArg.getValueLabel());
        ++i;
    }
    arr->setLength(exec, n);
    arr->setObjectLabel(finalLabel);
    return (arr);
}

JSValue JSC_HOST_CALL arrayProtoFuncPop(ExecState* exec)
{
    // IFC4BC
    JSValue thisValue = exec->hostThisValue();
    if (!JSLabel(JSLabel::pcGlobalLabel).NSU(asObject(thisValue)->getObjectLabel()))
    {
        // printf("IFC check in array-Pop failed\n");
        JSLabel::ABORT_FLAG = true;
        // return jsUndefined();
    }
    
    JSValue result=jsUndefined(); 
    result.setValueLabel(JSLabel(JSLabel::argLabel[0]));

    if (isJSArray(thisValue))
        return (asArray(thisValue)->pop(exec));

    JSObject* thisObj = thisValue.toObject(exec);
    
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (result);
    
    
    if (length == 0) {
        putProperty(exec, thisObj, exec->propertyNames().length, jsNumber(length));
        result = jsUndefined();
    } else {
        result = thisObj->get(exec, length - 1);
        result.setValueLabel(result.joinValueLabel(JSLabel(JSLabel::argLabel[0])));
        if (exec->hadException())
            return (result);
        if (!thisObj->methodTable()->deletePropertyByIndex(thisObj, exec, length - 1)) {
            throwTypeError(exec, "Unable to delete property.");
            return (result);
        }
        putProperty(exec, thisObj, exec->propertyNames().length, jsNumber(length - 1));
    }
    return (result);
}

JSValue JSC_HOST_CALL arrayProtoFuncPush(ExecState* exec)
{
    // IFC4BC
    JSValue thisValue = exec->hostThisValue();
    if (!JSLabel(JSLabel::pcGlobalLabel).NSU(asObject(thisValue)->getObjectLabel()))
    {
        // printf("IFC check in array-Push failed\n");
        JSLabel::ABORT_FLAG = true;
        // return jsUndefined();
    }
    JSValue retLength = jsUndefined();
    JSLabel retLabel = JSLabel(JSLabel::argLabel[0]).Join(JSLabel(JSLabel::argLabel[1]));
    retLength.setValueLabel(retLabel);

    if (isJSArray(thisValue) && exec->argumentCount() == 1) {
        JSArray* array = asArray(thisValue);
        array->push(exec, exec->argument(0));
        retLength = jsNumber(array->length());
        retLength.setValueLabel(retLength.joinValueLabel(retLabel));
        array->setObjectLabel(array->joinObjectLabel(retLabel));
        return (retLength);
    }

    JSObject* thisObj = thisValue.toObject(exec);
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (retLength);

    for (unsigned n = 0; n < exec->argumentCount(); n++) {
        // Check for integer overflow; where safe we can do a fast put by index.
        if (length + n >= length)
            thisObj->methodTable()->putByIndex(thisObj, exec, length + n, exec->argument(n), true);
        else {
            PutPropertySlot slot;
            Identifier propertyName(exec, JSValue(static_cast<int64_t>(length) + static_cast<int64_t>(n)).toUString(exec));
            thisObj->methodTable()->put(thisObj, exec, propertyName, exec->argument(n), slot);
        }
        if (exec->hadException())
            return (retLength);
    }

    JSValue newLength(static_cast<int64_t>(length) + static_cast<int64_t>(exec->argumentCount()));
    putProperty(exec, thisObj, exec->propertyNames().length, newLength);
    // IFC4BC - Low context adds a high value - can return length without labeling it high. Does not leak information 
    newLength.setValueLabel(retLabel);
    thisObj->setObjectLabel(thisObj->joinObjectLabel(retLabel));
    return (newLength);
}

JSValue JSC_HOST_CALL arrayProtoFuncReverse(ExecState* exec)
{
    
    JSObject* thisObj = exec->hostThisValue().toObject(exec);

    JSValue retLength = jsUndefined();
    JSLabel retLabel = JSLabel(JSLabel::argLabel[0]).Join(JSLabel::argLabel[1]);
    retLength.setValueLabel(retLabel);

    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (retLength);

    unsigned middle = length / 2;
    for (unsigned k = 0; k < middle; k++) {
        unsigned lk1 = length - k - 1;
        JSValue obj2 = getProperty(exec, thisObj, lk1);
        retLabel = retLabel.Join(obj2.getValueLabel());
        if (exec->hadException())
            return (retLength);
        JSValue obj = getProperty(exec, thisObj, k);
        retLabel = retLabel.Join(obj.getValueLabel());
        if (exec->hadException())
            return (retLength);

        if (obj2) {
            thisObj->methodTable()->putByIndex(thisObj, exec, k, obj2, true);
            if (exec->hadException())
                return (retLength);
        } else if (!thisObj->methodTable()->deletePropertyByIndex(thisObj, exec, k)) {
            throwTypeError(exec, "Unable to delete property.");
            return (retLength);
        }

        if (obj) {
            thisObj->methodTable()->putByIndex(thisObj, exec, lk1, obj, true);
            if (exec->hadException())
                return (retLength);
        } else if (!thisObj->methodTable()->deletePropertyByIndex(thisObj, exec, lk1)) {
            throwTypeError(exec, "Unable to delete property.");
            return (retLength);
        }
    }
    thisObj->setObjectLabel(thisObj->joinObjectLabel(retLabel));
    return (thisObj);
}

JSValue JSC_HOST_CALL arrayProtoFuncShift(ExecState* exec)
{
    // IFC4BC
    JSObject* thisObj = exec->hostThisValue().toObject(exec);
    if (!JSLabel(JSLabel::pcGlobalLabel).NSU(thisObj->getObjectLabel()))
    {
        // printf("IFC check in array-Shift failed\n");
        JSLabel::ABORT_FLAG = true;
        // return jsUndefined();
    }
    
    JSValue result=jsUndefined(); 
    result.setValueLabel(JSLabel(JSLabel::argLabel[0]));
    
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (jsUndefined());

    if (length == 0) {
        putProperty(exec, thisObj, exec->propertyNames().length, jsNumber(length));
        result = jsUndefined();
        result.setValueLabel(JSLabel(JSLabel::argLabel[0]));
    } else {
        result = thisObj->get(exec, 0);
        result.setValueLabel(result.joinValueLabel(JSLabel(JSLabel::argLabel[0])));
        shift(exec, thisObj, 0, 1, 0, length);
        if (exec->hadException())
            return (result);
        putProperty(exec, thisObj, exec->propertyNames().length, jsNumber(length - 1));
    }
    return (result);
}

JSValue JSC_HOST_CALL arrayProtoFuncSlice(ExecState* exec)
{
    // http://developer.netscape.com/docs/manuals/js/client/jsref/array.htm#1193713 or 15.4.4.10
    JSObject* thisObj = exec->hostThisValue().toObject(exec);
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (jsUndefined());

    // We return a new array
    JSArray* resObj = constructEmptyArray(exec);
    JSValue result = resObj;
    JSLabel resLabel = JSLabel(JSLabel::argLabel[0]).Join(JSLabel::argLabel[1]).Join(JSLabel::argLabel[2]);
    
    unsigned begin = argumentClampedIndexFromStartOrEnd(exec, 0, length);
    unsigned end = argumentClampedIndexFromStartOrEnd(exec, 1, length, length);

    unsigned n = 0;
    for (unsigned k = begin; k < end; k++, n++) {
        JSValue v = getProperty(exec, thisObj, k);
        resLabel = resLabel.Join(v.getValueLabel());
        if (exec->hadException()){
            result = jsUndefined();
            result.setValueLabel(resLabel);
            return (result);
        }
        if (v)
            resObj->putDirectIndex(exec, n, v);
    }
    resObj->setLength(exec, n);
    result.setValueLabel(resLabel);
    thisObj->setObjectLabel(thisObj->joinObjectLabel(resLabel));
    return (result);
}

JSValue JSC_HOST_CALL arrayProtoFuncSort(ExecState* exec)
{
    JSObject* thisObj = exec->hostThisValue().toObject(exec);
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (!length || exec->hadException())
        return (thisObj);

    JSValue function = exec->argument(0);
    JSLabel resLabel = JSLabel(JSLabel::argLabel[0]);
    JSValue result = jsUndefined();

    CallData callData;
    CallType callType = getCallData(function, callData);

    for (unsigned i = 0; i < length; ++i) {
        JSValue iObj = thisObj->get(exec, i);
        resLabel = resLabel.Join(iObj.getValueLabel());
        result.setValueLabel(resLabel);
    }
    
    if (thisObj->classInfo() == &JSArray::s_info && !asArray(thisObj)->inSparseMode()) {
        if (isNumericCompareFunction(exec, callType, callData))
            asArray(thisObj)->sortNumeric(exec, function, callType, callData);
        else if (callType != CallTypeNone)
            asArray(thisObj)->sort(exec, function, callType, callData);
        else
            asArray(thisObj)->sort(exec);
        return (thisObj);
    }

    // "Min" sort. Not the fastest, but definitely less code than heapsort
    // or quicksort, and much less swapping than bubblesort/insertionsort.
    for (unsigned i = 0; i < length - 1; ++i) {
        JSValue iObj = thisObj->get(exec, i);
        if (exec->hadException())
            return (result);
        unsigned themin = i;
        JSValue minObj = iObj;
        for (unsigned j = i + 1; j < length; ++j) {
            JSValue jObj = thisObj->get(exec, j);
            if (exec->hadException())
                return (result);
            double compareResult;
            if (jObj.isUndefined())
                compareResult = 1; // don't check minObj because there's no need to differentiate == (0) from > (1)
            else if (minObj.isUndefined())
                compareResult = -1;
            else if (callType != CallTypeNone) {
                MarkedArgumentBuffer l;
                l.append(jObj);
                l.append(minObj);
                compareResult = call(exec, function, callType, callData, jsUndefined(), l).toNumber(exec);
            } else
                compareResult = (jObj.toUStringInline(exec) < minObj.toUStringInline(exec)) ? -1 : 1;

            if (compareResult < 0) {
                themin = j;
                minObj = jObj;
            }
        }
        result.setValueLabel(resLabel);
        // Swap themin and i
        if (themin > i) {
            thisObj->methodTable()->putByIndex(thisObj, exec, i, minObj, true);
            if (exec->hadException())
                return (result);
            thisObj->methodTable()->putByIndex(thisObj, exec, themin, iObj, true);
            if (exec->hadException())
                return (result);
        }
    }
    return (thisObj);
}

JSValue JSC_HOST_CALL arrayProtoFuncSplice(ExecState* exec)
{
    // 15.4.4.12
    // IFC4BC
    JSObject* thisObj = exec->hostThisValue().toObject(exec);
    if (!JSLabel(JSLabel::pcGlobalLabel).NSU(thisObj->getObjectLabel()))
    {
        // printf("IFC check in array-Splice failed\n");
        JSLabel::ABORT_FLAG = true;
        // return jsUndefined();
    }
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (jsUndefined());

    if (!exec->argumentCount())
        return (constructEmptyArray(exec));

    unsigned begin = argumentClampedIndexFromStartOrEnd(exec, 0, length);

    unsigned deleteCount = length - begin;
    if (exec->argumentCount() > 1) {
        double deleteDouble = exec->argument(1).toInteger(exec);
        if (deleteDouble < 0)
            deleteCount = 0;
        else if (deleteDouble > length - begin)
            deleteCount = length - begin;
        else
            deleteCount = static_cast<unsigned>(deleteDouble);
    }

    JSArray* resObj = JSArray::tryCreateUninitialized(exec->globalData(), exec->lexicalGlobalObject()->arrayStructure(), deleteCount);
    if (!resObj)
        return (throwOutOfMemoryError(exec));

    JSValue result = resObj;
    JSGlobalData& globalData = exec->globalData();
    for (unsigned k = 0; k < deleteCount; k++) {
        JSValue v = getProperty(exec, thisObj, k + begin);
        if (exec->hadException())
            return (jsUndefined());
        resObj->initializeIndex(globalData, k, v);
    }
    resObj->completeInitialization(deleteCount);

    unsigned additionalArgs = std::max<int>(exec->argumentCount() - 2, 0);
    if (additionalArgs < deleteCount) {
        shift(exec, thisObj, begin, deleteCount, additionalArgs, length);
        if (exec->hadException())
            return (jsUndefined());
    } else if (additionalArgs > deleteCount) {
        unshift(exec, thisObj, begin, deleteCount, additionalArgs, length);
        if (exec->hadException())
            return (jsUndefined());
    }
    for (unsigned k = 0; k < additionalArgs; ++k) {
        thisObj->methodTable()->putByIndex(thisObj, exec, k + begin, exec->argument(k + 2), true);
        if (exec->hadException())
            return (jsUndefined());
    }

    putProperty(exec, thisObj, exec->propertyNames().length, jsNumber(length - deleteCount + additionalArgs));
    return (result);
}

JSValue JSC_HOST_CALL arrayProtoFuncUnShift(ExecState* exec)
{
    // 15.4.4.13
    // IFC4BC
    JSObject* thisObj = exec->hostThisValue().toObject(exec);
    if (!JSLabel(JSLabel::pcGlobalLabel).NSU(thisObj->getObjectLabel()))
    {
        // printf("IFC check in array-UnShift failed\n");
        JSLabel::ABORT_FLAG = true;
        // return jsUndefined();
    }
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (jsUndefined());

    unsigned nrArgs = exec->argumentCount();
    if (nrArgs) {
        unshift(exec, thisObj, 0, 0, nrArgs, length);
        if (exec->hadException())
            return (jsUndefined());
    }
    for (unsigned k = 0; k < nrArgs; ++k) {
        thisObj->methodTable()->putByIndex(thisObj, exec, k, exec->argument(k), true);
        if (exec->hadException())
            return (jsUndefined());
    }
    JSValue result = jsNumber(length + nrArgs);
    putProperty(exec, thisObj, exec->propertyNames().length, result);
    return (result);
}

JSValue JSC_HOST_CALL arrayProtoFuncFilter(ExecState* exec)
{
    JSObject* thisObj = exec->hostThisValue().toObject(exec);
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (jsUndefined());

    JSValue function = exec->argument(0);
    CallData callData;
    CallType callType = getCallData(function, callData);
    if (callType == CallTypeNone)
        return throwVMTypeError(exec);

    JSValue applyThis = exec->argument(1);
    JSArray* resultArray = constructEmptyArray(exec);

    unsigned filterIndex = 0;
    unsigned k = 0;
    if (callType == CallTypeJS && isJSArray(thisObj)) {
        JSFunction* f = jsCast<JSFunction*>(function);
        JSArray* array = asArray(thisObj);
        CachedCall cachedCall(exec, f, 3);
        for (; k < length && !exec->hadException(); ++k) {
            if (!array->canGetIndex(k))
                break;
            JSValue v = array->getIndex(k);
            cachedCall.setThis(applyThis);
            cachedCall.setArgument(0, v);
            cachedCall.setArgument(1, jsNumber(k));
            cachedCall.setArgument(2, thisObj);
            
            JSValue result = cachedCall.call();
            if (result.toBoolean())
                resultArray->putDirectIndex(exec, filterIndex++, v);
        }
        if (k == length)
            return (resultArray);
    }
    for (; k < length && !exec->hadException(); ++k) {
        PropertySlot slot(thisObj);
        if (!thisObj->getPropertySlot(exec, k, slot))
            continue;
        JSValue v = slot.getValue(exec, k);

        if (exec->hadException())
            return (jsUndefined());

        MarkedArgumentBuffer eachArguments;
        eachArguments.append(v);
        eachArguments.append(jsNumber(k));
        eachArguments.append(thisObj);

        JSValue result = call(exec, function, callType, callData, applyThis, eachArguments);
        if (result.toBoolean())
            resultArray->putDirectIndex(exec, filterIndex++, v);
    }
    return (resultArray);
}

JSValue JSC_HOST_CALL arrayProtoFuncMap(ExecState* exec)
{
    JSObject* thisObj = exec->hostThisValue().toObject(exec);
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (jsUndefined());

    JSValue function = exec->argument(0);
    CallData callData;
    CallType callType = getCallData(function, callData);
    if (callType == CallTypeNone)
        return throwVMTypeError(exec);

    JSValue applyThis = exec->argument(1);

    JSArray* resultArray = constructEmptyArray(exec, length);
    unsigned k = 0;
    if (callType == CallTypeJS && isJSArray(thisObj)) {
        JSFunction* f = jsCast<JSFunction*>(function);
        JSArray* array = asArray(thisObj);
        CachedCall cachedCall(exec, f, 3);
        for (; k < length && !exec->hadException(); ++k) {
            if (UNLIKELY(!array->canGetIndex(k)))
                break;

            cachedCall.setThis(applyThis);
            cachedCall.setArgument(0, array->getIndex(k));
            cachedCall.setArgument(1, jsNumber(k));
            cachedCall.setArgument(2, thisObj);

            resultArray->putDirectIndex(exec, k, cachedCall.call());
        }
    }
    for (; k < length && !exec->hadException(); ++k) {
        PropertySlot slot(thisObj);
        if (!thisObj->getPropertySlot(exec, k, slot))
            continue;
        JSValue v = slot.getValue(exec, k);

        if (exec->hadException())
            return (jsUndefined());

        MarkedArgumentBuffer eachArguments;
        eachArguments.append(v);
        eachArguments.append(jsNumber(k));
        eachArguments.append(thisObj);

        if (exec->hadException())
            return (jsUndefined());

        JSValue result = call(exec, function, callType, callData, applyThis, eachArguments);
        resultArray->putDirectIndex(exec, k, result);
    }

    return (resultArray);
}

// Documentation for these three is available at:
// http://developer-test.mozilla.org/en/docs/Core_JavaScript_1.5_Reference:Objects:Array:every
// http://developer-test.mozilla.org/en/docs/Core_JavaScript_1.5_Reference:Objects:Array:forEach
// http://developer-test.mozilla.org/en/docs/Core_JavaScript_1.5_Reference:Objects:Array:some

JSValue JSC_HOST_CALL arrayProtoFuncEvery(ExecState* exec)
{
    JSObject* thisObj = exec->hostThisValue().toObject(exec);
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (jsUndefined());

    JSValue function = exec->argument(0);
    CallData callData;
    CallType callType = getCallData(function, callData);
    if (callType == CallTypeNone)
        return throwVMTypeError(exec);

    JSValue applyThis = exec->argument(1);

    JSValue result = jsBoolean(true);

    unsigned k = 0;
    if (callType == CallTypeJS && isJSArray(thisObj)) {
        JSFunction* f = jsCast<JSFunction*>(function);
        JSArray* array = asArray(thisObj);
        CachedCall cachedCall(exec, f, 3);
        for (; k < length && !exec->hadException(); ++k) {
            if (UNLIKELY(!array->canGetIndex(k)))
                break;
            
            cachedCall.setThis(applyThis);
            cachedCall.setArgument(0, array->getIndex(k));
            cachedCall.setArgument(1, jsNumber(k));
            cachedCall.setArgument(2, thisObj);
            JSValue result = cachedCall.call();
            if (!result.toBoolean())
                return (jsBoolean(false));
        }
    }
    for (; k < length && !exec->hadException(); ++k) {
        PropertySlot slot(thisObj);
        if (!thisObj->getPropertySlot(exec, k, slot))
            continue;

        MarkedArgumentBuffer eachArguments;
        eachArguments.append(slot.getValue(exec, k));
        eachArguments.append(jsNumber(k));
        eachArguments.append(thisObj);

        if (exec->hadException())
            return (jsUndefined());

        bool predicateResult = call(exec, function, callType, callData, applyThis, eachArguments).toBoolean();
        if (!predicateResult) {
            result = jsBoolean(false);
            break;
        }
    }

    return (result);
}

JSValue JSC_HOST_CALL arrayProtoFuncForEach(ExecState* exec)
{
    JSObject* thisObj = exec->hostThisValue().toObject(exec);
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (jsUndefined());

    JSValue function = exec->argument(0);
    CallData callData;
    CallType callType = getCallData(function, callData);
    if (callType == CallTypeNone)
        return throwVMTypeError(exec);

    JSValue applyThis = exec->argument(1);

    unsigned k = 0;
    if (callType == CallTypeJS && isJSArray(thisObj)) {
        JSFunction* f = jsCast<JSFunction*>(function);
        JSArray* array = asArray(thisObj);
        CachedCall cachedCall(exec, f, 3);
        for (; k < length && !exec->hadException(); ++k) {
            if (UNLIKELY(!array->canGetIndex(k)))
                break;

            cachedCall.setThis(applyThis);
            cachedCall.setArgument(0, array->getIndex(k));
            cachedCall.setArgument(1, jsNumber(k));
            cachedCall.setArgument(2, thisObj);

            cachedCall.call();
        }
    }
    for (; k < length && !exec->hadException(); ++k) {
        PropertySlot slot(thisObj);
        if (!thisObj->getPropertySlot(exec, k, slot))
            continue;

        MarkedArgumentBuffer eachArguments;
        eachArguments.append(slot.getValue(exec, k));
        eachArguments.append(jsNumber(k));
        eachArguments.append(thisObj);

        if (exec->hadException())
            return (jsUndefined());

        call(exec, function, callType, callData, applyThis, eachArguments);
    }
    return (jsUndefined());
}

JSValue JSC_HOST_CALL arrayProtoFuncSome(ExecState* exec)
{
    JSObject* thisObj = exec->hostThisValue().toObject(exec);
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (jsUndefined());

    JSValue function = exec->argument(0);
    CallData callData;
    CallType callType = getCallData(function, callData);
    if (callType == CallTypeNone)
        return throwVMTypeError(exec);

    JSValue applyThis = exec->argument(1);

    JSValue result = jsBoolean(false);

    unsigned k = 0;
    if (callType == CallTypeJS && isJSArray(thisObj)) {
        JSFunction* f = jsCast<JSFunction*>(function);
        JSArray* array = asArray(thisObj);
        CachedCall cachedCall(exec, f, 3);
        for (; k < length && !exec->hadException(); ++k) {
            if (UNLIKELY(!array->canGetIndex(k)))
                break;
            
            cachedCall.setThis(applyThis);
            cachedCall.setArgument(0, array->getIndex(k));
            cachedCall.setArgument(1, jsNumber(k));
            cachedCall.setArgument(2, thisObj);
            JSValue result = cachedCall.call();
            if (result.toBoolean())
                return (jsBoolean(true));
        }
    }
    for (; k < length && !exec->hadException(); ++k) {
        PropertySlot slot(thisObj);
        if (!thisObj->getPropertySlot(exec, k, slot))
            continue;

        MarkedArgumentBuffer eachArguments;
        eachArguments.append(slot.getValue(exec, k));
        eachArguments.append(jsNumber(k));
        eachArguments.append(thisObj);

        if (exec->hadException())
            return (jsUndefined());

        bool predicateResult = call(exec, function, callType, callData, applyThis, eachArguments).toBoolean();
        if (predicateResult) {
            result = jsBoolean(true);
            break;
        }
    }
    return (result);
}

JSValue JSC_HOST_CALL arrayProtoFuncReduce(ExecState* exec)
{
    JSObject* thisObj = exec->hostThisValue().toObject(exec);
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (jsUndefined());

    JSValue function = exec->argument(0);
    CallData callData;
    CallType callType = getCallData(function, callData);
    if (callType == CallTypeNone)
        return throwVMTypeError(exec);

    unsigned i = 0;
    JSValue rv;
    if (!length && exec->argumentCount() == 1)
        return throwVMTypeError(exec);

    JSArray* array = 0;
    if (isJSArray(thisObj))
        array = asArray(thisObj);

    if (exec->argumentCount() >= 2)
        rv = exec->argument(1);
    else if (array && array->canGetIndex(0)){
        rv = array->getIndex(0);
        i = 1;
    } else {
        for (i = 0; i < length; i++) {
            rv = getProperty(exec, thisObj, i);
            if (exec->hadException())
                return (jsUndefined());
            if (rv)
                break;
        }
        if (!rv)
            return throwVMTypeError(exec);
        i++;
    }

    if (callType == CallTypeJS && array) {
        CachedCall cachedCall(exec, jsCast<JSFunction*>(function), 4);
        for (; i < length && !exec->hadException(); ++i) {
            cachedCall.setThis(jsUndefined());
            cachedCall.setArgument(0, rv);
            JSValue v;
            if (LIKELY(array->canGetIndex(i)))
                v = array->getIndex(i);
            else
                break; // length has been made unsafe while we enumerate fallback to slow path
            cachedCall.setArgument(1, v);
            cachedCall.setArgument(2, jsNumber(i));
            cachedCall.setArgument(3, array);
            rv = cachedCall.call();
        }
        if (i == length) // only return if we reached the end of the array
            return (rv);
    }

    for (; i < length && !exec->hadException(); ++i) {
        JSValue prop = getProperty(exec, thisObj, i);
        if (exec->hadException())
            return (jsUndefined());
        if (!prop)
            continue;
        
        MarkedArgumentBuffer eachArguments;
        eachArguments.append(rv);
        eachArguments.append(prop);
        eachArguments.append(jsNumber(i));
        eachArguments.append(thisObj);
        
        rv = call(exec, function, callType, callData, jsUndefined(), eachArguments);
    }
    return (rv);
}

JSValue JSC_HOST_CALL arrayProtoFuncReduceRight(ExecState* exec)
{
    JSObject* thisObj = exec->hostThisValue().toObject(exec);
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (jsUndefined());

    JSValue function = exec->argument(0);
    CallData callData;
    CallType callType = getCallData(function, callData);
    if (callType == CallTypeNone)
        return throwVMTypeError(exec);
    
    unsigned i = 0;
    JSValue rv;
    if (!length && exec->argumentCount() == 1)
        return throwVMTypeError(exec);

    JSArray* array = 0;
    if (isJSArray(thisObj))
        array = asArray(thisObj);
    
    if (exec->argumentCount() >= 2)
        rv = exec->argument(1);
    else if (array && array->canGetIndex(length - 1)){
        rv = array->getIndex(length - 1);
        i = 1;
    } else {
        for (i = 0; i < length; i++) {
            rv = getProperty(exec, thisObj, length - i - 1);
            if (exec->hadException())
                return (jsUndefined());
            if (rv)
                break;
        }
        if (!rv)
            return throwVMTypeError(exec);
        i++;
    }
    
    if (callType == CallTypeJS && array) {
        CachedCall cachedCall(exec, jsCast<JSFunction*>(function), 4);
        for (; i < length && !exec->hadException(); ++i) {
            unsigned idx = length - i - 1;
            cachedCall.setThis(jsUndefined());
            cachedCall.setArgument(0, rv);
            if (UNLIKELY(!array->canGetIndex(idx)))
                break; // length has been made unsafe while we enumerate fallback to slow path
            cachedCall.setArgument(1, array->getIndex(idx));
            cachedCall.setArgument(2, jsNumber(idx));
            cachedCall.setArgument(3, array);
            rv = cachedCall.call();
        }
        if (i == length) // only return if we reached the end of the array
            return (rv);
    }
    
    for (; i < length && !exec->hadException(); ++i) {
        unsigned idx = length - i - 1;
        JSValue prop = getProperty(exec, thisObj, idx);
        if (exec->hadException())
            return (jsUndefined());
        if (!prop)
            continue;
        
        MarkedArgumentBuffer eachArguments;
        eachArguments.append(rv);
        eachArguments.append(prop);
        eachArguments.append(jsNumber(idx));
        eachArguments.append(thisObj);
        
        rv = call(exec, function, callType, callData, jsUndefined(), eachArguments);
    }
    return (rv);        
}

JSValue JSC_HOST_CALL arrayProtoFuncIndexOf(ExecState* exec)
{
    // 15.4.4.14
    JSLabel eLabel;
    JSObject* thisObj = exec->hostThisValue().toObject(exec);
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    if (exec->hadException())
        return (jsUndefined());

    unsigned index = argumentClampedIndexFromStartOrEnd(exec, 1, length);
    JSValue searchElement = exec->argument(0);
    JSValue ret;
    for (; index < length; ++index) {
        JSValue e = getProperty(exec, thisObj, index);
        eLabel = eLabel.Join(e.getValueLabel());
        if (exec->hadException())
            return (jsUndefined());
        if (!e)
            continue;
        if (JSValue::strictEqual(exec, searchElement, e)) {
            ret = (jsNumber(index));
            ret.setValueLabel(searchElement.joinValueLabel(JSLabel::argLabel[0]).Join(eLabel));
            return ret;
        }
    }

    ret = (jsNumber(-1));
    ret.setValueLabel(searchElement.joinValueLabel(JSLabel::argLabel[0]).Join(eLabel));
    return ret;
}

JSValue JSC_HOST_CALL arrayProtoFuncLastIndexOf(ExecState* exec)
{
    // 15.4.4.15
    JSLabel eLabel;    
    JSObject* thisObj = exec->hostThisValue().toObject(exec);
    unsigned length = thisObj->get(exec, exec->propertyNames().length).toUInt32(exec);
    JSValue ret;
    if (!length) {
        ret = (jsNumber(-1));
        ret.setValueLabel(JSLabel(JSLabel::argLabel[0]).Join(JSLabel(JSLabel::argLabel[1]).Join(JSLabel::argLabel[2])));
        return ret;
    }

    unsigned index = length - 1;
    if (exec->argumentCount() >= 2) {
        JSValue fromValue = exec->argument(1);
        double fromDouble = fromValue.toInteger(exec);
        if (fromDouble < 0) {
            fromDouble += length;
            if (fromDouble < 0) {
                ret = (jsNumber(-1));
                ret.setValueLabel(JSLabel(JSLabel::argLabel[0]).Join(JSLabel(JSLabel::argLabel[1]).Join(JSLabel::argLabel[2])));
                return ret;
            }
        }
        if (fromDouble < length)
            index = static_cast<unsigned>(fromDouble);
    }

    JSValue searchElement = exec->argument(0);
    do {
        ASSERT(index < length);
        JSValue e = getProperty(exec, thisObj, index);
        eLabel = eLabel.Join(e.getValueLabel());
        if (exec->hadException())
            return (jsUndefined());
        if (!e)
            continue;
        if (JSValue::strictEqual(exec, searchElement, e)) {
            ret = (jsNumber(index));
            ret.setValueLabel(JSLabel(JSLabel::argLabel[0]).Join(JSLabel(JSLabel::argLabel[1]).Join(JSLabel::argLabel[2])).Join(eLabel));
            return ret;
        }
    } while (index--);

    ret = (jsNumber(-1));
    ret.setValueLabel(JSLabel(JSLabel::argLabel[0]).Join(JSLabel(JSLabel::argLabel[1]).Join(JSLabel::argLabel[2])).Join(eLabel));
    thisObj->setObjectLabel(thisObj->joinObjectLabel(ret.getValueLabel()));
    return ret;
}

} // namespace JSC
