/*
 *  Copyright (C) 1999-2000 Harri Porten (porten@kde.org)
 *  Copyright (C) 2008, 2011 Apple Inc. All rights reserved.
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
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 */

#include "config.h"
#include "ObjectPrototype.h"

#include "Error.h"
#include "JSFunction.h"
#include "JSString.h"
#include "JSStringBuilder.h"

#include "CodeBlock.h"

// #include "BitMap.h"

namespace JSC {

static JSValue JSC_HOST_CALL objectProtoFuncValueOf(ExecState*);
static JSValue JSC_HOST_CALL objectProtoFuncHasOwnProperty(ExecState*);
static JSValue JSC_HOST_CALL objectProtoFuncIsPrototypeOf(ExecState*);
static JSValue JSC_HOST_CALL objectProtoFuncDefineGetter(ExecState*);
static JSValue JSC_HOST_CALL objectProtoFuncDefineSetter(ExecState*);
static JSValue JSC_HOST_CALL objectProtoFuncLookupGetter(ExecState*);
static JSValue JSC_HOST_CALL objectProtoFuncLookupSetter(ExecState*);
static JSValue JSC_HOST_CALL objectProtoFuncPropertyIsEnumerable(ExecState*);
static JSValue JSC_HOST_CALL objectProtoFuncToLocaleString(ExecState*);
static JSValue JSC_HOST_CALL objectProtoFuncSetLabel(ExecState*);
static JSValue JSC_HOST_CALL objectProtoFuncUpgrade(ExecState*);
static JSValue JSC_HOST_CALL objectProtoFuncSetContext(ExecState*);
}

#include "ObjectPrototype.lut.h"

namespace JSC {

ASSERT_HAS_TRIVIAL_DESTRUCTOR(ObjectPrototype);

const ClassInfo ObjectPrototype::s_info = { "Object", &JSNonFinalObject::s_info, 0, ExecState::objectPrototypeTable, CREATE_METHOD_TABLE(ObjectPrototype) };

/* Source for ObjectPrototype.lut.h
@begin objectPrototypeTable
  toString              objectProtoFuncToString                 DontEnum|Function 0
  setLabel              objectProtoFuncSetLabel                 DontEnum|Function 1
  upgrade               objectProtoFuncUpgrade                  DontEnum|Function 0
  setContext            objectProtoFuncSetContext               DontEnum|Function 1
  toLocaleString        objectProtoFuncToLocaleString           DontEnum|Function 0
  valueOf               objectProtoFuncValueOf                  DontEnum|Function 0
  hasOwnProperty        objectProtoFuncHasOwnProperty           DontEnum|Function 1
  propertyIsEnumerable  objectProtoFuncPropertyIsEnumerable     DontEnum|Function 1
  isPrototypeOf         objectProtoFuncIsPrototypeOf            DontEnum|Function 1
  __defineGetter__      objectProtoFuncDefineGetter             DontEnum|Function 2
  __defineSetter__      objectProtoFuncDefineSetter             DontEnum|Function 2
  __lookupGetter__      objectProtoFuncLookupGetter             DontEnum|Function 1
  __lookupSetter__      objectProtoFuncLookupSetter             DontEnum|Function 1
@end
*/

ASSERT_CLASS_FITS_IN_CELL(ObjectPrototype);

ObjectPrototype::ObjectPrototype(ExecState* exec, Structure* stucture)
    : JSNonFinalObject(exec->globalData(), stucture)
    , m_hasNoPropertiesWithUInt32Names(true)
{
}

void ObjectPrototype::finishCreation(JSGlobalData& globalData, JSGlobalObject*)
{
    Base::finishCreation(globalData);
    ASSERT(inherits(&s_info));
}

void ObjectPrototype::put(JSCell* cell, ExecState* exec, PropertyName propertyName, JSValue value, PutPropertySlot& slot)
{
    ObjectPrototype* thisObject = jsCast<ObjectPrototype*>(cell);
    Base::put(cell, exec, propertyName, value, slot);

    if (thisObject->m_hasNoPropertiesWithUInt32Names && propertyName.asIndex() != PropertyName::NotAnIndex)
        thisObject->m_hasNoPropertiesWithUInt32Names = false;
}

bool ObjectPrototype::defineOwnProperty(JSObject* object, ExecState* exec, PropertyName propertyName, PropertyDescriptor& descriptor, bool shouldThrow)
{
    ObjectPrototype* thisObject = jsCast<ObjectPrototype*>(object);
    bool result = Base::defineOwnProperty(object, exec, propertyName, descriptor, shouldThrow);

    if (thisObject->m_hasNoPropertiesWithUInt32Names && propertyName.asIndex() != PropertyName::NotAnIndex)
        thisObject->m_hasNoPropertiesWithUInt32Names = false;

    return result;
}

bool ObjectPrototype::getOwnPropertySlotByIndex(JSCell* cell, ExecState* exec, unsigned propertyName, PropertySlot& slot)
{
    ObjectPrototype* thisObject = jsCast<ObjectPrototype*>(cell);
    if (thisObject->m_hasNoPropertiesWithUInt32Names)
        return false;
    return Base::getOwnPropertySlotByIndex(thisObject, exec, propertyName, slot);
}

bool ObjectPrototype::getOwnPropertySlot(JSCell* cell, ExecState* exec, PropertyName propertyName, PropertySlot &slot)
{
    return getStaticFunctionSlot<JSNonFinalObject>(exec, ExecState::objectPrototypeTable(exec), jsCast<ObjectPrototype*>(cell), propertyName, slot);
}

bool ObjectPrototype::getOwnPropertyDescriptor(JSObject* object, ExecState* exec, PropertyName propertyName, PropertyDescriptor& descriptor)
{
    return getStaticFunctionDescriptor<JSNonFinalObject>(exec, ExecState::objectPrototypeTable(exec), jsCast<ObjectPrototype*>(object), propertyName, descriptor);
}

// ------------------------------ Functions --------------------------------

JSValue JSC_HOST_CALL objectProtoFuncValueOf(ExecState* exec)
{
    JSValue thisValue = exec->hostThisValue();
    return (thisValue.toObject(exec));
}

JSValue JSC_HOST_CALL objectProtoFuncHasOwnProperty(ExecState* exec)
{
    JSValue thisValue = exec->hostThisValue();
    return (jsBoolean(thisValue.toObject(exec)->hasOwnProperty(exec, Identifier(exec, exec->argument(0).toString(exec)->value(exec)))));
}

JSValue JSC_HOST_CALL objectProtoFuncIsPrototypeOf(ExecState* exec)
{
    JSValue thisValue = exec->hostThisValue();
    JSObject* thisObj = thisValue.toObject(exec);

    if (!exec->argument(0).isObject())
        return (jsBoolean(false));

    JSValue v = asObject(exec->argument(0))->prototype();

    while (true) {
        if (!v.isObject())
            return (jsBoolean(false));
        if (v == thisObj)
            return (jsBoolean(true));
        v = asObject(v)->prototype();
    }
}

JSValue JSC_HOST_CALL objectProtoFuncDefineGetter(ExecState* exec)
{
    JSObject* thisObject = exec->hostThisValue().toObject(exec);
    if (exec->hadException())
        return (jsUndefined());

    JSValue get = exec->argument(1);
    CallData callData;
    if (getCallData(get, callData) == CallTypeNone)
        return throwVMError(exec, createSyntaxError(exec, "invalid getter usage"));

    PropertyDescriptor descriptor;
    descriptor.setGetter(get);
    descriptor.setEnumerable(true);
    descriptor.setConfigurable(true);
    thisObject->methodTable()->defineOwnProperty(thisObject, exec, Identifier(exec, exec->argument(0).toString(exec)->value(exec)), descriptor, false);

    return (jsUndefined());
}

JSValue JSC_HOST_CALL objectProtoFuncDefineSetter(ExecState* exec)
{
    JSObject* thisObject = exec->hostThisValue().toObject(exec);
    if (exec->hadException())
        return (jsUndefined());

    JSValue set = exec->argument(1);
    CallData callData;
    if (getCallData(set, callData) == CallTypeNone)
        return throwVMError(exec, createSyntaxError(exec, "invalid setter usage"));

    PropertyDescriptor descriptor;
    descriptor.setSetter(set);
    descriptor.setEnumerable(true);
    descriptor.setConfigurable(true);
    thisObject->methodTable()->defineOwnProperty(thisObject, exec, Identifier(exec, exec->argument(0).toString(exec)->value(exec)), descriptor, false);

    return (jsUndefined());
}

JSValue JSC_HOST_CALL objectProtoFuncLookupGetter(ExecState* exec)
{
    JSObject* thisObject = exec->hostThisValue().toObject(exec);
    if (exec->hadException())
        return (jsUndefined());

    PropertyDescriptor descriptor;
    if (thisObject->getPropertyDescriptor(exec, Identifier(exec, exec->argument(0).toString(exec)->value(exec)), descriptor)
        && descriptor.getterPresent())
        return (descriptor.getter());

    return (jsUndefined());
}

JSValue JSC_HOST_CALL objectProtoFuncLookupSetter(ExecState* exec)
{
    JSObject* thisObject = exec->hostThisValue().toObject(exec);
    if (exec->hadException())
        return (jsUndefined());

    PropertyDescriptor descriptor;
    if (thisObject->getPropertyDescriptor(exec, Identifier(exec, exec->argument(0).toString(exec)->value(exec)), descriptor)
        && descriptor.setterPresent())
        return (descriptor.setter());

    return (jsUndefined());
}

JSValue JSC_HOST_CALL objectProtoFuncPropertyIsEnumerable(ExecState* exec)
{
    JSValue thisValue = exec->hostThisValue();
    return (jsBoolean(thisValue.toObject(exec)->propertyIsEnumerable(exec, Identifier(exec, exec->argument(0).toString(exec)->value(exec)))));
}

// 15.2.4.3 Object.prototype.toLocaleString()
JSValue JSC_HOST_CALL objectProtoFuncToLocaleString(ExecState* exec)
{
    // 1. Let O be the result of calling ToObject passing the this value as the argument.
    JSObject* object = exec->hostThisValue().toObject(exec);
    if (exec->hadException())
        return (jsUndefined());

    // 2. Let toString be the result of calling the [[Get]] internal method of O passing "toString" as the argument.
    JSValue toString = object->get(exec, exec->propertyNames().toString);

    // 3. If IsCallable(toString) is false, throw a TypeError exception.
    CallData callData;
    CallType callType = getCallData(toString, callData);
    if (callType == CallTypeNone)
        return (jsUndefined());

    // 4. Return the result of calling the [[Call]] internal method of toString passing O as the this value and no arguments.
    return (call(exec, toString, callType, callData, object, exec->emptyList()));
}

JSValue JSC_HOST_CALL objectProtoFuncToString(ExecState* exec)
{
    JSValue thisValue = exec->hostThisValue();
    if (thisValue.isUndefinedOrNull())
        return (jsNontrivialString(exec, thisValue.isUndefined() ? "[object Undefined]" : "[object Null]"));
    JSObject* thisObject = thisValue.toObject(exec);

    JSString* result = thisObject->structure()->objectToStringValue();
    if (!result) {
        RefPtr<StringImpl> newString = WTF::tryMakeString("[object ", thisObject->methodTable()->className(thisObject), "]");
        if (!newString)
            return (throwOutOfMemoryError(exec));

        result = jsNontrivialString(exec, newString.release());
        thisObject->structure()->setObjectToStringValue(exec->globalData(), thisObject, result);
    }
    return (result);
}

// IFC4BC - Sets the label of the global value as defined by the policy
JSValue JSC_HOST_CALL objectProtoFuncSetLabel(ExecState* exec)
{
    JSValue thisValue = exec->hostThisValue();
    // Setting label of only the first argument.
    // Cannot handle multiple arguments/labels for now
    size_t argCount = exec->argumentCount();
    if (argCount == 0) {
        return thisValue;
    }
        
    JSValue temp = exec->argument(0);
    JSLabel setLabel;
    // JSLabel funcLabel = asObject(thisValue)->getObjectLabel();
    if (JSLabel::pcGlobalLabel.clabel==1)
    {
        if (strcmp(temp.toUString(exec).utf8().data(), "HOST") == 0)
            setLabel = JSLabel(URLMap::urlmap().getLabel(exec->codeBlock()->source()->url().utf8().data()));
        else
            setLabel = JSLabel(URLMap::urlmap().getLabel(temp.toUString(exec).utf8().data()));
        // printf("This is policy. Setting label\n");
        // URLMap::urlmap().put(temp.toUString(exec).utf8().data(), false);
        // JSLabel set = JSLabel(URLMap::urlmap().getLabel(temp.toUString(exec).utf8().data()));
        /*
        if (argCount >= 2 && exec->argument(1).isInt32()) {
            // Set the number of bits allowed
            char* address = new char[20]; // assume the maximum length of address to be 20. Bad hack!!!!
            sprintf(address, "%p", thisValue.asCell());
            int noBits = 0;
            if (exec->argument(1).isInt32())
                noBits = exec->argument(1).asInt32();
            JSLabel decLabel;
            if (argCount == 3) {
                JSValue tempURL = exec->argument(2);
                decLabel = JSLabel(URLMap::urlmap().getLabel(tempURL.toUString(exec).utf8().data()));
            }
            // set.pLabel = BitMap::Bitmap().put(address, noBits, set.Val(), decLabel.Val());
            // JSLabelMap::labelMap().append(set.pLabel, set.Val());
            set.setVal(0);
            delete(address);
        }*/
        thisValue.setValueLabel(setLabel);
        if (thisValue.isObject()) {
            asObject(thisValue)->setObjectLabel(setLabel);
        }
    }
    else
    { 
        printf("SetLabel: This is not a policy\n");
    }

    return thisValue;
}

// IFC4BC - Set the object as a private variable for the script
JSValue JSC_HOST_CALL objectProtoFuncUpgrade(ExecState* exec)
{
    JSValue thisValue = exec->hostThisValue();
    if (!JSLabel(JSLabel::pcGlobalLabel).NSU(thisValue.getValueLabel())) {
        printf("IFC: Value upgrade in high context\n");
        JSLabel::ABORT_FLAG = true;
        return jsUndefined();
    }
    
    // Use the source from the codeblock to get the label
    JSLabel funcLabel = JSLabel(URLMap::urlmap().getLabel(exec->codeBlock()->source()->url().utf8().data())) ;
    // funcLabel.pLabel = thisValue.getValueLabel().pLabel;
    // funcLabel.setiVal(thisValue.getValueLabel().iVal());
    thisValue.setValueLabel(funcLabel);
    if (thisValue.isObject()) {
        asObject(thisValue)->setObjectLabel(funcLabel);
    }
    return thisValue;
}

// IFC4BC - Set the context for the event handlers to run
// TODO - Add the functionality
JSValue JSC_HOST_CALL objectProtoFuncSetContext(ExecState* exec)
{
    if (JSLabel::pcGlobalLabel.clabel == 1)
    {
        JSLabel labelVal;
        size_t argCount = exec->argumentCount();
        size_t i = 0;
        while (1 && argCount) {
            JSValue curArg = (exec->argument(i));
            labelVal = JSLabel(URLMap::urlmap().getLabel(curArg.toUString(exec).utf8().data()));
            // If null is set then ignore other contexts.
            if (labelVal.Val() == 0) {
                JSLabel::eventContextLabel.clabel = 0;
                break;
            }
            if (JSLabel::eventContextLabel.clabel == 1)
                JSLabel::eventContextLabel.clabel = labelVal.Val();
            else
                JSLabel::eventContextLabel.clabel |= labelVal.Val();
            if (++i == argCount) {
                break;
            }
        }
    }
    return JSValue(true);
}
    

} // namespace JSC
