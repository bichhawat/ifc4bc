/*
 * Copyright (C) 2008, 2009, 2010, 2012 Apple Inc. All rights reserved.
 * Copyright (C) 2008 Cameron Zwarich <cwzwarich@uwaterloo.ca>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1.  Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 * 2.  Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in the
 *     documentation and/or other materials provided with the distribution.
 * 3.  Neither the name of Apple Computer, Inc. ("Apple") nor the names of
 *     its contributors may be used to endorse or promote products derived
 *     from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY APPLE AND ITS CONTRIBUTORS "AS IS" AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL APPLE OR ITS CONTRIBUTORS BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "config.h"
#include "Interpreter.h"

#include "Arguments.h"
#include "BatchedTransitionOptimizer.h"
#include "CallFrame.h"
#include "CallFrameClosure.h"
#include "CodeBlock.h"
#include "Heap.h"
#include "Debugger.h"
#include "DebuggerCallFrame.h"
#include "ErrorInstance.h"
#include "EvalCodeCache.h"
#include "ExceptionHelpers.h"
#include "GetterSetter.h"
#include "JSActivation.h"
#include "JSArray.h"
#include "JSBoundFunction.h"
#include "JSNotAnObject.h"
#include "JSPropertyNameIterator.h"
#include "LiteralParser.h"
#include "JSStaticScopeObject.h"
#include "JSString.h"
#include "NameInstance.h"
#include "ObjectPrototype.h"
#include "Operations.h"
#include "Parser.h"
#include "Profiler.h"
#include "RegExpObject.h"
#include "RegExpPrototype.h"
#include "Register.h"
#include "SamplingTool.h"
#include "StrictEvalActivation.h"
#include "StrongInlines.h"
#include "UStringConcatenate.h"
#include <limits.h>
#include <stdio.h>
#include <wtf/Threading.h>
#include <wtf/text/StringBuilder.h>

// #include "BitMap.h"

#if ENABLE(JIT)
#include "JIT.h"
#endif

#define WTF_USE_GCC_COMPUTED_GOTO_WORKAROUND ((ENABLE(COMPUTED_GOTO_CLASSIC_INTERPRETER) || ENABLE(LLINT)) && !defined(__llvm__))


// IFC4BC - Print stack messages
#define LDEBUG 0

using namespace std;

namespace JSC {

// Returns the depth of the scope chain within a given call frame.
static int depth(CodeBlock* codeBlock, ScopeChainNode* sc)
{
    if (!codeBlock->needsFullScopeChain())
        return 0;
    return sc->localDepth();
}

#if ENABLE(CLASSIC_INTERPRETER) 
static NEVER_INLINE JSValue concatenateStrings(ExecState* exec, Register* strings, unsigned count)
{
    return jsString(exec, strings, count);
}

NEVER_INLINE bool Interpreter::resolve(CallFrame* callFrame, Instruction* vPC, JSValue& exceptionValue, bool* labelReq)
{
    int dst = vPC[1].u.operand;
    int property = vPC[2].u.operand;
    
    //IFC4BC
    JSLabel increasingContextLabel = pcstack.Head();
    //--------
    
    ScopeChainNode* scopeChain = callFrame->scopeChain();
    ScopeChainIterator iter = scopeChain->begin();
    ScopeChainIterator end = scopeChain->end();
    ASSERT(iter != end);
    
    CodeBlock* codeBlock = callFrame->codeBlock();
    Identifier& ident = codeBlock->identifier(property);
    do {
        JSObject* o = iter->get();
        PropertySlot slot(o);
        increasingContextLabel = increasingContextLabel.Join(o->getObjectLabel());
        //------
        //PropertySlot slot(o);
        // Traverse the prototype chain to check if it has the property.
        if (o->getPropertySlotIFC(callFrame, ident, slot, &increasingContextLabel)) {
            JSValue result = slot.getValue(callFrame, ident);
            // if (result.getValueLabel().Star()) {
                // Add the context value to the result label
                increasingContextLabel = increasingContextLabel.Join(result.getValueLabel());
                // increasingContextLabel.setStar(false);
                result.setValueLabel(increasingContextLabel);
            // }
            // else // Pre-defined property, so making label 0 with context.
            //     result.setValueLabel(increasingContextLabel);
            exceptionValue = callFrame->globalData().exception;
            // IFC4BC - Set the exception value
            if (increasingContextLabel != pcstack.Head() && labelReq && (*labelReq == false))
            {
                *labelReq = true;
                callFrame->uncheckedR(dst).setRegLabel(pcstack.Head());
            }
            exceptionValue.setValueLabel(increasingContextLabel);
            if (exceptionValue)
                return false;
            if (JSLabel::ABORT_FLAG) {
                JSLabel::ABORT_FLAG = false;
                printf("Aborting in resolve %d in %p!\n", (int) (vPC - codeBlock->instructions().begin()), codeBlock);
                // return jsUndefined();
            }
            if (*labelReq) {
                JSLabel dstLabel = JSLabel();
                if(!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
                {
                    // printf("Sensitive Upgrade at %ld in %p\n", vPC - codeBlock->instructions().begin(), codeBlock);
                    dstLabel.setStar(true);
                }
                callFrame->uncheckedR(dst) = JSValue(result);
                callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(result.getValueLabel()));
            }
            else {
                callFrame->uncheckedR(dst) = JSValue(result);
            }
            
            return true;
        }
        //IFC4BC - Traverse the scope chain for getting the value
        increasingContextLabel = increasingContextLabel.Join(iter.getCurrentNode()->scopeNextLabel);
        //------
    } while (++iter != end);
    if (increasingContextLabel != pcstack.Head() && labelReq && (*labelReq == false))
    {
        *labelReq = true;
        callFrame->uncheckedR(dst).setRegLabel(pcstack.Head());
    }
    exceptionValue = createUndefinedVariableError(callFrame, ident);
    // IFC4BC - Set the exception value label
    if (increasingContextLabel != pcstack.Head() && labelReq)
        *labelReq = true;
    exceptionValue.setValueLabel(increasingContextLabel);
    return false;
}

NEVER_INLINE bool Interpreter::resolveSkip(CallFrame* callFrame, Instruction* vPC, JSValue& exceptionValue, bool* labelReq)
{
    CodeBlock* codeBlock = callFrame->codeBlock();
    
    int dst = vPC[1].u.operand;
    int property = vPC[2].u.operand;
    int skip = vPC[3].u.operand;
    
    //IFC4BC
    JSLabel increasingContextLabel = pcstack.Head();
    //--------
    
    ScopeChainNode* scopeChain = callFrame->scopeChain();
    ScopeChainIterator iter = scopeChain->begin();
    ScopeChainIterator end = scopeChain->end();
    ASSERT(iter != end);
    bool checkTopLevel = codeBlock->codeType() == FunctionCode && codeBlock->needsFullScopeChain();
    ASSERT(skip || !checkTopLevel);
    if (checkTopLevel && skip--) {
        if (callFrame->uncheckedR(codeBlock->activationRegister()).jsValue()){
            //IFC4BC - for objects being skipped
            JSObject* o = iter->get();
            increasingContextLabel = increasingContextLabel.Join(o->getObjectLabel());
            increasingContextLabel = increasingContextLabel.Join(iter.getCurrentNode()->scopeNextLabel);
            //------
            ++iter;
        }
    }
    while (skip--) {
        // IFC4BC - for objects being skipped
        JSObject* o = iter->get();
        increasingContextLabel = increasingContextLabel.Join(o->getObjectLabel());
        increasingContextLabel = increasingContextLabel.Join(iter.getCurrentNode()->scopeNextLabel);
        // -----
        ++iter;
        ASSERT(iter != end);
    }
    Identifier& ident = codeBlock->identifier(property);
    do {
        JSObject* o = iter->get();
        PropertySlot slot(o);
        // IFC4BC - for objects being skipped
        increasingContextLabel = increasingContextLabel.Join(o->getObjectLabel());
        // -----
        // IFC4BC - Traverse the prototype chain
        if (o->getPropertySlotIFC(callFrame, ident, slot, &increasingContextLabel)) {
            JSValue result = slot.getValue(callFrame, ident);
            // if (result.getValueLabel().Star()) {
                // Add the context value to the result label
                increasingContextLabel = increasingContextLabel.Join(result.getValueLabel());
                // increasingContextLabel.setStar(false);
                result.setValueLabel(increasingContextLabel);
            // }
            // else // Pre-defined property, so making label 0.
            //    result.setValueLabel(increasingContextLabel);
            exceptionValue = callFrame->globalData().exception;
            // IFC4BC - Set the exception value label
            if (increasingContextLabel != pcstack.Head() && labelReq && (*labelReq == false))
            {
                *labelReq = true;
                callFrame->uncheckedR(dst).setRegLabel(pcstack.Head());
            }
            exceptionValue.setValueLabel(increasingContextLabel);
            if (exceptionValue)
                return false;
            ASSERT(result);
            if (JSLabel::ABORT_FLAG) {
                JSLabel::ABORT_FLAG = false;
                printf("Aborting in resolve skip %d in %p!\n", (int) (vPC - codeBlock->instructions().begin()), codeBlock);
                // return jsUndefined();
            }
            if (*labelReq) {
                JSLabel dstLabel = JSLabel();
                if(!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
                {
                    // printf("Sensitive Upgrade at %ld in %p\n", vPC - codeBlock->instructions().begin(), codeBlock);
                    dstLabel.setStar(true);
                }
                callFrame->uncheckedR(dst) = JSValue(result);
                callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(result.getValueLabel()));
            }
            else {
                callFrame->uncheckedR(dst) = JSValue(result);
            }
            return true;
        }
        // IFC4BC - Scope chain pointer label joined with the context
        increasingContextLabel = increasingContextLabel.Join(iter.getCurrentNode()->scopeNextLabel);
        // ------
    } while (++iter != end);
    if (increasingContextLabel != pcstack.Head() && labelReq && (*labelReq == false))
    {
        *labelReq = true;
        callFrame->uncheckedR(dst).setRegLabel(pcstack.Head());
    }
    exceptionValue = createUndefinedVariableError(callFrame, ident);
    if (increasingContextLabel != pcstack.Head() && labelReq)
        *labelReq = true;
    // IFC4BC - Set the exception value label
    exceptionValue.setValueLabel(increasingContextLabel);
    return false;
}

NEVER_INLINE bool Interpreter::resolveGlobal(CallFrame* callFrame, Instruction* vPC, JSValue& exceptionValue, bool* labelReq)
{
    int dst = vPC[1].u.operand;
    CodeBlock* codeBlock = callFrame->codeBlock();
    JSGlobalObject* globalObject = codeBlock->globalObject();
    ASSERT(globalObject->isGlobalObject());
    int property = vPC[2].u.operand;
    Structure* structure = vPC[3].u.structure.get();
    int offset = vPC[4].u.operand;
    
    //IFC4BC
    JSLabel increasingContextLabel = pcstack.Head();
    //-------
    
    if (structure == globalObject->structure()) {
        //IFC4BC
        JSValue val = JSValue(globalObject->getDirectOffset(offset));
        // if (val.getValueLabel().Star()) {
            // Add the context value to the result label. Global object's label is zero.
            increasingContextLabel = increasingContextLabel.Join(val.getValueLabel());
            // increasingContextLabel.setStar(false);
            val.setValueLabel(increasingContextLabel);
        // }
        // else // Pre-defined property, so making label 0.
        //    val.setValueLabel(increasingContextLabel);
        
        if (JSLabel::ABORT_FLAG) {
            JSLabel::ABORT_FLAG = false;
            printf("Aborting in resolve global %d in %p!\n", (int) (vPC - codeBlock->instructions().begin()), codeBlock);
            // return jsUndefined();
        }
        
        if (*labelReq) {
            JSLabel dstLabel = JSLabel(); /* val.getValueLabel() */
            if(!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                // printf("Sensitive Upgrade at %ld in %p\n", vPC - codeBlock->instructions().begin(), codeBlock);
                dstLabel.setStar(true);
            }
            callFrame->uncheckedR(dst) = val;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(val.getValueLabel()));
        }
        else {
            callFrame->uncheckedR(dst) = val;
        }
        return true;
    }
    
    Identifier& ident = codeBlock->identifier(property);
    PropertySlot slot(globalObject);
    // IFC4BC - Traverse the prototype chain of the object
    if (globalObject->getPropertySlotIFC(callFrame, ident, slot, &increasingContextLabel)) {
        JSValue result = slot.getValue(callFrame, ident);
        // if (result.getValueLabel().Star()) {
            // Add the context value to the result label. Global object's label is zero.
            increasingContextLabel = increasingContextLabel.Join(result.getValueLabel());
            // increasingContextLabel.setStar(false);
            result.setValueLabel(increasingContextLabel);
        // }
        // else // Pre-defined property, so making label 0.
        //     result.setValueLabel(increasingContextLabel);
        if (increasingContextLabel != pcstack.Head() && labelReq)
            *labelReq = true;
        if (JSLabel::ABORT_FLAG) {
            JSLabel::ABORT_FLAG = false;
            printf("Aborting in resolve global %d in %p!\n", (int) (vPC - codeBlock->instructions().begin()), codeBlock);
            // return jsUndefined();
        }
        if (increasingContextLabel != pcstack.Head() && labelReq && (*labelReq == false))
        {
            *labelReq = true;
            callFrame->uncheckedR(dst).setRegLabel(pcstack.Head());
        }
        
        if (slot.isCacheableValue() && !globalObject->structure()->isUncacheableDictionary() && slot.slotBase() == globalObject) {
            vPC[3].u.structure.set(callFrame->globalData(), codeBlock->ownerExecutable(), globalObject->structure());
            vPC[4] = slot.cachedOffset();
            // IFC4BC - Assigning label for the dst reg
            if (*labelReq) {
                JSLabel dstLabel = JSLabel(); /* result.getValueLabel() */
                if(!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
                {
                    // printf("Sensitive Upgrade at %ld in %p\n", vPC - codeBlock->instructions().begin(), codeBlock);
                    dstLabel.setStar(true);
                }
                callFrame->uncheckedR(dst) = result;
                callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(result.getValueLabel()));
            }
            else {
                callFrame->uncheckedR(dst) = result;
            }
            return true;
        }
        exceptionValue = callFrame->globalData().exception;
        // IFC4BC - Set the exception value label
        exceptionValue.setValueLabel(increasingContextLabel);
        if (exceptionValue)
            return false;
        if (*labelReq) {
            JSLabel dstLabel = JSLabel(); /* result.getValueLabel() */
            if(!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                // printf("Sensitive Upgrade at %ld in %p\n", vPC - codeBlock->instructions().begin(), codeBlock);
                dstLabel.setStar(true);
            }
            callFrame->uncheckedR(dst) = JSValue(result);
            callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(result.getValueLabel()));
        }
        else {
            callFrame->uncheckedR(dst) = JSValue(result);
        }
        return true;
    }
    if (increasingContextLabel != pcstack.Head() && labelReq && (*labelReq == false))
    {
        *labelReq = true;
        callFrame->uncheckedR(dst).setRegLabel(pcstack.Head());
    }
    exceptionValue = createUndefinedVariableError(callFrame, ident);
    // IFC4BC - Set the exception value label
    if (increasingContextLabel != pcstack.Head() && labelReq)
        *labelReq = true;
    exceptionValue.setValueLabel(increasingContextLabel);
    return false;
}

NEVER_INLINE bool Interpreter::resolveGlobalDynamic(CallFrame* callFrame, Instruction* vPC, JSValue& exceptionValue, bool* labelReq)
{
    int dst = vPC[1].u.operand;
    CodeBlock* codeBlock = callFrame->codeBlock();
    JSGlobalObject* globalObject = codeBlock->globalObject();
    ASSERT(globalObject->isGlobalObject());
    int property = vPC[2].u.operand;
    Structure* structure = vPC[3].u.structure.get();
    int offset = vPC[4].u.operand;
    int skip = vPC[5].u.operand;
    
    //IFC4BC
    JSLabel increasingContextLabel = pcstack.Head();
    //-------
    
    ScopeChainNode* scopeChain = callFrame->scopeChain();
    ScopeChainIterator iter = scopeChain->begin();
    ScopeChainIterator end = scopeChain->end();
    ASSERT(iter != end);
    bool checkTopLevel = codeBlock->codeType() == FunctionCode && codeBlock->needsFullScopeChain();
    ASSERT(skip || !checkTopLevel);
    if (checkTopLevel && skip--) {
        if (callFrame->uncheckedR(codeBlock->activationRegister()).jsValue()){
            JSObject* o = iter->get();
            //IFC4BC - for objects being skipped
            increasingContextLabel = increasingContextLabel.Join(o->getObjectLabel());
            increasingContextLabel = increasingContextLabel.Join(iter.getCurrentNode()->scopeNextLabel);
            //------
            ++iter;
        }
    }
    while (skip--) {
        JSObject* o = iter->get();
        //IFC4BC - for objects being skipped
        increasingContextLabel = increasingContextLabel.Join(o->getObjectLabel());
        increasingContextLabel = increasingContextLabel.Join(iter.getCurrentNode()->scopeNextLabel);
        //------
        if (o->hasCustomProperties()) {
            Identifier& ident = codeBlock->identifier(property);
            do {
                PropertySlot slot(o);
                // IFC4BC - Traverse the prototype chain as well
                if (o->getPropertySlotIFC(callFrame, ident, slot, &increasingContextLabel)) {
                    JSValue result = slot.getValue(callFrame, ident);
                    // if (result.getValueLabel().Star()) {
                        // Add the context value to the result label
                        increasingContextLabel = increasingContextLabel.Join(result.getValueLabel());
                        // increasingContextLabel.setStar(false);
                        result.setValueLabel(increasingContextLabel);
                    // }
                    // else // Pre-defined property, so making label 0.
                    //     result.setValueLabel(increasingContextLabel);
                    if (increasingContextLabel != pcstack.Head() && labelReq && (*labelReq == false))
                    {
                        *labelReq = true;
                        callFrame->uncheckedR(dst).setRegLabel(pcstack.Head());
                    }
                    
                    if (JSLabel::ABORT_FLAG) {
                        JSLabel::ABORT_FLAG = false;
                        printf("Aborting in resolve global dynamic %d in %p!\n", (int) (vPC - codeBlock->instructions().begin()), codeBlock);
                        // return jsUndefined();
                    }
                    exceptionValue = callFrame->globalData().exception;
                    // IFC4BC - Set the exception value label
                    exceptionValue.setValueLabel(increasingContextLabel);
                    if (exceptionValue)
                        return false;
                    ASSERT(result);
                    // IFC4BC - Setting the label for result in case it comes in here.
                    if (*labelReq) {
                        JSLabel dstLabel = JSLabel(); /* result.getValueLabel() */
                        if(!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
                        {
                            // printf("Sensitive Upgrade at %ld in %p\n", vPC - codeBlock->instructions().begin(), codeBlock);
                            dstLabel.setStar(true);
                        }
                        callFrame->uncheckedR(dst) = JSValue(result);
                        callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(result.getValueLabel()));
                    }
                    else {
                        callFrame->uncheckedR(dst) = JSValue(result);
                    }
                    return true;
                }
                if (iter == end)
                    break;
                o = iter->get();
                ++iter;
            } while (true);
            if (increasingContextLabel != pcstack.Head() && labelReq && (*labelReq == false))
            {
                *labelReq = true;
                callFrame->uncheckedR(dst).setRegLabel(pcstack.Head());
            }
            exceptionValue = createUndefinedVariableError(callFrame, ident);
            // IFC4BC - Set the exception value label
            exceptionValue.setValueLabel(increasingContextLabel);
            return false;
        }
        ++iter;
    }
    
    if (structure == globalObject->structure()) {
        // IFC4BC
        JSValue vRet = JSValue(globalObject->getDirectOffset(offset));
        // if (vRet.getValueLabel().Star()) {
            // Add the context value to the result label
            increasingContextLabel = increasingContextLabel.Join(vRet.getValueLabel());
            // increasingContextLabel.setStar(false);
            vRet.setValueLabel(increasingContextLabel);
        // }
        // else // Pre-defined property, so making label 0.
        //    vRet.setValueLabel(increasingContextLabel);
        if (increasingContextLabel != pcstack.Head() && labelReq && (*labelReq == false))
        {
            *labelReq = true;
            callFrame->uncheckedR(dst).setRegLabel(pcstack.Head());
        }
        if (JSLabel::ABORT_FLAG) {
            JSLabel::ABORT_FLAG = false;
            printf("Aborting in resolve global dynamic %d in %p!\n", (int) (vPC - codeBlock->instructions().begin()), codeBlock);
            // return jsUndefined();
        }
        if (*labelReq) {
            JSLabel dstLabel = JSLabel() /*vRet.getValueLabel()*/;
            if(!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                // printf("Sensitive Upgrade at %ld in %p\n", vPC - codeBlock->instructions().begin(), codeBlock);
                dstLabel.setStar(true);
            }
            callFrame->uncheckedR(dst) = vRet;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(vRet.getValueLabel()));

        }
        else {
            callFrame->uncheckedR(dst) = vRet;
        }

        ASSERT(callFrame->uncheckedR(dst).jsValue());
        return true;
    }
    
    // IFC4BC - Adding labels and checking if the property is user defined.
    Identifier& ident = codeBlock->identifier(property);
    PropertySlot slot(globalObject);
    if (globalObject->getPropertySlotIFC(callFrame, ident, slot, &increasingContextLabel)) {
        JSValue result = slot.getValue(callFrame, ident);
        // if (result.getValueLabel().Star()) {
            // Add the context value to the result label
            increasingContextLabel = increasingContextLabel.Join(result.getValueLabel());
            // increasingContextLabel.setStar(false);
            result.setValueLabel(increasingContextLabel);
        // }
        // else // Pre-defined property, so making label 0.
        //     result.setValueLabel(increasingContextLabel);
        if (increasingContextLabel != pcstack.Head() && labelReq && (*labelReq == false))
        {
            *labelReq = true;
            callFrame->uncheckedR(dst).setRegLabel(pcstack.Head());
        }
        if (JSLabel::ABORT_FLAG) {
            JSLabel::ABORT_FLAG = false;
            printf("Aborting in resolve global dynamic %d in %p!\n", (int) (vPC - codeBlock->instructions().begin()), codeBlock);
            // return jsUndefined();
        }
        if (slot.isCacheableValue() && !globalObject->structure()->isUncacheableDictionary() && slot.slotBase() == globalObject) {
            vPC[3].u.structure.set(callFrame->globalData(), codeBlock->ownerExecutable(), globalObject->structure());
            vPC[4] = slot.cachedOffset();
            ASSERT(result);
            // IFC4BC - Assigning label for the dst reg
            if (*labelReq) {
                JSLabel dstLabel = JSLabel(); /* result.getValueLabel() */
                if(!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
                {
                    // printf("Sensitive Upgrade at %ld in %p\n", vPC - codeBlock->instructions().begin(), codeBlock);
                    dstLabel.setStar(true);
                }
                callFrame->uncheckedR(dst) = result;
                callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(result.getValueLabel()));
            }
            else {
                callFrame->uncheckedR(dst) = result;
            }
            return true;
        }
        exceptionValue = callFrame->globalData().exception;
        // IFC4BC - Set the exception value label
        exceptionValue.setValueLabel(increasingContextLabel);
        if (exceptionValue)
            return false;
        ASSERT(result);
        // IFC4BC - Assigning label for the dst reg
        if (*labelReq) {
            JSLabel dstLabel = JSLabel(); /* result.getValueLabel() */
            if(!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                // printf("Sensitive Upgrade at %ld in %p\n", vPC - codeBlock->instructions().begin(), codeBlock);
                dstLabel.setStar(true);
            }
            callFrame->uncheckedR(dst) = JSValue(result);
            callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(result.getValueLabel()));
        }
        else {
            callFrame->uncheckedR(dst) = JSValue(result);
        }
        return true;
    }
    
    if (increasingContextLabel != pcstack.Head() && labelReq && (*labelReq == false))
    {
        *labelReq = true;
        callFrame->uncheckedR(dst).setRegLabel(pcstack.Head());
    }
    exceptionValue = createUndefinedVariableError(callFrame, ident);
    // IFC4BC - Set the exception value label
    exceptionValue.setValueLabel(increasingContextLabel);
    return false;
}

NEVER_INLINE void Interpreter::resolveBase(CallFrame* callFrame, Instruction* vPC, bool* labelReq)
{
    int dst = vPC[1].u.operand;
    int property = vPC[2].u.operand;
    bool isStrictPut = vPC[3].u.operand;
    Identifier ident = callFrame->codeBlock()->identifier(property);
    //IFC4BC
    JSLabel contextLabel = pcstack.Head();
    JSValue result = JSC::resolveBase(callFrame, ident, callFrame->scopeChain(), isStrictPut, &contextLabel);
    // if (result.getValueLabel().Star()) {
        // Add the context value to the result label
        contextLabel = contextLabel.Join(result.getValueLabel());
        // contextLabel.setStar(false);
        result.setValueLabel(contextLabel);
    // }
    // else // Pre-defined property, so making label 0.
    //    result.setValueLabel(contextLabel);
    if (contextLabel != pcstack.Head() && labelReq && (*labelReq == false))
    {
        *labelReq = true;
        callFrame->uncheckedR(dst).setRegLabel(pcstack.Head());
    }
    
    if (result) {
        if (*labelReq) {
            JSLabel dstLabel = JSLabel(); /* result.getValueLabel() */
            if(!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                // printf("Sensitive Upgrade at %ld\n", vPC - callFrame->codeBlock()->instructions().begin());
                dstLabel.setStar(true);
            }
            callFrame->uncheckedR(dst) = result;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(result.getValueLabel()));
        }
        else {
            callFrame->uncheckedR(dst) = result;
        }
        ASSERT(callFrame->uncheckedR(dst).jsValue());
    } else {
        callFrame->globalData().exception = createErrorForInvalidGlobalAssignment(callFrame, ident.ustring());
        // IFC4BC - Set the exception label
        callFrame->globalData().exception.setValueLabel(contextLabel);
    }
}

NEVER_INLINE bool Interpreter::resolveBaseAndProperty(CallFrame* callFrame, Instruction* vPC, JSValue& exceptionValue, bool* labelReq)
{
    int baseDst = vPC[1].u.operand;
    int propDst = vPC[2].u.operand;
    int property = vPC[3].u.operand;
    
    //IFC4BC
    JSLabel increasingContextLabel = pcstack.Head();
    //--------
    
    ScopeChainNode* scopeChain = callFrame->scopeChain();
    ScopeChainIterator iter = scopeChain->begin();
    ScopeChainIterator end = scopeChain->end();
    
    // FIXME: add scopeDepthIsZero optimization
    
    ASSERT(iter != end);
    
    CodeBlock* codeBlock = callFrame->codeBlock();
    Identifier& ident = codeBlock->identifier(property);
    JSObject* base;
    do {
        base = iter->get();
        PropertySlot slot(base);
        if (base->getPropertySlotIFC(callFrame, ident, slot, &increasingContextLabel)) {
            JSValue result = slot.getValue(callFrame, ident);
            //IFC4BC
            // if (result.getValueLabel().Star()) {
                // Add the context value to the result label
                increasingContextLabel = increasingContextLabel.Join(result.getValueLabel());
                // increasingContextLabel.setStar(false);
                result.setValueLabel(increasingContextLabel);
            // }
            // else // Pre-defined property, so making label 0.
            //    result.setValueLabel(increasingContextLabel);
            if (increasingContextLabel != pcstack.Head() && labelReq && (*labelReq == false))
            {
                *labelReq = true;
                callFrame->uncheckedR(propDst).setRegLabel(pcstack.Head());
                callFrame->uncheckedR(baseDst).setRegLabel(pcstack.Head());
            }
            if (JSLabel::ABORT_FLAG) {
                JSLabel::ABORT_FLAG = false;
                printf("Aborting in resolve base and property %d in %p!\n", (int) (vPC - codeBlock->instructions().begin()), codeBlock);
                // return jsUndefined();
            }
            exceptionValue = callFrame->globalData().exception;
            exceptionValue.setValueLabel(increasingContextLabel);
            if (exceptionValue)
                return false;
            //IFC4BC
            if (*labelReq) {
                JSLabel pdstLabel = JSLabel();
                JSLabel bdstLabel = JSLabel();
                if(!noSensitiveUpgrade(callFrame->r(propDst).getRegLabel()))
                {
                    // printf("Sensitive Upgrade at %ld in %p\n", vPC - codeBlock->instructions().begin(), codeBlock);
                    pdstLabel.setStar(true);
                }
                if(!noSensitiveUpgrade(callFrame->r(baseDst).getRegLabel()))
                {
                    // printf("Sensitive Upgrade at %ld in %p\n", vPC - codeBlock->instructions().begin(), codeBlock);
                    bdstLabel.setStar(true);
                }
                callFrame->uncheckedR(propDst) = JSValue(result);
                callFrame->uncheckedR(baseDst) = JSValue(base);
                callFrame->uncheckedR(propDst).setRegLabel(pdstLabel.Join(result.joinValueLabel(increasingContextLabel)));
                callFrame->uncheckedR(baseDst).setRegLabel(bdstLabel.Join(base->joinObjectLabel(increasingContextLabel)));
            }
            else {
                callFrame->uncheckedR(propDst) = JSValue(result);
                callFrame->uncheckedR(baseDst) = JSValue(base);
            }
            
            return true;
        }
        //IFC4BC
        increasingContextLabel = increasingContextLabel.Join(iter.getCurrentNode()->scopeNextLabel);
        //------
        ++iter;
    } while (iter != end);
    
    if (increasingContextLabel != pcstack.Head() && labelReq && (*labelReq == false))
    {
        *labelReq = true;
        callFrame->uncheckedR(propDst).setRegLabel(pcstack.Head());
        callFrame->uncheckedR(baseDst).setRegLabel(pcstack.Head());
    }
    exceptionValue = createUndefinedVariableError(callFrame, ident);
    exceptionValue.setValueLabel(increasingContextLabel);
    return false;
}

NEVER_INLINE bool Interpreter::resolveThisAndProperty(CallFrame* callFrame, Instruction* vPC, JSValue& exceptionValue, bool* labelReq)
{
    int thisDst = vPC[1].u.operand;
    int propDst = vPC[2].u.operand;
    int property = vPC[3].u.operand;
    
    ScopeChainNode* scopeChain = callFrame->scopeChain();
    ScopeChainIterator iter = scopeChain->begin();
    ScopeChainIterator end = scopeChain->end();
    
    //IFC4BC
    JSLabel increasingContextLabel = pcstack.Head();
    //--------
    
    // FIXME: add scopeDepthIsZero optimization
    
    ASSERT(iter != end);
    
    CodeBlock* codeBlock = callFrame->codeBlock();
    Identifier& ident = codeBlock->identifier(property);
    JSObject* base;
    do {
        base = iter->get();
        // IFC4BC
        // Original
        // ++iter;
        increasingContextLabel = increasingContextLabel.Join(base->getObjectLabel());
        PropertySlot slot(base);
        if (base->getPropertySlotIFC(callFrame, ident, slot, &increasingContextLabel)) {
            JSValue result = slot.getValue(callFrame, ident);
            // if (result.getValueLabel().Star()) {
                // Add the context value to the result label
                increasingContextLabel = increasingContextLabel.Join(result.getValueLabel());
                // increasingContextLabel.setStar(false);
                result.setValueLabel(increasingContextLabel);
            // }
            // else // Pre-defined property, so making label 0.
            //     result.setValueLabel(increasingContextLabel);
            if (increasingContextLabel != pcstack.Head() && labelReq && (*labelReq == false))
            {
                *labelReq = true;
                callFrame->uncheckedR(propDst).setRegLabel(pcstack.Head());
                callFrame->uncheckedR(thisDst).setRegLabel(pcstack.Head());
            }
            if (JSLabel::ABORT_FLAG) {
                JSLabel::ABORT_FLAG = false;
                printf("Aborting in resolve this and property %d in %p!\n", (int) (vPC - codeBlock->instructions().begin()), codeBlock);
                // return jsUndefined();
            }
            exceptionValue = callFrame->globalData().exception;
            // IFC4BC - Set the exception label
            exceptionValue.setValueLabel(increasingContextLabel);
            if (exceptionValue)
                return false;
            if (*labelReq) {
                JSLabel pdstLabel = JSLabel(); 
                if(!noSensitiveUpgrade(callFrame->r(propDst).getRegLabel()))
                {
                    // printf("Sensitive Upgrade at %ld in %p\n", vPC - codeBlock->instructions().begin(), codeBlock);
                    pdstLabel.setStar(true);
                }
                callFrame->uncheckedR(propDst) = JSValue(result);
                callFrame->uncheckedR(propDst).setRegLabel(pdstLabel.Join(result.getValueLabel()));
            }
            else {
                callFrame->uncheckedR(propDst) = JSValue(result);
            }
            // All entries on the scope chain should be EnvironmentRecords (activations etc),
            // other then 'with' object, which are directly referenced from the scope chain,
            // and the global object. If we hit either an EnvironmentRecord or a global
            // object at the end of the scope chain, this is undefined. If we hit a non-
            // EnvironmentRecord within the scope chain, pass the base as the this value.
            
            // IFC4BC
            ++iter;
            if (*labelReq) {
                JSLabel dstLabel = JSLabel();
                if(!noSensitiveUpgrade(callFrame->r(thisDst).getRegLabel()))
                {
                    // printf("Sensitive Upgrade at %ld in %p\n", vPC - codeBlock->instructions().begin(), codeBlock);
                    dstLabel.setStar(true);
                }
                if (iter == end || base->structure()->typeInfo().isEnvironmentRecord())
                    callFrame->uncheckedR(thisDst) = jsUndefined();
                else
                    callFrame->uncheckedR(thisDst) = JSValue(base);
                callFrame->uncheckedR(thisDst).setRegLabel(dstLabel.Join(increasingContextLabel));
            }
            else
            {
                if (iter == end || base->structure()->typeInfo().isEnvironmentRecord())
                    callFrame->uncheckedR(thisDst) = jsUndefined();
                else
                    callFrame->uncheckedR(thisDst) = JSValue(base);
            }
            return true;
        }
        //IFC4BC
        increasingContextLabel = increasingContextLabel.Join(iter.getCurrentNode()->scopeNextLabel);
        ++iter;
        //------
    } while (iter != end);
    
    if (increasingContextLabel != pcstack.Head() && labelReq && (*labelReq == false))
    {
        *labelReq = true;
        callFrame->uncheckedR(propDst).setRegLabel(pcstack.Head());
        callFrame->uncheckedR(thisDst).setRegLabel(pcstack.Head());
    }
    exceptionValue = createUndefinedVariableError(callFrame, ident);
    exceptionValue.setValueLabel(increasingContextLabel);
    return false;
}

#endif // ENABLE(CLASSIC_INTERPRETER)

ALWAYS_INLINE CallFrame* Interpreter::slideRegisterWindowForCall(CodeBlock* newCodeBlock, RegisterFile* registerFile, CallFrame* callFrame, size_t registerOffset, int argumentCountIncludingThis)
{
    // This ensures enough space for the worst case scenario of zero arguments passed by the caller.
    if (!registerFile->grow(callFrame->registers() + registerOffset + newCodeBlock->numParameters() + newCodeBlock->m_numCalleeRegisters))
        return 0;

    if (argumentCountIncludingThis >= newCodeBlock->numParameters()) {
        Register* newCallFrame = callFrame->registers() + registerOffset;
        return CallFrame::create(newCallFrame);
    }

    // Too few arguments -- copy arguments, then fill in missing arguments with undefined.
    size_t delta = newCodeBlock->numParameters() - argumentCountIncludingThis;
    CallFrame* newCallFrame = CallFrame::create(callFrame->registers() + registerOffset + delta);

    Register* dst = &newCallFrame->uncheckedR(CallFrame::thisArgumentOffset());
    Register* end = dst - argumentCountIncludingThis;
    for ( ; dst != end; --dst)
        *dst = *(dst - delta);

    end -= delta;
    
    for ( ; dst != end; --dst)
        *dst = jsUndefined();

    return newCallFrame;
}

/* Might be required for op_construct. Checking still!
// The label assignment is now done in op_call
// IFC4BC - New function to assign label for arguments not present and copied.
ALWAYS_INLINE CallFrame* Interpreter::slideRegisterWindowForCallIFC(CodeBlock* newCodeBlock, RegisterFile* registerFile, CallFrame* callFrame, size_t registerOffset, int argumentCountIncludingThis, JSLabel head)
{
    // This ensures enough space for the worst case scenario of zero arguments passed by the caller.
    if (!registerFile->grow(callFrame->registers() + registerOffset + newCodeBlock->numParameters() + newCodeBlock->m_numCalleeRegisters))
        return 0;
    
    if (argumentCountIncludingThis >= newCodeBlock->numParameters()) {
        Register* newCallFrame = callFrame->registers() + registerOffset;
        return CallFrame::create(newCallFrame);
    }
    
    // Too few arguments -- copy arguments, then fill in missing arguments with undefined.
    size_t delta = newCodeBlock->numParameters() - argumentCountIncludingThis;
    CallFrame* newCallFrame = CallFrame::create(callFrame->registers() + registerOffset + delta);
    
    Register* dst = &newCallFrame->uncheckedR(CallFrame::thisArgumentOffset());
    Register* end = dst - argumentCountIncludingThis;
    for ( ; dst != end; --dst)
        *dst = *(dst - delta);
    
    end -= delta;
    
    // Setting the label of the arguments that were not passed to the new function's context
    JSValue val = jsUndefined();
    val.setLabel(head);
    for ( ; dst != end; --dst){
        *dst = val;
    }
    
    return newCallFrame;
}
// IFC4BC-----------------------------------------------------*/
    
#if ENABLE(CLASSIC_INTERPRETER)
static NEVER_INLINE bool isInvalidParamForIn(CallFrame* callFrame, JSValue value, JSValue& exceptionData)
{
    if (value.isObject())
        return false;
    exceptionData = createInvalidParamError(callFrame, "in" , value);
    return true;
}

static NEVER_INLINE bool isInvalidParamForInstanceOf(CallFrame* callFrame, JSValue value, JSValue& exceptionData)
{
    if (value.isObject() && asObject(value)->structure()->typeInfo().implementsHasInstance())
        return false;
    exceptionData = createInvalidParamError(callFrame, "instanceof" , value);
    return true;
}
#endif

JSValue eval(CallFrame* callFrame)
{
    if (!callFrame->argumentCount())
        return jsUndefined();

    JSValue program = callFrame->argument(0);
    if (!program.isString())
        return program;
    
    TopCallFrameSetter topCallFrame(callFrame->globalData(), callFrame);
    UString programSource = asString(program)->value(callFrame);
    if (callFrame->hadException())
        return JSValue();
    
    CallFrame* callerFrame = callFrame->callerFrame();
    CodeBlock* callerCodeBlock = callerFrame->codeBlock();
    ScopeChainNode* callerScopeChain = callerFrame->scopeChain();
    EvalExecutable* eval = callerCodeBlock->evalCodeCache().tryGet(callerCodeBlock->isStrictMode(), programSource, callerScopeChain);

    if (!eval) {
        if (!callerCodeBlock->isStrictMode()) {
            // FIXME: We can use the preparser in strict mode, we just need additional logic
            // to prevent duplicates.
            if (programSource.is8Bit()) {
                LiteralParser<LChar> preparser(callFrame, programSource.characters8(), programSource.length(), NonStrictJSON);
                if (JSValue parsedObject = preparser.tryLiteralParse())
                    return parsedObject;
            } else {
                LiteralParser<UChar> preparser(callFrame, programSource.characters16(), programSource.length(), NonStrictJSON);
                if (JSValue parsedObject = preparser.tryLiteralParse())
                    return parsedObject;                
            }
        }

        JSValue exceptionValue;
        eval = callerCodeBlock->evalCodeCache().getSlow(callFrame, callerCodeBlock->ownerExecutable(), callerCodeBlock->isStrictMode(), programSource, callerScopeChain, exceptionValue);
        
        ASSERT(!eval == exceptionValue);
        if (UNLIKELY(!eval))
            return throwError(callFrame, exceptionValue);
    }

    JSValue thisValue = callerFrame->thisValue();
    ASSERT(isValidThisObject(thisValue, callFrame));
    Interpreter* interpreter = callFrame->globalData().interpreter;
    return interpreter->execute(eval, callFrame, thisValue, callerScopeChain, callFrame->registers() - interpreter->registerFile().begin() + 1 + RegisterFile::CallFrameHeaderSize);
}

CallFrame* loadVarargs(CallFrame* callFrame, RegisterFile* registerFile, JSValue thisValue, JSValue arguments, int firstFreeRegister)
{
    if (!arguments) { // f.apply(x, arguments), with arguments unmodified.
        unsigned argumentCountIncludingThis = callFrame->argumentCountIncludingThis();
        CallFrame* newCallFrame = CallFrame::create(callFrame->registers() + firstFreeRegister + argumentCountIncludingThis + RegisterFile::CallFrameHeaderSize);
        if (argumentCountIncludingThis > Arguments::MaxArguments + 1 || !registerFile->grow(newCallFrame->registers())) {
            callFrame->globalData().exception = createStackOverflowError(callFrame);
            return 0;
        }

        newCallFrame->setArgumentCountIncludingThis(argumentCountIncludingThis);
        newCallFrame->setThisValue(thisValue);
        for (size_t i = 0; i < callFrame->argumentCount(); ++i)
            newCallFrame->setArgument(i, callFrame->argument(i));
        return newCallFrame;
    }

    if (arguments.isUndefinedOrNull()) {
        CallFrame* newCallFrame = CallFrame::create(callFrame->registers() + firstFreeRegister + 1 + RegisterFile::CallFrameHeaderSize);
        if (!registerFile->grow(newCallFrame->registers())) {
            callFrame->globalData().exception = createStackOverflowError(callFrame);
            return 0;
        }
        newCallFrame->setArgumentCountIncludingThis(1);
        newCallFrame->setThisValue(thisValue);
        return newCallFrame;
    }

    if (!arguments.isObject()) {
        callFrame->globalData().exception = createInvalidParamError(callFrame, "Function.prototype.apply", arguments);
        return 0;
    }

    if (asObject(arguments)->classInfo() == &Arguments::s_info) {
        Arguments* argsObject = asArguments(arguments);
        unsigned argCount = argsObject->length(callFrame);
        CallFrame* newCallFrame = CallFrame::create(callFrame->registers() + firstFreeRegister + CallFrame::offsetFor(argCount + 1));
        if (argCount > Arguments::MaxArguments || !registerFile->grow(newCallFrame->registers())) {
            callFrame->globalData().exception = createStackOverflowError(callFrame);
            return 0;
        }
        newCallFrame->setArgumentCountIncludingThis(argCount + 1);
        newCallFrame->setThisValue(thisValue);
        argsObject->copyToArguments(callFrame, newCallFrame, argCount);
        return newCallFrame;
    }

    if (isJSArray(arguments)) {
        JSArray* array = asArray(arguments);
        unsigned argCount = array->length();
        CallFrame* newCallFrame = CallFrame::create(callFrame->registers() + firstFreeRegister + CallFrame::offsetFor(argCount + 1));
        if (argCount > Arguments::MaxArguments || !registerFile->grow(newCallFrame->registers())) {
            callFrame->globalData().exception = createStackOverflowError(callFrame);
            return 0;
        }
        newCallFrame->setArgumentCountIncludingThis(argCount + 1);
        newCallFrame->setThisValue(thisValue);
        array->copyToArguments(callFrame, newCallFrame, argCount);
        return newCallFrame;
    }

    JSObject* argObject = asObject(arguments);
    unsigned argCount = argObject->get(callFrame, callFrame->propertyNames().length).toUInt32(callFrame);
    CallFrame* newCallFrame = CallFrame::create(callFrame->registers() + firstFreeRegister + CallFrame::offsetFor(argCount + 1));
    if (argCount > Arguments::MaxArguments || !registerFile->grow(newCallFrame->registers())) {
        callFrame->globalData().exception = createStackOverflowError(callFrame);
        return 0;
    }
    newCallFrame->setArgumentCountIncludingThis(argCount + 1);
    newCallFrame->setThisValue(thisValue);
    for (size_t i = 0; i < argCount; ++i) {
        newCallFrame->setArgument(i, asObject(arguments)->get(callFrame, i));
        if (UNLIKELY(callFrame->globalData().exception))
            return 0;
    }
    return newCallFrame;
}

Interpreter::Interpreter()
    : m_sampleEntryDepth(0)
    , m_reentryDepth(0)
#if !ASSERT_DISABLED
    , m_initialized(false)
#endif
    , m_classicEnabled(false)
{
}

Interpreter::~Interpreter()
{
#if ENABLE(LLINT)
    if (m_classicEnabled)
        delete[] m_opcodeTable;
#endif
}

void Interpreter::initialize(LLInt::Data* llintData, bool canUseJIT)
{
    UNUSED_PARAM(llintData);
    UNUSED_PARAM(canUseJIT);

    // If we have LLInt, then we shouldn't be building any kind of classic interpreter.
#if ENABLE(LLINT) && ENABLE(CLASSIC_INTERPRETER)
#error "Building both LLInt and the Classic Interpreter is not supported because it doesn't make sense."
#endif

#if ENABLE(LLINT)
    m_opcodeTable = llintData->opcodeMap();
    for (int i = 0; i < numOpcodeIDs; ++i)
        m_opcodeIDTable.add(m_opcodeTable[i], static_cast<OpcodeID>(i));
    m_classicEnabled = false;
#elif ENABLE(COMPUTED_GOTO_CLASSIC_INTERPRETER)
    if (canUseJIT) {
        // If the JIT is present, don't use jump destinations for opcodes.
        
        for (int i = 0; i < numOpcodeIDs; ++i) {
            Opcode opcode = bitwise_cast<void*>(static_cast<uintptr_t>(i));
            m_opcodeTable[i] = opcode;
        }
        m_classicEnabled = false;
    } else {
        JSLabel::pcGlobalLabel.clabel = 0;
        JSLabel::BRANCH_FLAG = false;
        // JSLabel::pcGlobalLabel.plabel = 0;
        privateExecute(InitializeAndReturn, 0, 0, 0);
        
        for (int i = 0; i < numOpcodeIDs; ++i)
            m_opcodeIDTable.add(m_opcodeTable[i], static_cast<OpcodeID>(i));
        
        m_classicEnabled = true;
    }
#else
#if ENABLE(CLASSIC_INTERPRETER)
    m_classicEnabled = true;
#else
    m_classicEnabled = false;
#endif
#endif // ENABLE(COMPUTED_GOTO_CLASSIC_INTERPRETER)
#if !ASSERT_DISABLED
    m_initialized = true;
#endif

#if ENABLE(OPCODE_SAMPLING)
    enableSampler();
#endif
}

#ifndef NDEBUG

void Interpreter::dumpCallFrame(CallFrame* callFrame)
{
    callFrame->codeBlock()->dump(callFrame);
    dumpRegisters(callFrame);
}

void Interpreter::dumpRegisters(CallFrame* callFrame)
{
    dataLog("Register frame: \n\n");
    dataLog("-----------------------------------------------------------------------------\n");
    dataLog("            use            |   address  |                value               \n");
    dataLog("-----------------------------------------------------------------------------\n");

    CodeBlock* codeBlock = callFrame->codeBlock();
    const Register* it;
    const Register* end;
    JSValue v;

    it = callFrame->registers() - RegisterFile::CallFrameHeaderSize - codeBlock->numParameters();
    v = (*it).jsValue();
#if USE(JSVALUE32_64)
    dataLog("[this]                     | %10p | %-16s 0x%llx \n", it, v.description(), JSValue::encode(v)); ++it;
#else
    dataLog("[this]                     | %10p | %-16s %p \n", it, v.description(), JSValue::encode(v)); ++it;
#endif
    end = it + max(codeBlock->numParameters() - 1, 0); // - 1 to skip "this"
    if (it != end) {
        do {
            v = (*it).jsValue();
#if USE(JSVALUE32_64)
            dataLog("[param]                    | %10p | %-16s 0x%llx \n", it, v.description(), JSValue::encode(v));
#else
            dataLog("[param]                    | %10p | %-16s %p \n", it, v.description(), JSValue::encode(v));
#endif
            ++it;
        } while (it != end);
    }
    dataLog("-----------------------------------------------------------------------------\n");
    dataLog("[CodeBlock]                | %10p | %p \n", it, (*it).codeBlock()); ++it;
    dataLog("[ScopeChain]               | %10p | %p \n", it, (*it).scopeChain()); ++it;
    dataLog("[CallerRegisters]          | %10p | %d \n", it, (*it).i()); ++it;
    dataLog("[ReturnPC]                 | %10p | %p \n", it, (*it).vPC()); ++it;
    dataLog("[ArgumentCount]            | %10p | %d \n", it, (*it).i()); ++it;
    dataLog("[Callee]                   | %10p | %p \n", it, (*it).function()); ++it;
    dataLog("-----------------------------------------------------------------------------\n");

    int registerCount = 0;

    end = it + codeBlock->m_numVars;
    if (it != end) {
        do {
            v = (*it).jsValue();
#if USE(JSVALUE32_64)
            dataLog("[r%2d]                      | %10p | %-16s 0x%llx \n", registerCount, it, v.description(), JSValue::encode(v));
#else
            dataLog("[r%2d]                      | %10p | %-16s %p \n", registerCount, it, v.description(), JSValue::encode(v));
#endif
            ++it;
            ++registerCount;
        } while (it != end);
    }
    dataLog("-----------------------------------------------------------------------------\n");

    end = it + codeBlock->m_numCalleeRegisters - codeBlock->m_numVars;
    if (it != end) {
        do {
            v = (*it).jsValue();
#if USE(JSVALUE32_64)
            dataLog("[r%2d]                      | %10p | %-16s 0x%llx \n", registerCount, it, v.description(), JSValue::encode(v));
#else
            dataLog("[r%2d]                      | %10p | %-16s %p \n", registerCount, it, v.description(), JSValue::encode(v));
#endif
            ++it;
            ++registerCount;
        } while (it != end);
    }
    dataLog("-----------------------------------------------------------------------------\n");
}

#endif

bool Interpreter::isOpcode(Opcode opcode)
{
#if ENABLE(COMPUTED_GOTO_CLASSIC_INTERPRETER) || ENABLE(LLINT)
#if !ENABLE(LLINT)
    if (!m_classicEnabled)
        return opcode >= 0 && static_cast<OpcodeID>(bitwise_cast<uintptr_t>(opcode)) <= op_end;
#endif
    return opcode != HashTraits<Opcode>::emptyValue()
        && !HashTraits<Opcode>::isDeletedValue(opcode)
        && m_opcodeIDTable.contains(opcode);
#else
    return opcode >= 0 && opcode <= op_end;
#endif
}

NEVER_INLINE bool Interpreter::unwindCallFrame(CallFrame*& callFrame, JSValue exceptionValue, unsigned& bytecodeOffset, CodeBlock*& codeBlock)
{
    CodeBlock* oldCodeBlock = codeBlock;
    ScopeChainNode* scopeChain = callFrame->scopeChain();

    if (Debugger* debugger = callFrame->dynamicGlobalObject()->debugger()) {
        DebuggerCallFrame debuggerCallFrame(callFrame, exceptionValue);
        if (callFrame->callee())
            debugger->returnEvent(debuggerCallFrame, codeBlock->ownerExecutable()->sourceID(), codeBlock->ownerExecutable()->lastLine());
        else
            debugger->didExecuteProgram(debuggerCallFrame, codeBlock->ownerExecutable()->sourceID(), codeBlock->ownerExecutable()->lastLine());
    }

    // If this call frame created an activation or an 'arguments' object, tear it off.
    if (oldCodeBlock->codeType() == FunctionCode && oldCodeBlock->needsFullScopeChain()) {
        if (!callFrame->uncheckedR(oldCodeBlock->activationRegister()).jsValue()) {
            oldCodeBlock->createActivation(callFrame);
            scopeChain = callFrame->scopeChain();
        }
        while (!scopeChain->object->inherits(&JSActivation::s_info))
            scopeChain = scopeChain->pop();

        callFrame->setScopeChain(scopeChain);
        JSActivation* activation = asActivation(scopeChain->object.get());
        activation->tearOff(*scopeChain->globalData);
        if (JSValue arguments = callFrame->uncheckedR(unmodifiedArgumentsRegister(oldCodeBlock->argumentsRegister())).jsValue())
            asArguments(arguments)->didTearOffActivation(callFrame->globalData(), activation);
    } else if (oldCodeBlock->usesArguments() && !oldCodeBlock->isStrictMode()) {
        if (JSValue arguments = callFrame->uncheckedR(unmodifiedArgumentsRegister(oldCodeBlock->argumentsRegister())).jsValue())
            asArguments(arguments)->tearOff(callFrame);
    }

    CallFrame* callerFrame = callFrame->callerFrame();
    callFrame->globalData().topCallFrame = callerFrame;
    if (callerFrame->hasHostCallFrameFlag())
        return false;

    codeBlock = callerFrame->codeBlock();
    
    // Because of how the JIT records call site->bytecode offset
    // information the JIT reports the bytecodeOffset for the returnPC
    // to be at the beginning of the opcode that has caused the call.
    // In the interpreter we have an actual return address, which is
    // the beginning of next instruction to execute. To get an offset
    // inside the call instruction that triggered the exception we
    // have to subtract 1.
#if ENABLE(JIT) && ENABLE(CLASSIC_INTERPRETER)
    if (callerFrame->globalData().canUseJIT())
        bytecodeOffset = codeBlock->bytecodeOffset(callerFrame, callFrame->returnPC());
    else
        bytecodeOffset = codeBlock->bytecodeOffset(callFrame->returnVPC()) - 1;
#elif ENABLE(JIT)
    bytecodeOffset = codeBlock->bytecodeOffset(callerFrame, callFrame->returnPC());
#else
    bytecodeOffset = codeBlock->bytecodeOffset(callFrame->returnVPC()) - 1;
#endif

    callFrame = callerFrame;
    return true;
}

static void appendSourceToError(CallFrame* callFrame, ErrorInstance* exception, unsigned bytecodeOffset)
{
    exception->clearAppendSourceToMessage();

    if (!callFrame->codeBlock()->hasExpressionInfo())
        return;

    int startOffset = 0;
    int endOffset = 0;
    int divotPoint = 0;

    CodeBlock* codeBlock = callFrame->codeBlock();
    codeBlock->expressionRangeForBytecodeOffset(bytecodeOffset, divotPoint, startOffset, endOffset);

    int expressionStart = divotPoint - startOffset;
    int expressionStop = divotPoint + endOffset;

    if (!expressionStop || expressionStart > codeBlock->source()->length())
        return;

    JSGlobalData* globalData = &callFrame->globalData();
    JSValue jsMessage = exception->getDirect(*globalData, globalData->propertyNames->message);
    if (!jsMessage || !jsMessage.isString())
        return;

    UString message = asString(jsMessage)->value(callFrame);

    if (expressionStart < expressionStop)
        message =  makeUString(message, " (evaluating '", codeBlock->source()->getRange(expressionStart, expressionStop), "')");
    else {
        // No range information, so give a few characters of context
        const StringImpl* data = codeBlock->source()->data();
        int dataLength = codeBlock->source()->length();
        int start = expressionStart;
        int stop = expressionStart;
        // Get up to 20 characters of context to the left and right of the divot, clamping to the line.
        // then strip whitespace.
        while (start > 0 && (expressionStart - start < 20) && (*data)[start - 1] != '\n')
            start--;
        while (start < (expressionStart - 1) && isStrWhiteSpace((*data)[start]))
            start++;
        while (stop < dataLength && (stop - expressionStart < 20) && (*data)[stop] != '\n')
            stop++;
        while (stop > expressionStart && isStrWhiteSpace((*data)[stop - 1]))
            stop--;
        message = makeUString(message, " (near '...", codeBlock->source()->getRange(start, stop), "...')");
    }

    exception->putDirect(*globalData, globalData->propertyNames->message, jsString(globalData, message));
}

static int getLineNumberForCallFrame(JSGlobalData* globalData, CallFrame* callFrame)
{
    UNUSED_PARAM(globalData);
    callFrame = callFrame->removeHostCallFrameFlag();
    CodeBlock* codeBlock = callFrame->codeBlock();
    if (!codeBlock)
        return -1;
#if ENABLE(CLASSIC_INTERPRETER)
    if (!globalData->canUseJIT())
        return codeBlock->lineNumberForBytecodeOffset(callFrame->bytecodeOffsetForNonDFGCode() - 1);
#endif
#if ENABLE(JIT)
#if ENABLE(DFG_JIT)
    if (codeBlock->getJITType() == JITCode::DFGJIT)
        return codeBlock->lineNumberForBytecodeOffset(codeBlock->codeOrigin(callFrame->codeOriginIndexForDFG()).bytecodeIndex);
#endif
    return codeBlock->lineNumberForBytecodeOffset(callFrame->bytecodeOffsetForNonDFGCode());
#else
    return -1;
#endif
}

static CallFrame* getCallerInfo(JSGlobalData* globalData, CallFrame* callFrame, int& lineNumber)
{
    UNUSED_PARAM(globalData);
    unsigned bytecodeOffset = 0;
    lineNumber = -1;
    ASSERT(!callFrame->hasHostCallFrameFlag());
    CallFrame* callerFrame = callFrame->codeBlock() ? callFrame->trueCallerFrame() : callFrame->callerFrame()->removeHostCallFrameFlag();
    bool callframeIsHost = callerFrame->addHostCallFrameFlag() == callFrame->callerFrame();
    ASSERT(!callerFrame->hasHostCallFrameFlag());

    if (callerFrame == CallFrame::noCaller() || !callerFrame || !callerFrame->codeBlock())
        return callerFrame;
    
    CodeBlock* callerCodeBlock = callerFrame->codeBlock();
    
#if ENABLE(JIT)
    if (!callFrame->hasReturnPC())
        callframeIsHost = true;
#endif
#if ENABLE(DFG_JIT)
    if (callFrame->isInlineCallFrame())
        callframeIsHost = false;
#endif

    if (callframeIsHost) {
        // Don't need to deal with inline callframes here as by definition we haven't
        // inlined a call with an intervening native call frame.
#if ENABLE(CLASSIC_INTERPRETER)
        if (!globalData->canUseJIT()) {
            bytecodeOffset = callerFrame->bytecodeOffsetForNonDFGCode();
            lineNumber = callerCodeBlock->lineNumberForBytecodeOffset(bytecodeOffset - 1);
            return callerFrame;
        }
#endif
#if ENABLE(JIT)
#if ENABLE(DFG_JIT)
        if (callerCodeBlock && callerCodeBlock->getJITType() == JITCode::DFGJIT) {
            unsigned codeOriginIndex = callerFrame->codeOriginIndexForDFG();
            bytecodeOffset = callerCodeBlock->codeOrigin(codeOriginIndex).bytecodeIndex;
        } else
#endif
            bytecodeOffset = callerFrame->bytecodeOffsetForNonDFGCode();
#endif
    } else {
#if ENABLE(CLASSIC_INTERPRETER)
        if (!globalData->canUseJIT()) {
            bytecodeOffset = callerCodeBlock->bytecodeOffset(callFrame->returnVPC());
            lineNumber = callerCodeBlock->lineNumberForBytecodeOffset(bytecodeOffset - 1);
            return callerFrame;
        }
#endif
#if ENABLE(JIT)
    #if ENABLE(DFG_JIT)
        if (callFrame->isInlineCallFrame()) {
            InlineCallFrame* icf = callFrame->inlineCallFrame();
            bytecodeOffset = icf->caller.bytecodeIndex;
            if (InlineCallFrame* parentCallFrame = icf->caller.inlineCallFrame) {
                FunctionExecutable* executable = static_cast<FunctionExecutable*>(parentCallFrame->executable.get());
                CodeBlock* newCodeBlock = executable->baselineCodeBlockFor(parentCallFrame->isCall ? CodeForCall : CodeForConstruct);
                ASSERT(newCodeBlock);
                ASSERT(newCodeBlock->instructionCount() > bytecodeOffset);
                callerCodeBlock = newCodeBlock;
            }
        } else if (callerCodeBlock && callerCodeBlock->getJITType() == JITCode::DFGJIT) {
            CodeOrigin origin;
            if (!callerCodeBlock->codeOriginForReturn(callFrame->returnPC(), origin))
                ASSERT_NOT_REACHED();
            bytecodeOffset = origin.bytecodeIndex;
            if (InlineCallFrame* icf = origin.inlineCallFrame) {
                FunctionExecutable* executable = static_cast<FunctionExecutable*>(icf->executable.get());
                CodeBlock* newCodeBlock = executable->baselineCodeBlockFor(icf->isCall ? CodeForCall : CodeForConstruct);
                ASSERT(newCodeBlock);
                ASSERT(newCodeBlock->instructionCount() > bytecodeOffset);
                callerCodeBlock = newCodeBlock;
            }
        } else
    #endif
            bytecodeOffset = callerCodeBlock->bytecodeOffset(callerFrame, callFrame->returnPC());
#endif
    }

    lineNumber = callerCodeBlock->lineNumberForBytecodeOffset(bytecodeOffset);
    return callerFrame;
}

static ALWAYS_INLINE const UString getSourceURLFromCallFrame(CallFrame* callFrame) 
{
    ASSERT(!callFrame->hasHostCallFrameFlag());
#if ENABLE(CLASSIC_INTERPRETER)
#if ENABLE(JIT)
    if (callFrame->globalData().canUseJIT())
        return callFrame->codeBlock()->ownerExecutable()->sourceURL();
#endif
    return callFrame->codeBlock()->source()->url();

#else
    return callFrame->codeBlock()->ownerExecutable()->sourceURL();
#endif
}

static StackFrameCodeType getStackFrameCodeType(CallFrame* callFrame)
{
    ASSERT(!callFrame->hasHostCallFrameFlag());

    switch (callFrame->codeBlock()->codeType()) {
    case EvalCode:
        return StackFrameEvalCode;
    case FunctionCode:
        return StackFrameFunctionCode;
    case GlobalCode:
        return StackFrameGlobalCode;
    }
    ASSERT_NOT_REACHED();
    return StackFrameGlobalCode;
}

void Interpreter::getStackTrace(JSGlobalData* globalData, Vector<StackFrame>& results)
{
    CallFrame* callFrame = globalData->topCallFrame->removeHostCallFrameFlag();
    if (!callFrame || callFrame == CallFrame::noCaller()) 
        return;
    int line = getLineNumberForCallFrame(globalData, callFrame);

    callFrame = callFrame->trueCallFrameFromVMCode();

    while (callFrame && callFrame != CallFrame::noCaller()) {
        UString sourceURL;
        if (callFrame->codeBlock()) {
            sourceURL = getSourceURLFromCallFrame(callFrame);
            StackFrame s = { Strong<JSObject>(*globalData, callFrame->callee()), getStackFrameCodeType(callFrame), Strong<ExecutableBase>(*globalData, callFrame->codeBlock()->ownerExecutable()), line, sourceURL};
            results.append(s);
        } else {
            StackFrame s = { Strong<JSObject>(*globalData, callFrame->callee()), StackFrameNativeCode, Strong<ExecutableBase>(), -1, UString()};
            results.append(s);
        }
        callFrame = getCallerInfo(globalData, callFrame, line);
    }
}

void Interpreter::addStackTraceIfNecessary(CallFrame* callFrame, JSObject* error)
{
    JSGlobalData* globalData = &callFrame->globalData();
    ASSERT(callFrame == globalData->topCallFrame || callFrame == callFrame->lexicalGlobalObject()->globalExec() || callFrame == callFrame->dynamicGlobalObject()->globalExec());
    if (error->hasProperty(callFrame, globalData->propertyNames->stack))
        return;

    Vector<StackFrame> stackTrace;
    getStackTrace(&callFrame->globalData(), stackTrace);
    
    if (stackTrace.isEmpty())
        return;
    
    JSGlobalObject* globalObject = 0;
    if (isTerminatedExecutionException(error) || isInterruptedExecutionException(error))
        globalObject = globalData->dynamicGlobalObject;
    else
        globalObject = error->globalObject();
    StringBuilder builder;
    for (unsigned i = 0; i < stackTrace.size(); i++) {
        builder.append(String(stackTrace[i].toString(globalObject->globalExec()).impl()));
        if (i != stackTrace.size() - 1)
            builder.append('\n');
    }
    
    error->putDirect(*globalData, globalData->propertyNames->stack, jsString(globalData, UString(builder.toString().impl())), ReadOnly | DontDelete);
}

NEVER_INLINE HandlerInfo* Interpreter::throwException(CallFrame*& callFrame, JSValue& exceptionValue, unsigned bytecodeOffset)
{
    CodeBlock* codeBlock = callFrame->codeBlock();
    bool isInterrupt = false;

    ASSERT(!exceptionValue.isEmpty());
    ASSERT(!exceptionValue.isCell() || exceptionValue.asCell());
    // This shouldn't be possible (hence the assertions), but we're already in the slowest of
    // slow cases, so let's harden against it anyway to be safe.
    if (exceptionValue.isEmpty() || (exceptionValue.isCell() && !exceptionValue.asCell())) {
        // IFC4BC - preserving the label of the exceptionvalue
        JSLabel excLabel = exceptionValue.getValueLabel();
        exceptionValue = jsNull(); // Original
        exceptionValue.setValueLabel(excLabel);
    }

    // Set up the exception object
    if (exceptionValue.isObject()) {
        JSObject* exception = asObject(exceptionValue);

        if (exception->isErrorInstance() && static_cast<ErrorInstance*>(exception)->appendSourceToMessage())
            appendSourceToError(callFrame, static_cast<ErrorInstance*>(exception), bytecodeOffset);

        if (!hasErrorInfo(callFrame, exception)) {
            // FIXME: should only really be adding these properties to VM generated exceptions,
            // but the inspector currently requires these for all thrown objects.
            addErrorInfo(callFrame, exception, codeBlock->lineNumberForBytecodeOffset(bytecodeOffset), codeBlock->ownerExecutable()->source());
        }

        isInterrupt = isInterruptedExecutionException(exception) || isTerminatedExecutionException(exception);
    }

    if (Debugger* debugger = callFrame->dynamicGlobalObject()->debugger()) {
        DebuggerCallFrame debuggerCallFrame(callFrame, exceptionValue);
        bool hasHandler = codeBlock->handlerForBytecodeOffset(bytecodeOffset);
        debugger->exception(debuggerCallFrame, codeBlock->ownerExecutable()->sourceID(), codeBlock->lineNumberForBytecodeOffset(bytecodeOffset), hasHandler);
    }

    // Calculate an exception handler vPC, unwinding call frames as necessary.
    HandlerInfo* handler = 0;
    while (isInterrupt || !(handler = codeBlock->handlerForBytecodeOffset(bytecodeOffset))) {
        if (!unwindCallFrame(callFrame, exceptionValue, bytecodeOffset, codeBlock)) {
            if (Profiler* profiler = callFrame->globalData().enabledProfiler())
                profiler->exceptionUnwind(callFrame);
            callFrame->globalData().topCallFrame = callFrame;
            return 0;
        }
    }
    callFrame->globalData().topCallFrame = callFrame;

    if (Profiler* profiler = callFrame->globalData().enabledProfiler())
        profiler->exceptionUnwind(callFrame);

    // Shrink the JS stack, in case stack overflow made it huge.
    Register* highWaterMark = 0;
    for (CallFrame* callerFrame = callFrame; callerFrame; callerFrame = callerFrame->callerFrame()->removeHostCallFrameFlag()) {
        CodeBlock* codeBlock = callerFrame->codeBlock();
        if (!codeBlock)
            continue;
        Register* callerHighWaterMark = callerFrame->registers() + codeBlock->m_numCalleeRegisters;
        highWaterMark = max(highWaterMark, callerHighWaterMark);
    }
    m_registerFile.shrink(highWaterMark);

    // Unwind the scope chain within the exception handler's call frame.
    ScopeChainNode* scopeChain = callFrame->scopeChain();
    int scopeDelta = 0;
    if (!codeBlock->needsFullScopeChain() || codeBlock->codeType() != FunctionCode 
        || callFrame->uncheckedR(codeBlock->activationRegister()).jsValue())
        scopeDelta = depth(codeBlock, scopeChain) - handler->scopeDepth;
    ASSERT(scopeDelta >= 0);
    while (scopeDelta--)
        scopeChain = scopeChain->pop();
    callFrame->setScopeChain(scopeChain);

    return handler;
}

static inline JSValue checkedReturn(JSValue returnValue)
{
    ASSERT(returnValue);
    return returnValue;
}

static inline JSObject* checkedReturn(JSObject* returnValue)
{
    ASSERT(returnValue);
    return returnValue;
}

JSValue Interpreter::execute(ProgramExecutable* program, CallFrame* callFrame, ScopeChainNode* scopeChain, JSObject* thisObj)
{
    ASSERT(isValidThisObject(thisObj, callFrame));
    ASSERT(!scopeChain->globalData->exception);
    ASSERT(!callFrame->globalData().isCollectorBusy());
    if (callFrame->globalData().isCollectorBusy())
        CRASH();

    if (m_reentryDepth >= MaxSmallThreadReentryDepth && m_reentryDepth >= callFrame->globalData().maxReentryDepth)
        return checkedReturn(throwStackOverflowError(callFrame));

    DynamicGlobalObjectScope globalObjectScope(*scopeChain->globalData, scopeChain->globalObject.get());
    Vector<JSONPData> JSONPData;
    bool parseResult;
    const UString programSource = program->source().toString();
    const UString checkUnknown = "srcunknown";
    unsigned unknownScript = programSource.find(checkUnknown);
    if (unknownScript <= 10) {
        printf("Unknown script detected.\n");
        return jsUndefined();
    }
    
    // IFC4BC - Setting the policy
    const char* pUrl = program->sourceURL().utf8().data();
    JSLabel srcLabel = JSLabel(URLMap::urlmap().getLabel(pUrl));
    if (srcLabel.Val() == 1) {
        JSLabel::pcGlobalLabel.clabel = srcLabel.Val();
        // JSLabel::pcGlobalLabel.plabel = srcLabel.pLabel;
    }
    // ---------------------------
    
    if (programSource.isNull())
        return jsUndefined();
    if (programSource.is8Bit()) {
        LiteralParser<LChar> literalParser(callFrame, programSource.characters8(), programSource.length(), JSONP);
        parseResult = literalParser.tryJSONPParse(JSONPData, scopeChain->globalObject->globalObjectMethodTable()->supportsRichSourceInfo(scopeChain->globalObject.get()));
    } else {
        LiteralParser<UChar> literalParser(callFrame, programSource.characters16(), programSource.length(), JSONP);
        parseResult = literalParser.tryJSONPParse(JSONPData, scopeChain->globalObject->globalObjectMethodTable()->supportsRichSourceInfo(scopeChain->globalObject.get()));
    }

    if (parseResult) {
        JSGlobalObject* globalObject = scopeChain->globalObject.get();
        JSValue result;
        for (unsigned entry = 0; entry < JSONPData.size(); entry++) {
            Vector<JSONPPathEntry> JSONPPath;
            JSONPPath.swap(JSONPData[entry].m_path);
            JSValue JSONPValue = JSONPData[entry].m_value.get();
            if (JSONPPath.size() == 1 && JSONPPath[0].m_type == JSONPPathEntryTypeDeclare) {
                if (globalObject->hasProperty(callFrame, JSONPPath[0].m_pathEntryName)) {
                    PutPropertySlot slot;
                    globalObject->methodTable()->put(globalObject, callFrame, JSONPPath[0].m_pathEntryName, JSONPValue, slot);
                } else
                    globalObject->methodTable()->putDirectVirtual(globalObject, callFrame, JSONPPath[0].m_pathEntryName, JSONPValue, DontEnum | DontDelete);
                // var declarations return undefined
                result = jsUndefined();
                continue;
            }
            JSValue baseObject(globalObject);
            for (unsigned i = 0; i < JSONPPath.size() - 1; i++) {
                ASSERT(JSONPPath[i].m_type != JSONPPathEntryTypeDeclare);
                switch (JSONPPath[i].m_type) {
                case JSONPPathEntryTypeDot: {
                    if (i == 0) {
                        PropertySlot slot(globalObject);
                        if (!globalObject->getPropertySlot(callFrame, JSONPPath[i].m_pathEntryName, slot)) {
                            if (entry)
                                return throwError(callFrame, createUndefinedVariableError(globalObject->globalExec(), JSONPPath[i].m_pathEntryName));
                            goto failedJSONP;
                        }
                        baseObject = slot.getValue(callFrame, JSONPPath[i].m_pathEntryName);
                    } else
                        baseObject = baseObject.get(callFrame, JSONPPath[i].m_pathEntryName);
                    if (callFrame->hadException())
                        return jsUndefined();
                    continue;
                }
                case JSONPPathEntryTypeLookup: {
                    baseObject = baseObject.get(callFrame, JSONPPath[i].m_pathIndex);
                    if (callFrame->hadException())
                        return jsUndefined();
                    continue;
                }
                default:
                    ASSERT_NOT_REACHED();
                    return jsUndefined();
                }
            }
            PutPropertySlot slot;
            switch (JSONPPath.last().m_type) {
            case JSONPPathEntryTypeCall: {
                JSValue function = baseObject.get(callFrame, JSONPPath.last().m_pathEntryName);
                if (callFrame->hadException())
                    return jsUndefined();
                CallData callData;
                CallType callType = getCallData(function, callData);
                if (callType == CallTypeNone)
                    return throwError(callFrame, createNotAFunctionError(callFrame, function));
                MarkedArgumentBuffer jsonArg;
                jsonArg.append(JSONPValue);
                JSValue thisValue = JSONPPath.size() == 1 ? jsUndefined(): baseObject;
                JSONPValue = JSC::call(callFrame, function, callType, callData, thisValue, jsonArg);
                if (callFrame->hadException())
                    return jsUndefined();
                break;
            }
            case JSONPPathEntryTypeDot: {
                baseObject.put(callFrame, JSONPPath.last().m_pathEntryName, JSONPValue, slot);
                if (callFrame->hadException())
                    return jsUndefined();
                break;
            }
            case JSONPPathEntryTypeLookup: {
                baseObject.putByIndex(callFrame, JSONPPath.last().m_pathIndex, JSONPValue, slot.isStrictMode());
                if (callFrame->hadException())
                    return jsUndefined();
                break;
            }
            default:
                ASSERT_NOT_REACHED();
                    return jsUndefined();
            }
            result = JSONPValue;
        }
        return result;
    }
failedJSONP:
    
    // IFC4BC -- Adidng the source URL to get a label
    // Need to be here as sometimes the privateExecute does not execute
    
    
   // const char* sURL = program->sourceURL().utf8().data();
    // Very Important Here you will get the URL of the source JS
    
   // printf("gdfgdf %s\n", sURL);
    

    // IFC4BC ---------------------------------------------------------
    
    JSObject* error = program->compile(callFrame, scopeChain);
    if (error)
        return checkedReturn(throwError(callFrame, error));
    CodeBlock* codeBlock = &program->generatedBytecode();
    
    Register* oldEnd = m_registerFile.end();
    Register* newEnd = oldEnd + codeBlock->numParameters() + RegisterFile::CallFrameHeaderSize + codeBlock->m_numCalleeRegisters;
    if (!m_registerFile.grow(newEnd))
        return checkedReturn(throwStackOverflowError(callFrame));

    CallFrame* newCallFrame = CallFrame::create(oldEnd + codeBlock->numParameters() + RegisterFile::CallFrameHeaderSize);
    ASSERT(codeBlock->numParameters() == 1); // 1 parameter for 'this'.
    newCallFrame->init(codeBlock, 0, scopeChain, CallFrame::noCaller(), codeBlock->numParameters(), 0);
    newCallFrame->setThisValue(thisObj);
    TopCallFrameSetter topCallFrame(callFrame->globalData(), newCallFrame);

    if (Profiler* profiler = callFrame->globalData().enabledProfiler())
        profiler->willExecute(callFrame, program->sourceURL(), program->lineNo());

    JSValue result;
    {
        SamplingTool::CallRecord callRecord(m_sampler.get());

        m_reentryDepth++;  
#if ENABLE(JIT)
        if (!classicEnabled())
            result = program->generatedJITCode().execute(&m_registerFile, newCallFrame, scopeChain->globalData);
        else
#endif
        {
            //ASSERT(pcSLen == 0);
            // IFC4BC -- Setting the current pc to the source being executed
          //  const char* sURL = program->sourceURL().utf8().data();
            //char *temp = strstr(sURL, ".policy");
            //printf("gdfgdfg gdfgdf %s dsfds", temp);
            JSLabel srcLabel;
            //if(temp) srcLabel = JSLabel(URLMap::urlmap().getLabel(sURL, 1));
            // printf("%lld fdsghfghjdsghjf", JSLabel::pcGlobalLabel.clabel);
            //    if(strstr(program->sourceURL().utf8().data(), ".policy")){
            //        if(strcmp(strstr(program->sourceURL().utf8().data(), ".policy"),".policy") == 0)
            //        {
            //            srcLabel = JSLabel(URLMap::urlmap().getLabel(program->sourceURL().utf8().data()));
            //        }
            //        else
            //        {
            //            srcLabel = JSLabel(URLMap::urlmap().getLabel(program->sourceURL().utf8().data()));
            //        }
            //    }
            //    else {
            //        URLMap::urlmap().put(program->sourceURL().utf8().data(),false);
            //    }

            srcLabel = JSLabel(URLMap::urlmap().getLabel(pUrl));
            // printf("Src Label is %lld\n", srcLabel.Val());
            if (srcLabel.Val() == 1)
                pcstack.Push(JSLabel(srcLabel), -1, newCallFrame->registers());
            else
                pcstack.Push(JSLabel(), -1, newCallFrame->registers());
            // printf("Pushed label %llu on the stack with len %d\n",srcLabel.Val(), pcSLen);
            // IFC4BC ------------------------------------------------------
            
            // newCallFrame->codeBlock()->contextLabel = srcLabel;
            /*
             struct timeval t0,t1;
             int rc;
             rc = gettimeofday(&t0,NULL);
             if(rc==0){
             
             }
             else{
             printf("################### getimeofday faileddddd\n");
             }
                         
             */
            
            if(srcLabel.Val() == 1)
                result = privateExecute(Normal, &m_registerFile, newCallFrame, true);
            else
                result = privateExecute(Normal, &m_registerFile, newCallFrame, false);
            //else result = privateExecute(Normal, &m_registerFile, newCallFrame, 0);
            
            // IFC4BC -- Popping the pushed entry to keep pcstack sane
            pcstack.Pop();
            JSLabel::pcGlobalLabel.clabel = pcstack.Head().Val();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
            // JSLabel::pcGlobalLabel.plabel = pcstack.Head().pLabel;
            
            /*
            rc = gettimeofday(&t1,NULL);
            if(rc==0)
            {
                if(strcmp(program->sourceURL().utf8().data(),"")!=0){
                    printf("\n");
                    printf("###################, time taken %ld us\n",(t1.tv_sec - t0.tv_sec)*1000000 + (t1.tv_usec - t0.tv_usec));
                    printf("\n");
                }
                
            }
            else{
                printf("################### 2nd getimeofday faileddddd\n");
            }
            */
            
            // printf("Popped the label %llu from stack with len %d\n",pcstack.Head().Val(), pcSLen);
            /*
            while (pcSLen > 0) {
                printf("There is an entry, which might not be right!\n");
                pcstack.Pop();
            }*/
            //}
            // IFC4BC ------------------------------------------------
        }

        m_reentryDepth--;
    }

    if (Profiler* profiler = callFrame->globalData().enabledProfiler())
        profiler->didExecute(callFrame, program->sourceURL(), program->lineNo());

    m_registerFile.shrink(oldEnd);

    return checkedReturn(result);
}

JSValue Interpreter::executeCall(CallFrame* callFrame, JSObject* function, CallType callType, const CallData& callData, JSValue thisValue, const ArgList& args)
{
    ASSERT(isValidThisObject(thisValue, callFrame));
    ASSERT(!callFrame->hadException());
    ASSERT(!callFrame->globalData().isCollectorBusy());
    if (callFrame->globalData().isCollectorBusy())
        return jsNull();

    if (m_reentryDepth >= MaxSmallThreadReentryDepth && m_reentryDepth >= callFrame->globalData().maxReentryDepth)
        return checkedReturn(throwStackOverflowError(callFrame));

    Register* oldEnd = m_registerFile.end();
    ASSERT(callFrame->frameExtent() <= oldEnd || callFrame == callFrame->scopeChain()->globalObject->globalExec());
    int argCount = 1 + args.size(); // implicit "this" parameter
    size_t registerOffset = argCount + RegisterFile::CallFrameHeaderSize;

    CallFrame* newCallFrame = CallFrame::create(oldEnd + registerOffset);
    if (!m_registerFile.grow(newCallFrame->registers()))
        return checkedReturn(throwStackOverflowError(callFrame));

    newCallFrame->setThisValue(thisValue);
    for (size_t i = 0; i < args.size(); ++i)
        newCallFrame->setArgument(i, args.at(i));

    if (callType == CallTypeJS) {
        ScopeChainNode* callDataScopeChain = callData.js.scopeChain;

        DynamicGlobalObjectScope globalObjectScope(*callDataScopeChain->globalData, callDataScopeChain->globalObject.get());

        JSObject* compileError = callData.js.functionExecutable->compileForCall(callFrame, callDataScopeChain);
        if (UNLIKELY(!!compileError)) {
            m_registerFile.shrink(oldEnd);
            return checkedReturn(throwError(callFrame, compileError));
        }

        CodeBlock* newCodeBlock = &callData.js.functionExecutable->generatedBytecodeForCall();
        newCallFrame = slideRegisterWindowForCall(newCodeBlock, &m_registerFile, newCallFrame, 0, argCount);
        if (UNLIKELY(!newCallFrame)) {
            m_registerFile.shrink(oldEnd);
            return checkedReturn(throwStackOverflowError(callFrame));
        }

        newCallFrame->init(newCodeBlock, 0, callDataScopeChain, callFrame->addHostCallFrameFlag(), argCount, function);

        TopCallFrameSetter topCallFrame(callFrame->globalData(), newCallFrame);
        
        // IFC4BC -
//        if(strstr(callData.js.functionExecutable->sourceURL().utf8().data(), ".policy")) {
//            if(strcmp(strstr(callData.js.functionExecutable->sourceURL().utf8().data(), ".policy"),".policy")==0) {
//                URLMap::urlmap().put(callData.js.functionExecutable->sourceURL().utf8().data(), true);
//            }
//            else {
//                URLMap::urlmap().put(callData.js.functionExecutable->sourceURL().utf8().data(), false);
//            }
//        }
//        else {
//            URLMap::urlmap().put(callData.js.functionExecutable->sourceURL().utf8().data(), false);
//        }
        //printf("Handler Label========%llu\n", JSLabel::eventNodeLabel);
        //----------------------

        if (Profiler* profiler = callFrame->globalData().enabledProfiler())
            profiler->willExecute(callFrame, function);

        JSValue result;
        {
            SamplingTool::CallRecord callRecord(m_sampler.get());

            m_reentryDepth++;  
#if ENABLE(JIT)
            if (!classicEnabled())
                result = callData.js.functionExecutable->generatedJITCodeForCall().execute(&m_registerFile, newCallFrame, callDataScopeChain->globalData);
            else
#endif
            {
                // IFC4BC -- Setting the current pc to the source being executed
    
                //char *temp1 = strstr(sURl, ".policy");
                JSLabel srcLabel = JSLabel();
                
                //if(temp1) srcLabel = JSLabel(URLMap::urlmap().getLabel(sURl, 1));
                
                // IFC4BC - There might be internal functions called that are probably (default). Do not check the NSU checks then
                const char* funcurl = callData.js.functionExecutable->sourceURL().utf8().data();
                JSLabel funcLabel = JSLabel(URLMap::urlmap().getLabel(funcurl));
                // newCallFrame->codeBlock()->contextLabel = funcLabel;
                /*
                struct timeval t0,t1;
                int rc;
                rc = gettimeofday(&t0,NULL);
                if(rc==0){
                    
                }
                else{
                    printf("################### getimeofday faileddddd\n");
                }
                 */
                // printf("URL: %s\n", callData.js.functionExecutable->sourceURL().utf8().data());
                // printf("%llu\n", funcLabel.Val());
                // Should check if handler is from the same function as the element on which it is defined
                // eventNodeLabel should be equal to srclabel to indicate that the handler is defined in the same function
                /*
                if (!srcLabel.NSU(JSLabel(JSLabel::eventNodeLabel)) && JSLabel::eventNodeLabel != 0) {
                    printf("Aborting as the handler was called on a node from different source\n");
                    result = jsUndefined();
                }
                 */
                // else {
                // Checking if integrity is 0, give the srcLabel. Need to change this to return the highest integrity label -- all bits set to 1
                // IFC4BC - 18446744073709551615 is the highest integrity, I suppose
                // srcLabel = srcLabel.Join(JSLabel(JSLabel::eventNodeLabel.clabel, JSLabel::eventNodeLabel.ilabel));
                // printf("Pushed label %llu on the stack with len %d\n",srcLabel.Val(), pcSLen);
                // IFC4BC ------------------------------------------------------
                if (strcmp("", callData.js.functionExecutable->sourceURL().utf8().data()) == 0 &&
                    JSLabel::eventNodeLabel.clabel == 0) {
                    pcstack.Push(JSLabel(), -1, newCallFrame->registers());
                    JSLabel::pcGlobalLabel.clabel = 0;
                    JSLabel::BRANCH_FLAG = pcstack.branchFlag();
                    // JSLabel::pcGlobalLabel.plabel = 0;
                    result = privateExecute(Normal, &m_registerFile, newCallFrame, 1);
                }
                else if (funcLabel.Val() == 1) {
                    pcstack.Push(funcLabel, -1, newCallFrame->registers());
                    JSLabel::pcGlobalLabel.clabel = pcstack.Head().Val();
                    JSLabel::BRANCH_FLAG = pcstack.branchFlag();
                    // JSLabel::pcGlobalLabel.plabel = pcstack.Head().pLabel;
                    result = privateExecute(Normal, &m_registerFile, newCallFrame, 1);
                }
                else {
                    /*
                    if (funcLabel.Val() == function->getObjectLabel().iVal())
                    {
                        // Set the function's confidentiality label to function-object's label
                        funcLabel.setVal(function->getObjectLabel().Val());
                    }
                    else if (function->getObjectLabel().iVal() == 0 || function->getObjectLabel().iVal() == 0xffffffffffffffff)
                    {   // the function object label is not yet set so set it here
                        funcLabel.setVal(0);
                        function->setObjectLabel(funcLabel);
                    }
                     */
                    // funcLabel.setVal(0); // Set the function's confidentiality label to 0
                    if (JSLabel::eventNodeLabel.clabel == 2) {
                        srcLabel = JSLabel(JSLabel::eventNodeLabel);
                    }
                    else if (JSLabel::eventNodeLabel.clabel == 0){
                        srcLabel = JSLabel();
                    }
                    else { // Join the function label with the context label in which to run
                        srcLabel = JSLabel(JSLabel::eventNodeLabel);
                        srcLabel = srcLabel.Join(funcLabel);
                    }
                    // printf("Event node label is %llu and srcLabel is %llu\n", JSLabel::eventNodeLabel.clabel, srcLabel.Val());
                    pcstack.Push(srcLabel, -1, newCallFrame->registers());
                    JSLabel::pcGlobalLabel.clabel = pcstack.Head().Val();
                    JSLabel::BRANCH_FLAG = pcstack.branchFlag();
                    // JSLabel::pcGlobalLabel.plabel = pcstack.Head().pLabel;
                    result = privateExecute(Normal, &m_registerFile, newCallFrame, 0);
                }
                
                // result = privateExecute(Normal, &m_registerFile, newCallFrame, 0);
                /*
                rc = gettimeofday(&t1,NULL);
                if(rc==0)
                {
                    if(strcmp(callData.js.functionExecutable->sourceURL().utf8().data(),"")!=0){
                        printf("\n");
                        printf("$$$$$$$$$$, time taken for eventhandler %ld us\n",(t1.tv_sec - t0.tv_sec)*1000000 + (t1.tv_usec - t0.tv_usec));
                        printf("\n");
                    }
                    
                }
                else{
                    printf("################### 2nd getimeofday faileddddd\n");
                }
                */
                // IFC4BC -- Popping the pushed entry to keep pcstack sane
                pcstack.Pop();
                JSLabel::pcGlobalLabel.clabel = pcstack.Head().Val();
                JSLabel::BRANCH_FLAG = pcstack.branchFlag();
                // JSLabel::pcGlobalLabel.plabel = pcstack.Head().pLabel;
                // printf("Popped the label %llu from stack with len %d\n",pcstack.Head().Val(), pcSLen);
                // IFC4BC ------------------------------------------------
                // }
            }
            // Original
            // result = privateExecute(Normal, &m_registerFile, newCallFrame);

            m_reentryDepth--;
        }

        if (Profiler* profiler = callFrame->globalData().enabledProfiler())
            profiler->didExecute(callFrame, function);

        m_registerFile.shrink(oldEnd);
        return checkedReturn(result);
    }

    ASSERT(callType == CallTypeHost);
    ScopeChainNode* scopeChain = callFrame->scopeChain();
    newCallFrame->init(0, 0, scopeChain, callFrame->addHostCallFrameFlag(), argCount, function);

    TopCallFrameSetter topCallFrame(callFrame->globalData(), newCallFrame);

    DynamicGlobalObjectScope globalObjectScope(*scopeChain->globalData, scopeChain->globalObject.get());

    if (Profiler* profiler = callFrame->globalData().enabledProfiler())
        profiler->willExecute(callFrame, function);

    JSValue result;
    {
        SamplingTool::HostCallRecord callRecord(m_sampler.get());
        result = (callData.native.function(newCallFrame));
    }

    if (Profiler* profiler = callFrame->globalData().enabledProfiler())
        profiler->didExecute(callFrame, function);

    m_registerFile.shrink(oldEnd);
    return checkedReturn(result);
}

JSObject* Interpreter::executeConstruct(CallFrame* callFrame, JSObject* constructor, ConstructType constructType, const ConstructData& constructData, const ArgList& args)
{
    ASSERT(!callFrame->hadException());
    ASSERT(!callFrame->globalData().isCollectorBusy());
    // We throw in this case because we have to return something "valid" but we're
    // already in an invalid state.
    if (callFrame->globalData().isCollectorBusy())
        return checkedReturn(throwStackOverflowError(callFrame));

    if (m_reentryDepth >= MaxSmallThreadReentryDepth && m_reentryDepth >= callFrame->globalData().maxReentryDepth)
        return checkedReturn(throwStackOverflowError(callFrame));

    Register* oldEnd = m_registerFile.end();
    int argCount = 1 + args.size(); // implicit "this" parameter
    size_t registerOffset = argCount + RegisterFile::CallFrameHeaderSize;

    if (!m_registerFile.grow(oldEnd + registerOffset))
        return checkedReturn(throwStackOverflowError(callFrame));

    CallFrame* newCallFrame = CallFrame::create(oldEnd + registerOffset);
    newCallFrame->setThisValue(jsUndefined());
    for (size_t i = 0; i < args.size(); ++i)
        newCallFrame->setArgument(i, args.at(i));

    if (constructType == ConstructTypeJS) {
        ScopeChainNode* constructDataScopeChain = constructData.js.scopeChain;

        DynamicGlobalObjectScope globalObjectScope(*constructDataScopeChain->globalData, constructDataScopeChain->globalObject.get());

        JSObject* compileError = constructData.js.functionExecutable->compileForConstruct(callFrame, constructDataScopeChain);
        if (UNLIKELY(!!compileError)) {
            m_registerFile.shrink(oldEnd);
            return checkedReturn(throwError(callFrame, compileError));
        }

        CodeBlock* newCodeBlock = &constructData.js.functionExecutable->generatedBytecodeForConstruct();
        newCallFrame = slideRegisterWindowForCall(newCodeBlock, &m_registerFile, newCallFrame, 0, argCount);
        if (UNLIKELY(!newCallFrame)) {
            m_registerFile.shrink(oldEnd);
            return checkedReturn(throwStackOverflowError(callFrame));
        }

        newCallFrame->init(newCodeBlock, 0, constructDataScopeChain, callFrame->addHostCallFrameFlag(), argCount, constructor);

        TopCallFrameSetter topCallFrame(callFrame->globalData(), newCallFrame);

        if (Profiler* profiler = callFrame->globalData().enabledProfiler())
            profiler->willExecute(callFrame, constructor);

        JSValue result;
        {
            SamplingTool::CallRecord callRecord(m_sampler.get());

            m_reentryDepth++;  
#if ENABLE(JIT)
            if (!classicEnabled())
                result = constructData.js.functionExecutable->generatedJITCodeForConstruct().execute(&m_registerFile, newCallFrame, constructDataScopeChain->globalData);
            else
#endif
            result = privateExecute(Normal, &m_registerFile, newCallFrame, 1);

            m_reentryDepth--;
        }

        if (Profiler* profiler = callFrame->globalData().enabledProfiler())
            profiler->didExecute(callFrame, constructor);

        m_registerFile.shrink(oldEnd);
        if (callFrame->hadException())
            return 0;
        ASSERT(result.isObject());
        return checkedReturn(asObject(result));
    }

    ASSERT(constructType == ConstructTypeHost);
    ScopeChainNode* scopeChain = callFrame->scopeChain();
    newCallFrame->init(0, 0, scopeChain, callFrame->addHostCallFrameFlag(), argCount, constructor);

    TopCallFrameSetter topCallFrame(callFrame->globalData(), newCallFrame);

    DynamicGlobalObjectScope globalObjectScope(*scopeChain->globalData, scopeChain->globalObject.get());

    if (Profiler* profiler = callFrame->globalData().enabledProfiler())
        profiler->willExecute(callFrame, constructor);

    JSValue result;
    {
        SamplingTool::HostCallRecord callRecord(m_sampler.get());
        result = (constructData.native.function(newCallFrame));
    }

    if (Profiler* profiler = callFrame->globalData().enabledProfiler())
        profiler->didExecute(callFrame, constructor);

    m_registerFile.shrink(oldEnd);
    if (callFrame->hadException())
        return 0;
    ASSERT(result.isObject());
    return checkedReturn(asObject(result));
}

CallFrameClosure Interpreter::prepareForRepeatCall(FunctionExecutable* functionExecutable, CallFrame* callFrame, JSFunction* function, int argumentCountIncludingThis, ScopeChainNode* scopeChain)
{
    ASSERT(!scopeChain->globalData->exception);
    
    if (callFrame->globalData().isCollectorBusy())
        return CallFrameClosure();

    if (m_reentryDepth >= MaxSmallThreadReentryDepth && m_reentryDepth >= callFrame->globalData().maxReentryDepth) {
        throwStackOverflowError(callFrame);
        return CallFrameClosure();
    }

    Register* oldEnd = m_registerFile.end();
    size_t registerOffset = argumentCountIncludingThis + RegisterFile::CallFrameHeaderSize;

    CallFrame* newCallFrame = CallFrame::create(oldEnd + registerOffset);
    if (!m_registerFile.grow(newCallFrame->registers())) {
        throwStackOverflowError(callFrame);
        return CallFrameClosure();
    }

    JSObject* error = functionExecutable->compileForCall(callFrame, scopeChain);
    if (error) {
        throwError(callFrame, error);
        m_registerFile.shrink(oldEnd);
        return CallFrameClosure();
    }
    CodeBlock* codeBlock = &functionExecutable->generatedBytecodeForCall();

    newCallFrame = slideRegisterWindowForCall(codeBlock, &m_registerFile, newCallFrame, 0, argumentCountIncludingThis);
    if (UNLIKELY(!newCallFrame)) {
        throwStackOverflowError(callFrame);
        m_registerFile.shrink(oldEnd);
        return CallFrameClosure();
    }
    newCallFrame->init(codeBlock, 0, scopeChain, callFrame->addHostCallFrameFlag(), argumentCountIncludingThis, function);  
    scopeChain->globalData->topCallFrame = newCallFrame;
    CallFrameClosure result = { callFrame, newCallFrame, function, functionExecutable, scopeChain->globalData, oldEnd, scopeChain, codeBlock->numParameters(), argumentCountIncludingThis };
    return result;
}

JSValue Interpreter::execute(CallFrameClosure& closure) 
{
    ASSERT(!closure.oldCallFrame->globalData().isCollectorBusy());
    if (closure.oldCallFrame->globalData().isCollectorBusy())
        return jsNull();
    closure.resetCallFrame();
    if (Profiler* profiler = closure.oldCallFrame->globalData().enabledProfiler())
        profiler->willExecute(closure.oldCallFrame, closure.function);

    TopCallFrameSetter topCallFrame(*closure.globalData, closure.newCallFrame);

    JSValue result;
    {
        SamplingTool::CallRecord callRecord(m_sampler.get());
        
        m_reentryDepth++;  
#if ENABLE(JIT)
#if ENABLE(CLASSIC_INTERPRETER)
        if (closure.newCallFrame->globalData().canUseJIT())
#endif
            result = closure.functionExecutable->generatedJITCodeForCall().execute(&m_registerFile, closure.newCallFrame, closure.globalData);
#if ENABLE(CLASSIC_INTERPRETER)
        else
#endif
#endif
#if ENABLE(CLASSIC_INTERPRETER)
        result = privateExecute(Normal, &m_registerFile, closure.newCallFrame, 1);
#endif
        m_reentryDepth--;
    }

    if (Profiler* profiler = closure.oldCallFrame->globalData().enabledProfiler())
        profiler->didExecute(closure.oldCallFrame, closure.function);
    return checkedReturn(result);
}

void Interpreter::endRepeatCall(CallFrameClosure& closure)
{
    closure.globalData->topCallFrame = closure.oldCallFrame;
    m_registerFile.shrink(closure.oldEnd);
}

JSValue Interpreter::execute(EvalExecutable* eval, CallFrame* callFrame, JSValue thisValue, ScopeChainNode* scopeChain, int globalRegisterOffset)
{
    ASSERT(isValidThisObject(thisValue, callFrame));
    ASSERT(!scopeChain->globalData->exception);
    ASSERT(!callFrame->globalData().isCollectorBusy());
    if (callFrame->globalData().isCollectorBusy())
        return jsNull();

    DynamicGlobalObjectScope globalObjectScope(*scopeChain->globalData, scopeChain->globalObject.get());

    if (m_reentryDepth >= MaxSmallThreadReentryDepth && m_reentryDepth >= callFrame->globalData().maxReentryDepth)
        return checkedReturn(throwStackOverflowError(callFrame));

    JSObject* compileError = eval->compile(callFrame, scopeChain);
    if (UNLIKELY(!!compileError))
        return checkedReturn(throwError(callFrame, compileError));
    EvalCodeBlock* codeBlock = &eval->generatedBytecode();

    JSObject* variableObject;
    for (ScopeChainNode* node = scopeChain; ; node = node->next.get()) {
        ASSERT(node);
        if (node->object->isVariableObject() && !node->object->isStaticScopeObject()) {
            variableObject = jsCast<JSSymbolTableObject*>(node->object.get());
            break;
        }
    }

    unsigned numVariables = codeBlock->numVariables();
    int numFunctions = codeBlock->numberOfFunctionDecls();
    bool pushedScope = false;
    if (numVariables || numFunctions) {
        if (codeBlock->isStrictMode()) {
            variableObject = StrictEvalActivation::create(callFrame);
            scopeChain = scopeChain->push(variableObject);
            pushedScope = true;
        }
        // Scope for BatchedTransitionOptimizer
        BatchedTransitionOptimizer optimizer(callFrame->globalData(), variableObject);

        for (unsigned i = 0; i < numVariables; ++i) {
            const Identifier& ident = codeBlock->variable(i);
            if (!variableObject->hasProperty(callFrame, ident)) {
                PutPropertySlot slot;
                variableObject->methodTable()->put(variableObject, callFrame, ident, jsUndefined(), slot);
            }
        }

        for (int i = 0; i < numFunctions; ++i) {
            FunctionExecutable* function = codeBlock->functionDecl(i);
            PutPropertySlot slot;
            variableObject->methodTable()->put(variableObject, callFrame, function->name(), function->make(callFrame, scopeChain), slot);
        }
    }

    Register* oldEnd = m_registerFile.end();
    Register* newEnd = m_registerFile.begin() + globalRegisterOffset + codeBlock->m_numCalleeRegisters;
    if (!m_registerFile.grow(newEnd)) {
        if (pushedScope)
            scopeChain->pop();
        return checkedReturn(throwStackOverflowError(callFrame));
    }

    CallFrame* newCallFrame = CallFrame::create(m_registerFile.begin() + globalRegisterOffset);

    ASSERT(codeBlock->numParameters() == 1); // 1 parameter for 'this'.
    newCallFrame->init(codeBlock, 0, scopeChain, callFrame->addHostCallFrameFlag(), codeBlock->numParameters(), 0);
    newCallFrame->setThisValue(thisValue);

    TopCallFrameSetter topCallFrame(callFrame->globalData(), newCallFrame);

    if (Profiler* profiler = callFrame->globalData().enabledProfiler())
        profiler->willExecute(callFrame, eval->sourceURL(), eval->lineNo());

    JSValue result;
    {
        SamplingTool::CallRecord callRecord(m_sampler.get());

        m_reentryDepth++;
        
#if ENABLE(JIT)
#if ENABLE(CLASSIC_INTERPRETER)
        if (callFrame->globalData().canUseJIT())
#endif
            result = eval->generatedJITCode().execute(&m_registerFile, newCallFrame, scopeChain->globalData);
#if ENABLE(CLASSIC_INTERPRETER)
        else
#endif
#endif
#if ENABLE(CLASSIC_INTERPRETER)
            
        // IFC4BC - handle eval
        JSLabel srcLabel = JSLabel();
        // printf("URL : %s\n", eval->sourceURL().  utf8().data());
        const char* funcurl = eval->sourceURL().utf8().data();
        JSLabel funcLabel = JSLabel(URLMap::urlmap().getLabel(funcurl));
        /*
         if (eval->source().provider()->data()->is8Bit())
            printf("URL : %s\n", eval->source().provider()->data()->characters8());
        else
            printf("URL : %s\n", (char*)eval->source().provider()->data()->characters16());
        */
        if (strcmp("", funcurl) == 0 &&
            JSLabel::eventNodeLabel.clabel == 0) {
            pcstack.Push(JSLabel(), -1, newCallFrame->registers());
            JSLabel::pcGlobalLabel.clabel = 0;
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
            // JSLabel::pcGlobalLabel.plabel = 0;
            result = privateExecute(Normal, &m_registerFile, newCallFrame, 1);
        }
        else if (funcLabel.Val() == 1) {
            pcstack.Push(funcLabel, -1, newCallFrame->registers());
            JSLabel::pcGlobalLabel.clabel = pcstack.Head().Val();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
            // JSLabel::pcGlobalLabel.plabel = pcstack.Head().pLabel;
            result = privateExecute(Normal, &m_registerFile, newCallFrame, 1);
        }
        else {
            if (JSLabel::eventNodeLabel.clabel == 2) {
                srcLabel = JSLabel(JSLabel::eventNodeLabel);
            }
            else if (JSLabel::eventNodeLabel.clabel == 0){
                srcLabel = JSLabel();
            }
            else { // Join the function label with the context label in which to run
                srcLabel = JSLabel(JSLabel::eventNodeLabel);
                srcLabel = srcLabel.Join(funcLabel);
            }
            pcstack.Push(srcLabel, -1, newCallFrame->registers());
            JSLabel::pcGlobalLabel.clabel = pcstack.Head().Val();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
            // JSLabel::pcGlobalLabel.plabel = pcstack.Head().pLabel;
            result = privateExecute(Normal, &m_registerFile, newCallFrame, 0);
        }
        // IFC4BC -- Popping the pushed entry to keep pcstack sane
        pcstack.Pop();
        JSLabel::pcGlobalLabel.clabel = pcstack.Head().Val();
        JSLabel::BRANCH_FLAG = pcstack.branchFlag();
        // JSLabel::pcGlobalLabel.plabel = pcstack.Head().pLabel;


        //original
        // result = privateExecute(Normal, &m_registerFile, newCallFrame, 0);

#endif
        m_reentryDepth--;
    }

    if (Profiler* profiler = callFrame->globalData().enabledProfiler())
        profiler->didExecute(callFrame, eval->sourceURL(), eval->lineNo());

    m_registerFile.shrink(oldEnd);
    if (pushedScope)
        scopeChain->pop();
    return checkedReturn(result);
}

NEVER_INLINE void Interpreter::debug(CallFrame* callFrame, DebugHookID debugHookID, int firstLine, int lastLine)
{
    Debugger* debugger = callFrame->dynamicGlobalObject()->debugger();
    if (!debugger)
        return;

    switch (debugHookID) {
        case DidEnterCallFrame:
            debugger->callEvent(callFrame, callFrame->codeBlock()->ownerExecutable()->sourceID(), firstLine);
            return;
        case WillLeaveCallFrame:
            debugger->returnEvent(callFrame, callFrame->codeBlock()->ownerExecutable()->sourceID(), lastLine);
            return;
        case WillExecuteStatement:
            debugger->atStatement(callFrame, callFrame->codeBlock()->ownerExecutable()->sourceID(), firstLine);
            return;
        case WillExecuteProgram:
            debugger->willExecuteProgram(callFrame, callFrame->codeBlock()->ownerExecutable()->sourceID(), firstLine);
            return;
        case DidExecuteProgram:
            debugger->didExecuteProgram(callFrame, callFrame->codeBlock()->ownerExecutable()->sourceID(), lastLine);
            return;
        case DidReachBreakpoint:
            debugger->didReachBreakpoint(callFrame, callFrame->codeBlock()->ownerExecutable()->sourceID(), lastLine);
            return;
    }
}
    
#if ENABLE(CLASSIC_INTERPRETER)
NEVER_INLINE ScopeChainNode* Interpreter::createExceptionScope(CallFrame* callFrame, const Instruction* vPC)
{
    int dst = vPC[1].u.operand;
    CodeBlock* codeBlock = callFrame->codeBlock();
    Identifier& property = codeBlock->identifier(vPC[2].u.operand);
    JSValue value = callFrame->r(vPC[3].u.operand).jsValue();
    JSObject* scope = JSStaticScopeObject::create(callFrame, property, value, DontDelete);
    callFrame->uncheckedR(dst) = JSValue(scope);

    return callFrame->scopeChain()->push(scope);
}

NEVER_INLINE void Interpreter::tryCachePutByID(CallFrame* callFrame, CodeBlock* codeBlock, Instruction* vPC, JSValue baseValue, const PutPropertySlot& slot)
{
    // Recursive invocation may already have specialized this instruction.
    if (vPC[0].u.opcode != getOpcode(op_put_by_id))
        return;

    if (!baseValue.isCell())
        return;

    // Uncacheable: give up.
    if (!slot.isCacheable()) {
        vPC[0] = getOpcode(op_put_by_id_generic);
        return;
    }
    
    JSCell* baseCell = baseValue.asCell();
    Structure* structure = baseCell->structure();

    if (structure->isUncacheableDictionary() || structure->typeInfo().prohibitsPropertyCaching()) {
        vPC[0] = getOpcode(op_put_by_id_generic);
        return;
    }

    // Cache miss: record Structure to compare against next time.
    Structure* lastStructure = vPC[4].u.structure.get();
    if (structure != lastStructure) {
        // First miss: record Structure to compare against next time.
        if (!lastStructure) {
            vPC[4].u.structure.set(callFrame->globalData(), codeBlock->ownerExecutable(), structure);
            return;
        }

        // Second miss: give up.
        vPC[0] = getOpcode(op_put_by_id_generic);
        return;
    }

    // Cache hit: Specialize instruction and ref Structures.

    // If baseCell != slot.base(), then baseCell must be a proxy for another object.
    if (baseCell != slot.base()) {
        vPC[0] = getOpcode(op_put_by_id_generic);
        return;
    }

    // Structure transition, cache transition info
    if (slot.type() == PutPropertySlot::NewProperty) {
        if (structure->isDictionary()) {
            vPC[0] = getOpcode(op_put_by_id_generic);
            return;
        }

        // put_by_id_transition checks the prototype chain for setters.
        normalizePrototypeChain(callFrame, baseCell);
        JSCell* owner = codeBlock->ownerExecutable();
        JSGlobalData& globalData = callFrame->globalData();
        // Get the prototype here because the call to prototypeChain could cause a 
        // GC allocation, which we don't want to happen while we're in the middle of 
        // initializing the union.
        StructureChain* prototypeChain = structure->prototypeChain(callFrame);
        vPC[0] = getOpcode(op_put_by_id_transition);
        vPC[4].u.structure.set(globalData, owner, structure->previousID());
        vPC[5].u.structure.set(globalData, owner, structure);
        vPC[6].u.structureChain.set(callFrame->globalData(), codeBlock->ownerExecutable(), prototypeChain);
        ASSERT(vPC[6].u.structureChain);
        vPC[7] = slot.cachedOffset();
        return;
    }

    vPC[0] = getOpcode(op_put_by_id_replace);
    vPC[5] = slot.cachedOffset();
}

NEVER_INLINE void Interpreter::uncachePutByID(CodeBlock*, Instruction* vPC)
{
    vPC[0] = getOpcode(op_put_by_id);
    vPC[4] = 0;
}

NEVER_INLINE void Interpreter::tryCacheGetByID(CallFrame* callFrame, CodeBlock* codeBlock, Instruction* vPC, JSValue baseValue, const Identifier& propertyName, const PropertySlot& slot)
{
    // Recursive invocation may already have specialized this instruction.
    if (vPC[0].u.opcode != getOpcode(op_get_by_id))
        return;

    // FIXME: Cache property access for immediates.
    if (!baseValue.isCell()) {
        vPC[0] = getOpcode(op_get_by_id_generic);
        return;
    }

    if (isJSArray(baseValue) && propertyName == callFrame->propertyNames().length) {
        vPC[0] = getOpcode(op_get_array_length);
        return;
    }

    if (isJSString(baseValue) && propertyName == callFrame->propertyNames().length) {
        vPC[0] = getOpcode(op_get_string_length);
        return;
    }

    // Uncacheable: give up.
    if (!slot.isCacheable()) {
        vPC[0] = getOpcode(op_get_by_id_generic);
        return;
    }

    Structure* structure = baseValue.asCell()->structure();

    if (structure->isUncacheableDictionary() || structure->typeInfo().prohibitsPropertyCaching()) {
        vPC[0] = getOpcode(op_get_by_id_generic);
        return;
    }

    // Cache miss
    Structure* lastStructure = vPC[4].u.structure.get();
    if (structure != lastStructure) {
        // First miss: record Structure to compare against next time.
        if (!lastStructure) {
            vPC[4].u.structure.set(callFrame->globalData(), codeBlock->ownerExecutable(), structure);
            return;
        }

        // Second miss: give up.
        vPC[0] = getOpcode(op_get_by_id_generic);
        return;
    }

    // Cache hit: Specialize instruction and ref Structures.

    if (slot.slotBase() == baseValue) {
        switch (slot.cachedPropertyType()) {
        case PropertySlot::Getter:
            vPC[0] = getOpcode(op_get_by_id_getter_self);
            vPC[5] = slot.cachedOffset();
            break;
        case PropertySlot::Custom:
            vPC[0] = getOpcode(op_get_by_id_custom_self);
            vPC[5] = slot.customGetter();
            break;
        default:
            vPC[0] = getOpcode(op_get_by_id_self);
            vPC[5] = slot.cachedOffset();
            break;
        }
        return;
    }

    if (structure->isDictionary()) {
        vPC[0] = getOpcode(op_get_by_id_generic);
        return;
    }

    if (slot.slotBase() == structure->prototypeForLookup(callFrame)) {
        ASSERT(slot.slotBase().isObject());

        JSObject* baseObject = asObject(slot.slotBase());
        PropertyOffset offset = slot.cachedOffset();

        // Since we're accessing a prototype in a loop, it's a good bet that it
        // should not be treated as a dictionary.
        if (baseObject->structure()->isDictionary()) {
            baseObject->flattenDictionaryObject(callFrame->globalData());
            offset = baseObject->structure()->get(callFrame->globalData(), propertyName);
        }

        ASSERT(!baseObject->structure()->isUncacheableDictionary());
        
        switch (slot.cachedPropertyType()) {
        case PropertySlot::Getter:
            vPC[0] = getOpcode(op_get_by_id_getter_proto);
            vPC[6] = offset;
            break;
        case PropertySlot::Custom:
            vPC[0] = getOpcode(op_get_by_id_custom_proto);
            vPC[6] = slot.customGetter();
            break;
        default:
            vPC[0] = getOpcode(op_get_by_id_proto);
            vPC[6] = offset;
            break;
        }
        vPC[5].u.structure.set(callFrame->globalData(), codeBlock->ownerExecutable(), baseObject->structure());
        return;
    }

    PropertyOffset offset = slot.cachedOffset();
    size_t count = normalizePrototypeChain(callFrame, baseValue, slot.slotBase(), propertyName, offset);
    if (!count) {
        vPC[0] = getOpcode(op_get_by_id_generic);
        return;
    }

    
    StructureChain* prototypeChain = structure->prototypeChain(callFrame);
    switch (slot.cachedPropertyType()) {
    case PropertySlot::Getter:
        vPC[0] = getOpcode(op_get_by_id_getter_chain);
        vPC[7] = offset;
        break;
    case PropertySlot::Custom:
        vPC[0] = getOpcode(op_get_by_id_custom_chain);
        vPC[7] = slot.customGetter();
        break;
    default:
        vPC[0] = getOpcode(op_get_by_id_chain);
        vPC[7] = offset;
        break;
    }
    vPC[4].u.structure.set(callFrame->globalData(), codeBlock->ownerExecutable(), structure);
    vPC[5].u.structureChain.set(callFrame->globalData(), codeBlock->ownerExecutable(), prototypeChain);
    vPC[6] = count;
}

NEVER_INLINE void Interpreter::uncacheGetByID(CodeBlock*, Instruction* vPC)
{
    vPC[0] = getOpcode(op_get_by_id);
    vPC[4] = 0;
}

#endif // ENABLE(CLASSIC_INTERPRETER)

void Interpreter::labelRegisters(CallFrame* callFrame, CodeBlock* codeBlock, JSLabel pcLabel)
{
    for (int i = 0; i < codeBlock->m_numCalleeRegisters; i++) {
        callFrame->uncheckedR(i).setRegLabel(pcLabel);
    }
    for(int i = -7, j = 1; j <= codeBlock->numParameters(); j++, i--)
    {
        callFrame->uncheckedR(i).setRegLabel(pcLabel);
    }
}

void Interpreter::labelRegistersMinusDst(CallFrame* callFrame, CodeBlock* codeBlock, JSLabel pcLabel, int dst)
{
    for (int i = 0; i < codeBlock->m_numCalleeRegisters; i++) {
        if (i != dst) {
            callFrame->uncheckedR(i).setRegLabel(pcLabel);
        }
    }
    for(int i = -7, j = 1; j <= codeBlock->numParameters(); j++, i--)
    {
        callFrame->uncheckedR(i).setRegLabel(pcLabel);
    }
}

JSValue Interpreter::privateExecute(ExecutionFlag flag, RegisterFile* registerFile, CallFrame* callFrame, bool isPolicy)
{
    // One-time initialization of our address tables. We have to put this code
    // here because our labels are only in scope inside this function.
    if (UNLIKELY(flag == InitializeAndReturn)) {
        #if ENABLE(COMPUTED_GOTO_CLASSIC_INTERPRETER)
            #define LIST_OPCODE_LABEL(id, length) &&id,
                static Opcode labels[] = { FOR_EACH_OPCODE_ID(LIST_OPCODE_LABEL) };
                for (size_t i = 0; i < WTF_ARRAY_LENGTH(labels); ++i)
                    m_opcodeTable[i] = labels[i];
            #undef LIST_OPCODE_LABEL
        #endif // ENABLE(COMPUTED_GOTO_CLASSIC_INTERPRETER)
        return JSValue();
    }
    
    ASSERT(m_initialized);
    ASSERT(m_classicEnabled);
    
#if ENABLE(JIT)
#if ENABLE(CLASSIC_INTERPRETER)
    // Mixing Interpreter + JIT is not supported.
    if (callFrame->globalData().canUseJIT())
#endif
        ASSERT_NOT_REACHED();
#endif

#if !ENABLE(CLASSIC_INTERPRETER)
    UNUSED_PARAM(registerFile);
    UNUSED_PARAM(callFrame);
    return JSValue();
#else

    ASSERT(callFrame->globalData().topCallFrame == callFrame);

    JSGlobalData* globalData = &callFrame->globalData();
    JSValue exceptionValue;
    HandlerInfo* handler = 0;
    CallFrame** topCallFrameSlot = &globalData->topCallFrame;

    CodeBlock* codeBlock = callFrame->codeBlock();
    Instruction* vPC = codeBlock->instructions().begin();
    Instruction* iBegin = codeBlock->instructions().begin();
    unsigned tickCount = globalData->timeoutChecker.ticksUntilNextCheck();
    JSValue functionReturnValue;

    // IFC4BC - Perform static analysis
    // Create CFG and calculate IPD
    if (pcstack.excHandler()) {
        // SEN exists
        if (!codeBlock->has_SENanalysis) {
            codeBlock->analyzerSEN.genContextTable(codeBlock, this, pcstack.excHandler());
            codeBlock->has_SENanalysis = true;
        }
        codeBlock->analyzer = codeBlock->analyzerSEN;
    }
    else {
        // No exception handler
        if (!codeBlock->has_analysis) {
            codeBlock->analyzerNOR.genContextTable(codeBlock, this, pcstack.excHandler());
            codeBlock->has_analysis = true;
        }
        codeBlock->analyzer = codeBlock->analyzerNOR;
    }
    // IFC4BC - Local variables for pc
    JSLabel pcLabel = pcstack.Head();
    int pcIPD = pcstack.Loc();
    int pcSLen = pcstack.Len();
    Register* pcReg = pcstack.Reg();
//    if(!isPolicy)
//        pcLabel = pcstack.Head();
//    else
//        pcLabel = JSLabel(1,1);
    pcLabel.setStar(false);
    JSLabel::pcGlobalLabel = pcLabel.getPair();
    JSLabel::BRANCH_FLAG = pcstack.branchFlag();
    // For sparse labelling
    bool labelReq = false;
    
    // For setting label of global variable in policy
    bool isGlobalVar = false;
    bool isSetLabel = false;
    bool isGlobalRVar = false;
    
    WriteBarrier<Unknown>* rPointer = 0;
    Identifier vIdent = Identifier(callFrame, "NULL");
    JSValue vValue;
        
    // IFC4BC -------------------------

    // Might have to transfer the label for exception value!!!
#define CHECK_FOR_EXCEPTION(excLabel) \
    do { \
        if (UNLIKELY(globalData->exception != JSValue())) { \
            exceptionValue = globalData->exception; \
            exceptionValue.setValueLabel(excLabel); \
            goto vm_throw; \
        } \
    } while (0)

#if ENABLE(OPCODE_STATS)
    OpcodeStats::resetLastInstruction();
#endif
    

// IFC4BC - Defining functions and performing push/pop for pcstack ------------------------------------------------------------

#define ABORT_CALL() do {\
int POSITION = (int) (vPC - iBegin); \
unsigned bytecodeOffset;\
bool end = false; \
while ( (pcSLen > 0) && !(end = callFrame->callerFrame()->hasHostCallFrameFlag())) { \
vPC = callFrame->returnVPC(); \
unwindCallFrame(callFrame, exceptionValue, bytecodeOffset, codeBlock); \
/*printf("abort while\n");*/\
} \
if (end && (pcSLen > 0)) { \
/*printf("abort end\n");*/\
/*printf("Program Counter Head: %llx\n", pcLabel.Val());*/\
while (pcSLen > 0) {\
pcstack.Pop();\
pcSLen = pcstack.Len();\
}\
pcLabel = pcstack.Head();\
pcIPD = pcstack.Loc();\
pcReg = pcstack.Reg();\
JSLabel::pcGlobalLabel = pcLabel.getPair();\
JSLabel::BRANCH_FLAG = pcstack.branchFlag();\
/*printf("Failed at line number:%d\n", POSITION);*/\
return jsUndefined(); \
} else { \
codeBlock = callFrame->codeBlock(); \
iBegin = codeBlock->instructions().begin();\
functionReturnValue = jsUndefined(); \
/*printf("abort else\n");*/\
NEXT_INSTRUCTION();\
} } while (0)

#define ABORT_TRANSACTION() do {\
int bytecodeOffset = (int) (vPC - iBegin);\
int lineNumber = codeBlock->lineNumberForBytecodeOffset(bytecodeOffset);\
printf("Line %d: IFC Violation at %d in %p!\n", lineNumber, bytecodeOffset, codeBlock);\
}while(0)

// #define ABORT_TRANSACTION() do {\
int bytecodeOffset = (int) (vPC - iBegin);\
int lineNumber = codeBlock->lineNumberForBytecodeOffset(bytecodeOffset);\
printf("Line %d: IFC Violation at %d in %p!\n", lineNumber, bytecodeOffset, codeBlock);\
if (pcstack.branchFlag()) {\
    printf("Possible information leak\n");\
} else {\
    printf("It might not be in a branch\n");\
}\
ABORT_CALL();\
}while(0)
    
//#define ABORT_TRANSACTION() do {}while(0)


//#define ABORT_TRANSACTION() do {\
printf("In abort\n");\
exceptionValue = jsString(callFrame, "Security violation\n"); \
goto vm_throw; \
} while (0)


#if LDEBUG
    
#define OP_BRANCH(op_label) \
int POSITION = (int) (vPC - iBegin); \
int SEN = (int) (codeBlock->instructions().end() - iBegin); \
int IPD = codeBlock->analyzer.IDom(POSITION); \
bool flag = true /*((pcLabel == op_label) ? pcstack.branchFlag() : true)*/;\
if ((pcSLen > 0) && ((IPD == SEN) || ((pcIPD == IPD) && (pcReg == callFrame->registers())))) { \
pcstack.Join(op_label, flag); \
printf("Joining label 0x%" PRIx64 " to PC at location %d with IPD %d\n", op_label.Val(), POSITION, IPD); \
pcLabel = pcstack.Head();\
pcLabel.setStar(false);\
JSLabel::pcGlobalLabel = pcLabel.getPair();\
JSLabel::BRANCH_FLAG = pcstack.branchFlag();\
} else { \
pcstack.Push(op_label, IPD, callFrame->registers(), pcstack.excHandler(), flag); \
printf("Pushing label 0x%" PRIx64 " to PC at location %d with IPD %d and exchandler %d\n", op_label.Val(), POSITION, IPD, pcstack.excHandler()); \
printf("Pushed on the stack with len %d\n",pcSLen);\
pcLabel = pcstack.Head();\
pcIPD = pcstack.Loc();\
pcSLen = pcstack.Len();\
pcReg = pcstack.Reg();\
pcLabel.setStar(false);\
JSLabel::pcGlobalLabel = pcLabel.getPair();\
JSLabel::BRANCH_FLAG = pcstack.branchFlag();\
}
    
#define OP_MERGE() \
if ((pcIPD == (int) (vPC - iBegin)) && (pcReg==callFrame->registers())) { \
pcstack.Pop(); \
printf("Popping label from PC at location %d\n", (int) (vPC - iBegin)); \
printf("Popped from the stack with len %d\n",pcLen);\
pcLabel = pcstack.Head();\
pcIPD = pcstack.Loc();\
pcSLen = pcstack.Len();\
pcReg = pcstack.Reg();\
pcLabel.setStar(false);\
JSLabel::pcGlobalLabel = pcLabel.getPair();\
JSLabel::BRANCH_FLAG = pcstack.branchFlag();\
}
    
    // Added OP_CALLBRANCH for function calls assisting in exception handling.
#define OP_CALLBRANCH(op_label, excHandler, funHandler) \
int POSITION = (int) (vPC - iBegin); \
int SEN = (int) (codeBlock->instructions().end() - iBegin); \
int IPD = codeBlock->analyzer.IDom(POSITION); \
if ((pcSLen > 0) && ((IPD==SEN) || ((pcIPD==IPD) && (pcReg==callFrame->registers())))) { \
pcstack.Join(op_label, excHandler, funHandler); \
printf("Joining label 0x%" PRIx64 " to PC at location %d with IPD %d\n", op_label.Val(), POSITION, IPD); \
pcLabel = pcstack.Head();\
pcLabel.setStar(false);\
JSLabel::pcGlobalLabel = pcLabel.getPair();\
JSLabel::BRANCH_FLAG = pcstack.branchFlag();\
} else { \
pcstack.Push(op_label, IPD, callFrame->registers(), excHandler, funHandler, pcstack.branchFlag()); \
printf("Pushing label 0x%" PRIx64 " to PC at location %d with IPD %d and funhandler %d\n", op_label.Val(), POSITION, IPD, funHandler); \
printf("Pushed on the stack with len %d\n",pcSLen);\
pcLabel = pcstack.Head();\
pcIPD = pcstack.Loc();\
pcSLen = pcstack.Len();\
pcReg = pcstack.Reg();\
pcLabel.setStar(false);\
JSLabel::pcGlobalLabel = pcLabel.getPair();\
JSLabel::BRANCH_FLAG = pcstack.branchFlag();\
}
    
#else // if !LDEBUG
    // the branchflag is set if we are entering a branch when the label differs from the current context
#define OP_BRANCH(op_label) \
int POSITION = (int) (vPC - iBegin); \
int SEN = (int) (codeBlock->instructions().end() - iBegin); \
int IPD = codeBlock->analyzer.IDom(POSITION); \
bool flag = true/*((pcstack.Head() == op_label) ? pcstack.branchFlag() : true)*/;\
if ((pcSLen > 0) && ((IPD==SEN) || ((pcIPD==IPD) && (pcReg==callFrame->registers())))) { \
pcstack.Join(op_label, flag); \
pcLabel = pcstack.Head();\
pcLabel.setStar(false);\
JSLabel::pcGlobalLabel = pcLabel.getPair();\
JSLabel::BRANCH_FLAG = pcstack.branchFlag();\
} else { \
pcstack.Push(op_label, IPD, callFrame->registers(), pcstack.excHandler(), flag); \
pcLabel = pcstack.Head();\
pcIPD = pcstack.Loc();\
pcSLen = pcstack.Len();\
pcReg = pcstack.Reg();\
pcLabel.setStar(false);\
JSLabel::pcGlobalLabel = pcLabel.getPair();\
JSLabel::BRANCH_FLAG = pcstack.branchFlag();\
}
    
#define OP_MERGE() \
if ((pcIPD == (int) (vPC - iBegin)) && (pcstack.Reg()==callFrame->registers())) { \
pcstack.Pop(); \
pcLabel = pcstack.Head();\
pcIPD = pcstack.Loc();\
pcSLen = pcstack.Len();\
pcReg = pcstack.Reg();\
pcLabel.setStar(false);\
JSLabel::pcGlobalLabel = pcLabel.getPair();\
JSLabel::BRANCH_FLAG = pcstack.branchFlag();\
}
    
    //  Added OP_CALLBRANCH for function calls assisting in exception handling.
#define OP_CALLBRANCH(op_label, excHandler, funHandler) \
int POSITION = (int) (vPC - iBegin); \
int SEN = (int) (codeBlock->instructions().end() - iBegin); \
int IPD = codeBlock->analyzer.IDom(POSITION); \
if ((pcSLen > 0) && ((IPD==SEN) || ((pcIPD==IPD) && (pcstack.Reg()==callFrame->registers())))) { \
pcstack.Join(op_label, excHandler, funHandler); \
pcLabel = pcstack.Head();\
pcLabel.setStar(false);\
JSLabel::pcGlobalLabel = pcLabel.getPair();\
JSLabel::BRANCH_FLAG = pcstack.branchFlag();\
} else { \
pcstack.Push(op_label, IPD, callFrame->registers(), excHandler, funHandler, pcstack.branchFlag()); \
pcLabel = pcstack.Head();\
pcIPD = pcstack.Loc();\
pcSLen = pcstack.Len();\
pcReg = pcstack.Reg();\
pcLabel.setStar(false);\
JSLabel::pcGlobalLabel = pcLabel.getPair();\
JSLabel::BRANCH_FLAG = pcstack.branchFlag();\
}
    
#endif // END if LEDBUG

// IFC4BC ---------------------------------------------------------------------------------------------------
    
#define CHECK_FOR_TIMEOUT() \
    if (!--tickCount) { \
        if (globalData->terminator.shouldTerminate() || globalData->timeoutChecker.didTimeOut(callFrame)) { \
            exceptionValue = jsNull(); \
            goto vm_throw; \
        } \
        tickCount = globalData->timeoutChecker.ticksUntilNextCheck(); \
    }
    
#if ENABLE(OPCODE_SAMPLING)
    #define SAMPLE(codeBlock, vPC) m_sampler->sample(codeBlock, vPC)
#else
    #define SAMPLE(codeBlock, vPC)
#endif

#define UPDATE_BYTECODE_OFFSET() \
    do {\
        callFrame->setBytecodeOffsetForNonDFGCode(vPC - codeBlock->instructions().data() + 1);\
    } while (0)

#if ENABLE(COMPUTED_GOTO_CLASSIC_INTERPRETER)
    // IFC4BC - Adding instruction to pop, if IPD is encountered
    #define NEXT_INSTRUCTION() SAMPLE(codeBlock, vPC); OP_MERGE(); goto *vPC->u.opcode
    // Original
    // #define NEXT_INSTRUCTION() SAMPLE(codeBlock, vPC); goto *vPC->u.opcode
#if ENABLE(OPCODE_STATS)
    #define DEFINE_OPCODE(opcode) \
        opcode:\
            OpcodeStats::recordInstruction(opcode);\
            UPDATE_BYTECODE_OFFSET();
#else
    #define DEFINE_OPCODE(opcode) opcode: UPDATE_BYTECODE_OFFSET();
#endif
    NEXT_INSTRUCTION();
#else
    // IFC4BC - Adding instruction to pop, if IPD is encountered
#define NEXT_INSTRUCTION() SAMPLE(codeBlock, vPC); OP_MERGE(); goto interpreterLoopStart
    // Original
    // #define NEXT_INSTRUCTION() SAMPLE(codeBlock, vPC); goto interpreterLoopStart
#if ENABLE(OPCODE_STATS)
    #define DEFINE_OPCODE(opcode) \
        case opcode:\
            OpcodeStats::recordInstruction(opcode);\
            UPDATE_BYTECODE_OFFSET();
#else
    #define DEFINE_OPCODE(opcode) case opcode: UPDATE_BYTECODE_OFFSET();
#endif
while (1) { // iterator loop begins
interpreterLoopStart:;
switch (vPC->u.opcode)
#endif
{
    DEFINE_OPCODE(op_new_object) {
        /* new_object dst(r)
         
         Constructs a new empty Object instance using the original
         constructor, and puts the result in register dst.
         */
        int dst = vPC[1].u.operand;
        
        // IFC4BC
        if (labelReq && !isPolicy) {
            JSObject* newlyCreatedObject = constructEmptyObject(callFrame);
            newlyCreatedObject->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            newlyCreatedObject->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
            // DNSU
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            callFrame->uncheckedR(dst) = JSValue(newlyCreatedObject);
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            JSObject* newlyCreatedObject = constructEmptyObject(callFrame);
            newlyCreatedObject->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            newlyCreatedObject->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            callFrame->uncheckedR(dst) = JSValue(newlyCreatedObject);
        }
        
        // Assign object label, proto label, and value label for JSValue going in the register
        
        // ------------------------------------- //
        // Original
        // callFrame->uncheckedR(dst) = JSValue(constructEmptyObject(callFrame));
        
        vPC += OPCODE_LENGTH(op_new_object);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_new_array) {
        /* new_array dst(r) firstArg(r) argCount(n)
         
         Constructs a new Array instance using the original
         constructor, and puts the result in register dst.
         The array will contain argCount elements with values
         taken from registers starting at register firstArg.
         */
        int dst = vPC[1].u.operand;
        int firstArg = vPC[2].u.operand;
        int argCount = vPC[3].u.operand;
        
        // IFC4BC
        // Should the values being written also have labels? Can assign the registers.
        if (labelReq && !isPolicy) {
            JSValue vA = JSValue(constructArray(callFrame, reinterpret_cast<JSValue*>(&callFrame->registers()[firstArg]), argCount));
            vA.asCell()->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            vA.asCell()->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
            // DNSU
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            callFrame->uncheckedR(dst) = vA;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            JSValue vA = JSValue(constructArray(callFrame, reinterpret_cast<JSValue*>(&callFrame->registers()[firstArg]), argCount));
            vA.asCell()->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            vA.asCell()->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            callFrame->uncheckedR(dst) = vA;
        }
        // ------
        // Original
        // callFrame->uncheckedR(dst) = JSValue(constructArray(callFrame, reinterpret_cast<JSValue*>(&callFrame->registers()[firstArg]), argCount));
        
        vPC += OPCODE_LENGTH(op_new_array);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_new_array_buffer) {
        /* new_array_buffer dst(r) index(n) argCount(n)
         
         Constructs a new Array instance using the original
         constructor, and puts the result in register dst.
         The array be initialized with the values from constantBuffer[index]
         */
        int dst = vPC[1].u.operand;
        int firstArg = vPC[2].u.operand;
        int argCount = vPC[3].u.operand;
        
        // IFC4BC
        // Should the values being written also have labels?
        if (labelReq  && !isPolicy) {
            JSValue vA = JSValue(constructArray(callFrame, codeBlock->constantBuffer(firstArg), argCount));
            vA.asCell()->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            vA.asCell()->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
            // DNSU
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = vA;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            JSValue vA = JSValue(constructArray(callFrame, codeBlock->constantBuffer(firstArg), argCount));
            vA.asCell()->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            vA.asCell()->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            callFrame->uncheckedR(dst) = vA;
        }
        // ------
        // Original
        // callFrame->uncheckedR(dst) = JSValue(constructArray(callFrame, codeBlock->constantBuffer(firstArg), argCount));
        
        vPC += OPCODE_LENGTH(op_new_array);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_new_regexp) {
        /* new_regexp dst(r) regExp(re)
         
         Constructs a new RegExp instance using the original
         constructor from regexp regExp, and puts the result in
         register dst.
         */
        int dst = vPC[1].u.operand;
        RegExp* regExp = codeBlock->regexp(vPC[2].u.operand);
        if (!regExp->isValid()) {
            exceptionValue = createSyntaxError(callFrame, "Invalid flags supplied to RegExp constructor.");
            exceptionValue.setValueLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            goto vm_throw;
        }
        
        // IFC4BC
        // Assign the object a label.
        if (labelReq && !isPolicy) {
            JSValue rv = JSValue(RegExpObject::create(*globalData, callFrame->lexicalGlobalObject(), callFrame->scopeChain()->globalObject->regExpStructure(), regExp));
            rv.asCell()->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            rv.asCell()->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
            // DNSU
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            callFrame->uncheckedR(dst) = rv;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            JSValue rv = JSValue(RegExpObject::create(*globalData, callFrame->lexicalGlobalObject(), callFrame->scopeChain()->globalObject->regExpStructure(), regExp));
            rv.asCell()->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            rv.asCell()->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            callFrame->uncheckedR(dst) = rv;
        }
        //-------------------------------
        // Original
        // callFrame->uncheckedR(dst) = JSValue(RegExpObject::create(*globalData, callFrame->lexicalGlobalObject(), callFrame->scopeChain()->globalObject->regExpStructure(), regExp));
        
        vPC += OPCODE_LENGTH(op_new_regexp);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_mov) {
        /* mov dst(r) src(r)
         
         Copies register src to register dst.
         */
        int dst = vPC[1].u.operand;
        int src = vPC[2].u.operand;
        
        if (labelReq  && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            callFrame->uncheckedR(dst) = callFrame->r(src);
            callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(callFrame->r(src).getRegLabel()));
        }
        else {
            callFrame->uncheckedR(dst) = callFrame->r(src);
        }
        
        vPC += OPCODE_LENGTH(op_mov);
         NEXT_INSTRUCTION();
    }
    // Abhi -- Definition for op_mov_empty
    // Makes the register value as empty
    // Used exclusively for finally block
    // Do not use this elsewhere / JS does not use this
    DEFINE_OPCODE(op_mov_empty) {
        /* mov_empty dst(r)
         
         Makes the register value as empty
         */
        int dst = vPC[1].u.operand;
        callFrame->uncheckedR(dst) = JSValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        vPC += OPCODE_LENGTH(op_mov_empty);
         NEXT_INSTRUCTION();
    }
    // Abhi ------------------------------------------
    DEFINE_OPCODE(op_eq) {
        /* eq dst(r) src1(r) src2(r)
         
         Checks whether register src1 and register src2 are equal,
         as with the ECMAScript '==' operator, and puts the result
         as a boolean in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src1 = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[3].u.operand).jsValue();
        
        // IFC4BC  instrumentation
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel;
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                dstLabel = dstLabel.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else {
                // dstLabel.setStar(false);
                JSLabel tdstLabel = (callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
                uint64_t dstL = tdstLabel.Val();
                /*
                if (pcLabel <= tdstLabel) {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t bits = BitMap::Bitmap().getBits(i);
                            uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                            uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                            if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                                dstL = dstL | aLabel;
                            }
                            else {
                                BitMap::Bitmap().setBits(i, bits - 1);
                                dstL = dstL | dLabel;
                            }
                        }
                        i = i << 1;
                    }
                }
                else {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                            dstL = dstL | dLabel;
                        }
                        i = i << 1;
                    }
                }*/
                dstLabel = dstLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            }
            if (src1.isInt32() && src2.isInt32())
                callFrame->uncheckedR(dst) = jsBoolean(src1.asInt32() == src2.asInt32());
            else {
                JSValue result = jsBoolean(JSValue::equalSlowCase(callFrame, src1, src2));
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(dst) = result;
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (src1.isInt32() && src2.isInt32())
                callFrame->uncheckedR(dst) = jsBoolean(src1.asInt32() == src2.asInt32());
            else {
                JSValue result = jsBoolean(JSValue::equalSlowCase(callFrame, src1, src2));
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(dst) = result;
            }
        }
        vPC += OPCODE_LENGTH(op_eq);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_eq_null) {
        /* eq_null dst(r) src(r)
         
         Checks whether register src is null, as with the ECMAScript '!='
         operator, and puts the result as a boolean in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src = callFrame->r(vPC[2].u.operand).jsValue();
        
        // IFC4BC  instrumentation
        if (labelReq && !isPolicy) {
//            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel());
//            
//            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
//            {
//                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
//                dstLabel.setStar(true);
//            }
//            else {
//                // dstLabel.setStar(false);
//            }
            JSLabel dstLabel = JSLabel();
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                dstLabel = pcLabel.Join(callFrame->r(vPC[2].u.operand).getRegLabel());
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else {
                // dstLabel.setStar(false);
                JSLabel tdstLabel = callFrame->r(vPC[2].u.operand).getRegLabel();
                uint64_t dstL = tdstLabel.Val();
                /*
                if (pcLabel <= tdstLabel) {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t bits = BitMap::Bitmap().getBits(i);
                            uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                            uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                            if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                                dstL = dstL | aLabel;
                            }
                            else {
                                BitMap::Bitmap().setBits(i, bits - 1);
                                dstL = dstL | dLabel;
                            }
                        }
                        i = i << 1;
                    }
                }
                else {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                            dstL = dstL | dLabel;
                        }
                        i = i << 1;
                    }
                }*/
                dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            }
            if (src.isUndefinedOrNull())
                callFrame->uncheckedR(dst) = jsBoolean(true);
            else
                callFrame->uncheckedR(dst) = jsBoolean(src.isCell() && src.asCell()->structure()->typeInfo().masqueradesAsUndefined());
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (src.isUndefinedOrNull())
                callFrame->uncheckedR(dst) = jsBoolean(true);
            else
                callFrame->uncheckedR(dst) = jsBoolean(src.isCell() && src.asCell()->structure()->typeInfo().masqueradesAsUndefined());
        }
        vPC += OPCODE_LENGTH(op_eq_null);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_neq) {
        /* neq dst(r) src1(r) src2(r)
         
         Checks whether register src1 and register src2 are not
         equal, as with the ECMAScript '!=' operator, and puts the
         result as a boolean in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src1 = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
//            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
//            
//            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
//            {
//                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
//                dstLabel.setStar(true);
//            }
//            else {
//                // dstLabel.setStar(false);
//            }
            JSLabel dstLabel = JSLabel();
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                dstLabel = pcLabel.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else {
                // dstLabel.setStar(false);
                JSLabel tdstLabel = (callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
                uint64_t dstL = tdstLabel.Val();
                /*
                if (pcLabel <= tdstLabel) {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t bits = BitMap::Bitmap().getBits(i);
                            uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                            uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                            if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                                dstL = dstL | aLabel;
                            }
                            else {
                                BitMap::Bitmap().setBits(i, bits - 1);
                                dstL = dstL | dLabel;
                            }
                        }
                        i = i << 1;
                    }
                }
                else {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                            dstL = dstL | dLabel;
                        }
                        i = i << 1;
                    }
                }*/
                dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            }
            if (src1.isInt32() && src2.isInt32())
                callFrame->uncheckedR(dst) = jsBoolean(src1.asInt32() != src2.asInt32());
            else {
                JSValue result = jsBoolean(!JSValue::equalSlowCase(callFrame, src1, src2));
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(dst) = result;
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (src1.isInt32() && src2.isInt32())
                callFrame->uncheckedR(dst) = jsBoolean(src1.asInt32() != src2.asInt32());
            else {
                JSValue result = jsBoolean(!JSValue::equalSlowCase(callFrame, src1, src2));
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(dst) = result;
            }
        }
        vPC += OPCODE_LENGTH(op_neq);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_neq_null) {
        /* neq_null dst(r) src(r)
         
         Checks whether register src is not null, as with the ECMAScript '!='
         operator, and puts the result as a boolean in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src = callFrame->r(vPC[2].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
//            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel());
//            
//            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
//            {
//                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
//                dstLabel.setStar(true);
//            }
//            else {
//                // dstLabel.setStar(false);
//            }
            JSLabel dstLabel = JSLabel();
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                dstLabel = pcLabel.Join(callFrame->r(vPC[2].u.operand).getRegLabel());
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else {
                // dstLabel.setStar(false);
                JSLabel tdstLabel = (callFrame->r(vPC[2].u.operand).getRegLabel());
                uint64_t dstL = tdstLabel.Val();
                /*
                if (pcLabel <= tdstLabel) {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t bits = BitMap::Bitmap().getBits(i);
                            uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                            uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                            if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                                dstL = dstL | aLabel;
                            }
                            else {
                                BitMap::Bitmap().setBits(i, bits - 1);
                                dstL = dstL | dLabel;
                            }
                        }
                        i = i << 1;
                    }
                }
                else {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                            dstL = dstL | dLabel;
                        }
                        i = i << 1;
                    }
                }*/
                dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            }
            if (src.isUndefinedOrNull())
                callFrame->uncheckedR(dst) = jsBoolean(false);
            else
                callFrame->uncheckedR(dst) = jsBoolean(!src.isCell() || !src.asCell()->structure()->typeInfo().masqueradesAsUndefined());
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (src.isUndefinedOrNull())
                callFrame->uncheckedR(dst) = jsBoolean(false);
            else
                callFrame->uncheckedR(dst) = jsBoolean(!src.isCell() || !src.asCell()->structure()->typeInfo().masqueradesAsUndefined());
        }
        vPC += OPCODE_LENGTH(op_neq_null);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_stricteq) {
        /* stricteq dst(r) src1(r) src2(r)
         
         Checks whether register src1 and register src2 are strictly
         equal, as with the ECMAScript '===' operator, and puts the
         result as a boolean in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src1 = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            // JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
            
            bool result = JSValue::strictEqual(callFrame, src1, src2);
            
//            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
//            {
//                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
//                dstLabel.setStar(true);
//            }
//            else {
//                // dstLabel.setStar(false);
//            }
            JSLabel dstLabel = pcLabel;
            CHECK_FOR_EXCEPTION(dstLabel);
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else {
                // dstLabel.setStar(false);
                JSLabel tdstLabel = (callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
                uint64_t dstL = tdstLabel.Val();
                /*
                if (pcLabel <= tdstLabel) {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t bits = BitMap::Bitmap().getBits(i);
                            uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                            uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                            if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                                dstL = dstL | aLabel;
                            }
                            else {
                                BitMap::Bitmap().setBits(i, bits - 1);
                                dstL = dstL | dLabel;
                            }
                        }
                        i = i << 1;
                    }
                }
                else {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                            dstL = dstL | dLabel;
                        }
                        i = i << 1;
                    }
                }*/
                dstLabel = dstLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            }
            callFrame->uncheckedR(dst) = jsBoolean(result);
            callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel())));
        }
        else {
            bool result = JSValue::strictEqual(callFrame, src1, src2);
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
            callFrame->uncheckedR(dst) = jsBoolean(result);
        }
        vPC += OPCODE_LENGTH(op_stricteq);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_nstricteq) {
        /* nstricteq dst(r) src1(r) src2(r)
         
         Checks whether register src1 and register src2 are not
         strictly equal, as with the ECMAScript '!==' operator, and
         puts the result as a boolean in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src1 = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            // JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
            
            bool result = !JSValue::strictEqual(callFrame, src1, src2);
//            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
//            {
//                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
//                dstLabel.setStar(true);
//            }
//            else {
//                // dstLabel.setStar(false);
//            }
            JSLabel dstLabel = pcLabel;
            CHECK_FOR_EXCEPTION(dstLabel);
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else {
                // dstLabel.setStar(false);
                JSLabel tdstLabel = (callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
                uint64_t dstL = tdstLabel.Val();
                /*
                if (pcLabel <= tdstLabel) {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t bits = BitMap::Bitmap().getBits(i);
                            uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                            uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                            if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                                dstL = dstL | aLabel;
                            }
                            else {
                                BitMap::Bitmap().setBits(i, bits - 1);
                                dstL = dstL | dLabel;
                            }
                        }
                        i = i << 1;
                    }
                }
                else {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                            dstL = dstL | dLabel;
                        }
                        i = i << 1;
                    }
                }*/
                dstLabel = dstLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            }

            callFrame->uncheckedR(dst) = jsBoolean(result);
            callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel())));
        }
        else {
            bool result = !JSValue::strictEqual(callFrame, src1, src2);
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
            callFrame->uncheckedR(dst) = jsBoolean(result);
        }
        vPC += OPCODE_LENGTH(op_nstricteq);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_less) {
        /* less dst(r) src1(r) src2(r)
         
         Checks whether register src1 is less than register src2, as
         with the ECMAScript '<' operator, and puts the result as
         a boolean in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src1 = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            // JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
            
            JSValue result = jsBoolean(jsLess<true>(callFrame, src1, src2));
//            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
//            {
//                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
//                dstLabel.setStar(true);
//            }
//            else
//            {
//                // dstLabel.setStar(false);
//            }
            JSLabel dstLabel = pcLabel;
            CHECK_FOR_EXCEPTION(dstLabel);
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else {
                // dstLabel.setStar(false);
                JSLabel tdstLabel = (callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
                uint64_t dstL = tdstLabel.Val();
                /*
                if (pcLabel <= tdstLabel) {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t bits = BitMap::Bitmap().getBits(i);
                            uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                            uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                            if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                                dstL = dstL | aLabel;
                            }
                            else {
                                BitMap::Bitmap().setBits(i, bits - 1);
                                dstL = dstL | dLabel;
                            }
                        }
                        i = i << 1;
                    }
                }
                else {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                            dstL = dstL | dLabel;
                        }
                        i = i << 1;
                    }
                }*/
                dstLabel = dstLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            }

            callFrame->uncheckedR(dst) = result;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel())));
        }
        else {
            JSValue result = jsBoolean(jsLess<true>(callFrame, src1, src2));
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
            callFrame->uncheckedR(dst) = result;
        }
        vPC += OPCODE_LENGTH(op_less);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_lesseq) {
        /* lesseq dst(r) src1(r) src2(r)
         
         Checks whether register src1 is less than or equal to
         register src2, as with the ECMAScript '<=' operator, and
         puts the result as a boolean in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src1 = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            //JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
            
            JSValue result = jsBoolean(jsLessEq<true>(callFrame, src1, src2));
//            CHECK_FOR_EXCEPTION(dstLabel);
//            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
//            {
//                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
//                dstLabel.setStar(true);
//            }
//            else {
//                // dstLabel.setStar(false);
//            }
            JSLabel dstLabel = pcLabel;
            CHECK_FOR_EXCEPTION(dstLabel);
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else {
                // dstLabel.setStar(false);
                JSLabel tdstLabel = (callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
                uint64_t dstL = tdstLabel.Val();
                /*
                if (pcLabel <= tdstLabel) {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t bits = BitMap::Bitmap().getBits(i);
                            uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                            uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                            if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                                dstL = dstL | aLabel;
                            }
                            else {
                                BitMap::Bitmap().setBits(i, bits - 1);
                                dstL = dstL | dLabel;
                            }
                        }
                        i = i << 1;
                    }
                }
                else {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                            dstL = dstL | dLabel;
                        }
                        i = i << 1;
                    }
                }*/
                dstLabel = dstLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            }
            
            callFrame->uncheckedR(dst) = result;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel())));
        }
        else {
            JSValue result = jsBoolean(jsLessEq<true>(callFrame, src1, src2));
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
            callFrame->uncheckedR(dst) = result;
        }
        vPC += OPCODE_LENGTH(op_lesseq);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_greater) {
        /* greater dst(r) src1(r) src2(r)
         
         Checks whether register src1 is greater than register src2, as
         with the ECMAScript '>' operator, and puts the result as
         a boolean in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src1 = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            // JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
            
            JSValue result = jsBoolean(jsLess<false>(callFrame, src2, src1));
//            CHECK_FOR_EXCEPTION(dstLabel);
//            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
//            {
//                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
//                dstLabel.setStar(true);
//            }
//            else {
//                // dstLabel.setStar(false);
//            }
            JSLabel dstLabel = pcLabel;
            CHECK_FOR_EXCEPTION(dstLabel);
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else {
                // dstLabel.setStar(false);
                JSLabel tdstLabel = (callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
                uint64_t dstL = tdstLabel.Val();
                /*
                if (pcLabel <= tdstLabel) {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t bits = BitMap::Bitmap().getBits(i);
                            uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                            uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                            if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                                dstL = dstL | aLabel;
                            }
                            else {
                                BitMap::Bitmap().setBits(i, bits - 1);
                                dstL = dstL | dLabel;
                            }
                        }
                        i = i << 1;
                    }
                }
                else {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                            dstL = dstL | dLabel;
                        }
                        i = i << 1;
                    }
                }*/
                dstLabel = dstLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            }
            callFrame->uncheckedR(dst) = result;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel())));
        }
        else {
            JSValue result = jsBoolean(jsLess<false>(callFrame, src2, src1));
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
            callFrame->uncheckedR(dst) = result;
        }
        vPC += OPCODE_LENGTH(op_greater);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_greatereq) {
        /* greatereq dst(r) src1(r) src2(r)
         
         Checks whether register src1 is greater than or equal to
         register src2, as with the ECMAScript '>=' operator, and
         puts the result as a boolean in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src1 = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            // JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
            
            JSValue result = jsBoolean(jsLessEq<false>(callFrame, src2, src1));
//            CHECK_FOR_EXCEPTION(dstLabel);
//            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
//            {
//                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
//                dstLabel.setStar(true);
//            }
//            else {
//                // dstLabel.setStar(false);
//            }
            JSLabel dstLabel = pcLabel.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
            CHECK_FOR_EXCEPTION(dstLabel);
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else {
                // dstLabel.setStar(false);
                JSLabel tdstLabel = (callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
                uint64_t dstL = tdstLabel.Val();
                /*
                if (pcLabel <= tdstLabel) {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t bits = BitMap::Bitmap().getBits(i);
                            uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                            uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                            if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                                dstL = dstL | aLabel;
                            }
                            else {
                                BitMap::Bitmap().setBits(i, bits - 1);
                                dstL = dstL | dLabel;
                            }
                        }
                        i = i << 1;
                    }
                }
                else {
                    uint64_t i = 1;
                    uint64_t pLabel = tdstLabel.pLabel;
                    tdstLabel.pLabel = 0;
                    for (int j = 1; j <= 64; j++) {
                        if (pLabel & i) {
                            uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                            dstL = dstL | dLabel;
                        }
                        i = i << 1;
                    }
                }*/
                dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            }
            callFrame->uncheckedR(dst) = result;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            JSValue result = jsBoolean(jsLessEq<false>(callFrame, src2, src1));
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
            callFrame->uncheckedR(dst) = result;
        }
        vPC += OPCODE_LENGTH(op_greatereq);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_pre_inc) {
        /* pre_inc srcDst(r)
         
         Converts register srcDst to number, adds one, and puts the result
         back in register srcDst.
         */
        int srcDst = vPC[1].u.operand;
        JSValue v = callFrame->r(srcDst).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(srcDst).getRegLabel());

            if (!noSensitiveUpgrade(callFrame->r(srcDst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(srcDst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (v.isInt32() && v.asInt32() < INT_MAX)
                callFrame->uncheckedR(srcDst) = jsNumber(v.asInt32() + 1);
            else {
                JSValue result = jsNumber(v.toNumber(callFrame) + 1);
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(srcDst) = result;
            }
            callFrame->uncheckedR(srcDst).setRegLabel(dstLabel);
        }
        else {
            if (v.isInt32() && v.asInt32() < INT_MAX)
                callFrame->uncheckedR(srcDst) = jsNumber(v.asInt32() + 1);
            else {
                JSValue result = jsNumber(v.toNumber(callFrame) + 1);
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(srcDst) = result;
            }
        }
        vPC += OPCODE_LENGTH(op_pre_inc);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_pre_dec) {
        /* pre_dec srcDst(r)
         
         Converts register srcDst to number, subtracts one, and puts the result
         back in register srcDst.
         */
        int srcDst = vPC[1].u.operand;
        JSValue v = callFrame->r(srcDst).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(srcDst).getRegLabel());
        
            if (!noSensitiveUpgrade(callFrame->r(srcDst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(srcDst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (v.isInt32() && v.asInt32() > INT_MIN)
                callFrame->uncheckedR(srcDst) = jsNumber(v.asInt32() - 1);
            else {
                JSValue result = jsNumber(v.toNumber(callFrame) - 1);
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(srcDst) = result;
            }
            callFrame->uncheckedR(srcDst).setRegLabel(dstLabel);
        }
        else {
            if (v.isInt32() && v.asInt32() > INT_MIN)
                callFrame->uncheckedR(srcDst) = jsNumber(v.asInt32() - 1);
            else {
                JSValue result = jsNumber(v.toNumber(callFrame) - 1);
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(srcDst) = result;
            }
        }
        vPC += OPCODE_LENGTH(op_pre_dec);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_post_inc) {
        /* post_inc dst(r) srcDst(r)
         
         Converts register srcDst to number. The number itself is
         written to register dst, and the number plus one is written
         back to register srcDst.
         */
        int dst = vPC[1].u.operand;
        int srcDst = vPC[2].u.operand;
        JSValue v = callFrame->r(srcDst).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(srcDst).getRegLabel());
        
            JSLabel srcDstLabel = dstLabel;
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (!noSensitiveUpgrade(callFrame->r(srcDst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(srcDst).getRegLabel().Val(), pcLabel.Val());
                srcDstLabel.setStar(true);
            }
            else {
                // srcDstLabel.setStar(false);
            }
            if (v.isInt32() && v.asInt32() < INT_MAX) {
                callFrame->uncheckedR(srcDst) = jsNumber(v.asInt32() + 1);
                callFrame->uncheckedR(dst) = v;
            } else {
                double number = callFrame->r(srcDst).jsValue().toNumber(callFrame);
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(srcDst) = jsNumber(number + 1);
                callFrame->uncheckedR(dst) = jsNumber(number);
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
            callFrame->uncheckedR(srcDst).setRegLabel(srcDstLabel);
        }
        else {
            if (v.isInt32() && v.asInt32() < INT_MAX) {
                callFrame->uncheckedR(srcDst) = jsNumber(v.asInt32() + 1);
                callFrame->uncheckedR(dst) = v;
            } else {
                double number = callFrame->r(srcDst).jsValue().toNumber(callFrame);
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(srcDst) = jsNumber(number + 1);
                callFrame->uncheckedR(dst) = jsNumber(number);
            }
        }
        vPC += OPCODE_LENGTH(op_post_inc);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_post_dec) {
        /* post_dec dst(r) srcDst(r)
         
         Converts register srcDst to number. The number itself is
         written to register dst, and the number minus one is written
         back to register srcDst.
         */
        int dst = vPC[1].u.operand;
        int srcDst = vPC[2].u.operand;
        JSValue v = callFrame->r(srcDst).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(srcDst).getRegLabel());
            JSLabel srcDstLabel = dstLabel;
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (!noSensitiveUpgrade(callFrame->r(srcDst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(srcDst).getRegLabel().Val(), pcLabel.Val());
                srcDstLabel.setStar(true);
            }
            else {
                // srcDstLabel.setStar(false);
            }
            if (v.isInt32() && v.asInt32() > INT_MIN) {
                callFrame->uncheckedR(srcDst) = jsNumber(v.asInt32() - 1);
                callFrame->uncheckedR(dst) = v;
            } else {
                double number = callFrame->r(srcDst).jsValue().toNumber(callFrame);
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(srcDst) = jsNumber(number - 1);
                callFrame->uncheckedR(dst) = jsNumber(number);
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
            callFrame->uncheckedR(srcDst).setRegLabel(srcDstLabel);
        }
        else {
            if (v.isInt32() && v.asInt32() > INT_MIN) {
                callFrame->uncheckedR(srcDst) = jsNumber(v.asInt32() - 1);
                callFrame->uncheckedR(dst) = v;
            } else {
                double number = callFrame->r(srcDst).jsValue().toNumber(callFrame);
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(srcDst) = jsNumber(number - 1);
                callFrame->uncheckedR(dst) = jsNumber(number);
            }
        }
        vPC += OPCODE_LENGTH(op_post_dec);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_to_jsnumber) {
        /* to_jsnumber dst(r) src(r)
         
         Converts register src to number, and puts the result
         in register dst.
         */
        int dst = vPC[1].u.operand;
        int src = vPC[2].u.operand;
        JSValue srcVal = callFrame->r(src).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(src).getRegLabel());
        
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (LIKELY(srcVal.isNumber()))
                callFrame->uncheckedR(dst) = callFrame->r(src);
            else {
                double number = srcVal.toNumber(callFrame);
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(dst) = jsNumber(number);
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (LIKELY(srcVal.isNumber()))
                callFrame->uncheckedR(dst) = callFrame->r(src);
            else {
                double number = srcVal.toNumber(callFrame);
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(dst) = jsNumber(number);
            }
        }
        vPC += OPCODE_LENGTH(op_to_jsnumber);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_negate) {
        /* negate dst(r) src(r)
         
         Converts register src to number, negates it, and puts the
         result in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src = callFrame->r(vPC[2].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel());
        
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (src.isInt32() && (src.asInt32() & 0x7fffffff)) // non-zero and no overflow
                callFrame->uncheckedR(dst) = jsNumber(-src.asInt32());
            else {
                JSValue result = jsNumber(-src.toNumber(callFrame));
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(dst) = result;
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (src.isInt32() && (src.asInt32() & 0x7fffffff)) // non-zero and no overflow
                callFrame->uncheckedR(dst) = jsNumber(-src.asInt32());
            else {
                JSValue result = jsNumber(-src.toNumber(callFrame));
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(dst) = result;
            }
        }
        vPC += OPCODE_LENGTH(op_negate);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_add) {
        /* add dst(r) src1(r) src2(r)
         
         Adds register src1 and register src2, and puts the result
         in register dst. (JS add may be string concatenation or
         numeric add, depending on the types of the operands.)
         */
        int dst = vPC[1].u.operand;
        JSValue src1 = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
        
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (src1.isInt32() && src2.isInt32() && !((src1.asInt32() | src2.asInt32()) & 0xc0000000)) // no overflow
                callFrame->uncheckedR(dst) = jsNumber(src1.asInt32() + src2.asInt32());
            else {
                JSValue result = jsAdd(callFrame, src1, src2);
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(dst) = result;
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (src1.isInt32() && src2.isInt32() && !((src1.asInt32() | src2.asInt32()) & 0xc0000000)) // no overflow
                callFrame->uncheckedR(dst) = jsNumber(src1.asInt32() + src2.asInt32());
            else {
                JSValue result = jsAdd(callFrame, src1, src2);
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(dst) = result;
            }
        }
        vPC += OPCODE_LENGTH(op_add);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_mul) {
        /* mul dst(r) src1(r) src2(r)
         
         Multiplies register src1 and register src2 (converted to
         numbers), and puts the product in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src1 = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
        
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (src1.isInt32() && src2.isInt32() && !(src1.asInt32() | src2.asInt32()) >> 15) // no overflow
                callFrame->uncheckedR(dst) = jsNumber(src1.asInt32() * src2.asInt32());
            else {
                JSValue result = jsNumber(src1.toNumber(callFrame) * src2.toNumber(callFrame));
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(dst) = result;
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (src1.isInt32() && src2.isInt32() && !(src1.asInt32() | src2.asInt32()) >> 15) // no overflow
                callFrame->uncheckedR(dst) = jsNumber(src1.asInt32() * src2.asInt32());
            else {
                JSValue result = jsNumber(src1.toNumber(callFrame) * src2.toNumber(callFrame));
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(dst) = result;
            }
        }
        vPC += OPCODE_LENGTH(op_mul);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_div) {
        /* div dst(r) dividend(r) divisor(r)
         
         Divides register dividend (converted to number) by the
         register divisor (converted to number), and puts the
         quotient in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue dividend = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue divisor = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
        
            JSValue result = jsNumber(dividend.toNumber(callFrame) / divisor.toNumber(callFrame));
            CHECK_FOR_EXCEPTION(dstLabel);
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = result;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            JSValue result = jsNumber(dividend.toNumber(callFrame) / divisor.toNumber(callFrame));
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
            callFrame->uncheckedR(dst) = result;
        }
        vPC += OPCODE_LENGTH(op_div);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_mod) {
        /* mod dst(r) dividend(r) divisor(r)
         
         Divides register dividend (converted to number) by
         register divisor (converted to number), and puts the
         remainder in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue dividend = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue divisor = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));

            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (dividend.isInt32() && divisor.isInt32() && divisor.asInt32() != 0 && divisor.asInt32() != -1) {
                JSValue result = jsNumber(dividend.asInt32() % divisor.asInt32());
                ASSERT(result);
                callFrame->uncheckedR(dst) = result;
            }
            else {
                double d1 = dividend.toNumber(callFrame);
                double d2 = divisor.toNumber(callFrame);
                JSValue result = jsNumber(fmod(d1, d2));
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(dst) = result;
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (dividend.isInt32() && divisor.isInt32() && divisor.asInt32() != 0 && divisor.asInt32() != -1) {
                JSValue result = jsNumber(dividend.asInt32() % divisor.asInt32());
                ASSERT(result);
                callFrame->uncheckedR(dst) = result;
            }
            else {
                double d1 = dividend.toNumber(callFrame);
                double d2 = divisor.toNumber(callFrame);
                JSValue result = jsNumber(fmod(d1, d2));
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(dst) = result;
            }
        }
        vPC += OPCODE_LENGTH(op_mod);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_sub) {
        /* sub dst(r) src1(r) src2(r)
         
         Subtracts register src2 (converted to number) from register
         src1 (converted to number), and puts the difference in
         register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src1 = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
        
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (src1.isInt32() && src2.isInt32() && !((src1.asInt32() | src2.asInt32()) & 0xc0000000)) // no overflow
                callFrame->uncheckedR(dst) = jsNumber(src1.asInt32() - src2.asInt32());
            else {
                JSValue result = jsNumber(src1.toNumber(callFrame) - src2.toNumber(callFrame));
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(dst) = result;
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (src1.isInt32() && src2.isInt32() && !((src1.asInt32() | src2.asInt32()) & 0xc0000000)) // no overflow
                callFrame->uncheckedR(dst) = jsNumber(src1.asInt32() - src2.asInt32());
            else {
                JSValue result = jsNumber(src1.toNumber(callFrame) - src2.toNumber(callFrame));
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(dst) = result;
            }
        }
        vPC += OPCODE_LENGTH(op_sub);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_lshift) {
        /* lshift dst(r) val(r) shift(r)
         
         Performs left shift of register val (converted to int32) by
         register shift (converted to uint32), and puts the result
         in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue val = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue shift = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
        
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (val.isInt32() && shift.isInt32())
                callFrame->uncheckedR(dst) = jsNumber(val.asInt32() << (shift.asInt32() & 0x1f));
            else {
                JSValue result = jsNumber((val.toInt32(callFrame)) << (shift.toUInt32(callFrame) & 0x1f));
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(dst) = result;
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (val.isInt32() && shift.isInt32())
                callFrame->uncheckedR(dst) = jsNumber(val.asInt32() << (shift.asInt32() & 0x1f));
            else {
                JSValue result = jsNumber((val.toInt32(callFrame)) << (shift.toUInt32(callFrame) & 0x1f));
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(dst) = result;
            }
        }
        vPC += OPCODE_LENGTH(op_lshift);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_rshift) {
        /* rshift dst(r) val(r) shift(r)
         
         Performs arithmetic right shift of register val (converted
         to int32) by register shift (converted to
         uint32), and puts the result in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue val = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue shift = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
        
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (val.isInt32() && shift.isInt32())
                callFrame->uncheckedR(dst) = jsNumber(val.asInt32() >> (shift.asInt32() & 0x1f));
            else {
                JSValue result = jsNumber((val.toInt32(callFrame)) >> (shift.toUInt32(callFrame) & 0x1f));
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(dst) = result;
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (val.isInt32() && shift.isInt32())
                callFrame->uncheckedR(dst) = jsNumber(val.asInt32() >> (shift.asInt32() & 0x1f));
            else {
                JSValue result = jsNumber((val.toInt32(callFrame)) >> (shift.toUInt32(callFrame) & 0x1f));
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(dst) = result;
            }
        }
        vPC += OPCODE_LENGTH(op_rshift);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_urshift) {
        /* rshift dst(r) val(r) shift(r)
         
         Performs logical right shift of register val (converted
         to uint32) by register shift (converted to
         uint32), and puts the result in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue val = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue shift = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
        
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (val.isUInt32() && shift.isInt32())
                callFrame->uncheckedR(dst) = jsNumber(val.asInt32() >> (shift.asInt32() & 0x1f));
            else {
                JSValue result = jsNumber((val.toUInt32(callFrame)) >> (shift.toUInt32(callFrame) & 0x1f));
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(dst) = result;
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (val.isUInt32() && shift.isInt32())
                callFrame->uncheckedR(dst) = jsNumber(val.asInt32() >> (shift.asInt32() & 0x1f));
            else {
                JSValue result = jsNumber((val.toUInt32(callFrame)) >> (shift.toUInt32(callFrame) & 0x1f));
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(dst) = result;
            }
        }
        vPC += OPCODE_LENGTH(op_urshift);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_bitand) {
        /* bitand dst(r) src1(r) src2(r)
         
         Computes bitwise AND of register src1 (converted to int32)
         and register src2 (converted to int32), and puts the result
         in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src1 = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
        
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (src1.isInt32() && src2.isInt32())
                callFrame->uncheckedR(dst) = jsNumber(src1.asInt32() & src2.asInt32());
            else {
                JSValue result = jsNumber(src1.toInt32(callFrame) & src2.toInt32(callFrame));
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(dst) = result;
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (src1.isInt32() && src2.isInt32())
                callFrame->uncheckedR(dst) = jsNumber(src1.asInt32() & src2.asInt32());
            else {
                JSValue result = jsNumber(src1.toInt32(callFrame) & src2.toInt32(callFrame));
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(dst) = result;
            }
        }
        vPC += OPCODE_LENGTH(op_bitand);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_bitxor) {
        /* bitxor dst(r) src1(r) src2(r)
         
         Computes bitwise XOR of register src1 (converted to int32)
         and register src2 (converted to int32), and puts the result
         in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src1 = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[3].u.operand).jsValue();
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
        
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (src1.isInt32() && src2.isInt32())
                callFrame->uncheckedR(dst) = jsNumber(src1.asInt32() ^ src2.asInt32());
            else {
                JSValue result = jsNumber(src1.toInt32(callFrame) ^ src2.toInt32(callFrame));
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(dst) = result;
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (src1.isInt32() && src2.isInt32())
                callFrame->uncheckedR(dst) = jsNumber(src1.asInt32() ^ src2.asInt32());
            else {
                JSValue result = jsNumber(src1.toInt32(callFrame) ^ src2.toInt32(callFrame));
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(dst) = result;
            }
        }
        vPC += OPCODE_LENGTH(op_bitxor);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_bitor) {
        /* bitor dst(r) src1(r) src2(r)
         
         Computes bitwise OR of register src1 (converted to int32)
         and register src2 (converted to int32), and puts the
         result in register dst.
         */
        int dst = vPC[1].u.operand;
        JSValue src1 = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(vPC[2].u.operand).getRegLabel().Join(callFrame->r(vPC[3].u.operand).getRegLabel()));
        
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){

                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (src1.isInt32() && src2.isInt32())
                callFrame->uncheckedR(dst) = jsNumber(src1.asInt32() | src2.asInt32());
            else {
                JSValue result = jsNumber(src1.toInt32(callFrame) | src2.toInt32(callFrame));
                CHECK_FOR_EXCEPTION(dstLabel);
                callFrame->uncheckedR(dst) = result;
            }
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            if (src1.isInt32() && src2.isInt32())
                callFrame->uncheckedR(dst) = jsNumber(src1.asInt32() | src2.asInt32());
            else {
                JSValue result = jsNumber(src1.toInt32(callFrame) | src2.toInt32(callFrame));
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(dst) = result;
            }
        }
        
        vPC += OPCODE_LENGTH(op_bitor);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_not) {
        /* not dst(r) src(r)
         
         Computes logical NOT of register src (converted to
         boolean), and puts the result in register dst.
         */
        int dst = vPC[1].u.operand;
        int src = vPC[2].u.operand;
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(src).getRegLabel());
        
            JSValue result = jsBoolean(!callFrame->r(src).jsValue().toBoolean());
            CHECK_FOR_EXCEPTION(dstLabel);
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = result;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            JSValue result = jsBoolean(!callFrame->r(src).jsValue().toBoolean());
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
            callFrame->uncheckedR(dst) = result;
        }
        
        vPC += OPCODE_LENGTH(op_not);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_check_has_instance) {
        /* check_has_instance constructor(r)
         
         Check 'constructor' is an object with the internal property
         [HasInstance] (i.e. is a function ... *shakes head sadly at
         JSC API*). Raises an exception if register constructor is not
         an valid parameter for instanceof.
         */
        int base = vPC[1].u.operand;
        JSValue baseVal = callFrame->r(base).jsValue();
        
        if (isInvalidParamForInstanceOf(callFrame, baseVal, exceptionValue)) {
            // IFC4BC - Setting the label for exceptionValue
            exceptionValue.setValueLabel(pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(base).getRegLabel()));
            // ------
            goto vm_throw;
        }
        
        vPC += OPCODE_LENGTH(op_check_has_instance);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_instanceof) {
        /* instanceof dst(r) value(r) constructor(r) constructorProto(r)
         
         Tests whether register value is an instance of register
         constructor, and puts the boolean result in register
         dst. Register constructorProto must contain the "prototype"
         property (not the actual prototype) of the object in
         register constructor. This lookup is separated so that
         polymorphic inline caching can apply.
         
         Raises an exception if register constructor is not an
         object.
         */
        int dst = vPC[1].u.operand;
        int value = vPC[2].u.operand;
        int base = vPC[3].u.operand;
        int baseProto = vPC[4].u.operand;
        
        JSValue val = callFrame->r(value).jsValue();
        JSValue basePro = callFrame->r(baseProto).jsValue();
        JSValue baseVal = callFrame->r(base).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(value).getRegLabel().Join(
                                callFrame->r(base).getRegLabel().Join(callFrame->r(baseProto).getRegLabel())));
        
            ASSERT(!isInvalidParamForInstanceOf(callFrame, baseVal, exceptionValue));
        
            bool result = asObject(baseVal)->methodTable()->hasInstance(asObject(baseVal), callFrame, val, basePro);
            // Original
            // bool result = asObject(baseVal)->methodTable()->hasInstance(asObject(baseVal), callFrame, callFrame->r(value).jsValue(), callFrame->r(baseProto).jsValue());
            CHECK_FOR_EXCEPTION(dstLabel);
        
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = jsBoolean(result);
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            ASSERT(!isInvalidParamForInstanceOf(callFrame, baseVal, exceptionValue));
            bool result = asObject(baseVal)->methodTable()->hasInstance(asObject(baseVal), callFrame, val, basePro);
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
            callFrame->uncheckedR(dst) = jsBoolean(result);
        }
        vPC += OPCODE_LENGTH(op_instanceof);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_typeof) {
        /* typeof dst(r) src(r)
         
         Determines the type string for src according to ECMAScript
         rules, and puts the result in register dst.
         */
        int dst = vPC[1].u.operand;
        int src = vPC[2].u.operand;
        
        if (labelReq && !isPolicy) {
            // IFC4BC - DNSU
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(src).getRegLabel());
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = JSValue(jsTypeStringForValue(callFrame, callFrame->r(src).jsValue()));
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = JSValue(jsTypeStringForValue(callFrame, callFrame->r(src).jsValue()));
        }
        vPC += OPCODE_LENGTH(op_typeof);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_is_undefined) {
        /* is_undefined dst(r) src(r)
         
         Determines whether the type string for src according to
         the ECMAScript rules is "undefined", and puts the result
         in register dst.
         */
        int dst = vPC[1].u.operand;
        int src = vPC[2].u.operand;
        JSValue v = callFrame->r(src).jsValue();
        if (labelReq && !isPolicy) {
            // IFC4BC - DNSU
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(src).getRegLabel());
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = jsBoolean(v.isCell() ? v.asCell()->structure()->typeInfo().masqueradesAsUndefined() : v.isUndefined());
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = jsBoolean(v.isCell() ? v.asCell()->structure()->typeInfo().masqueradesAsUndefined() : v.isUndefined());
        }
        vPC += OPCODE_LENGTH(op_is_undefined);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_is_boolean) {
        /* is_boolean dst(r) src(r)
         
         Determines whether the type string for src according to
         the ECMAScript rules is "boolean", and puts the result
         in register dst.
         */
        int dst = vPC[1].u.operand;
        int src = vPC[2].u.operand;
        if (labelReq && !isPolicy) {
            // IFC4BC - DNSU
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(src).getRegLabel());
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = jsBoolean(callFrame->r(src).jsValue().isBoolean());
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = jsBoolean(callFrame->r(src).jsValue().isBoolean());
        }
        vPC += OPCODE_LENGTH(op_is_boolean);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_is_number) {
        /* is_number dst(r) src(r)
         
         Determines whether the type string for src according to
         the ECMAScript rules is "number", and puts the result
         in register dst.
         */
        int dst = vPC[1].u.operand;
        int src = vPC[2].u.operand;
        if (labelReq && !isPolicy) {
            // IFC4BC - DNSU
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(src).getRegLabel());
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = jsBoolean(callFrame->r(src).jsValue().isNumber());
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = jsBoolean(callFrame->r(src).jsValue().isNumber());
        }
        vPC += OPCODE_LENGTH(op_is_number);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_is_string) {
        /* is_string dst(r) src(r)
         
         Determines whether the type string for src according to
         the ECMAScript rules is "string", and puts the result
         in register dst.
         */
        int dst = vPC[1].u.operand;
        int src = vPC[2].u.operand;
        if (labelReq && !isPolicy) {
            // IFC4BC - DNSU
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(src).getRegLabel());
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = jsBoolean(callFrame->r(src).jsValue().isString());
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = jsBoolean(callFrame->r(src).jsValue().isString());
        }
        vPC += OPCODE_LENGTH(op_is_string);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_is_object) {
        /* is_object dst(r) src(r)
         
         Determines whether the type string for src according to
         the ECMAScript rules is "object", and puts the result
         in register dst.
         */
        int dst = vPC[1].u.operand;
        int src = vPC[2].u.operand;
        if (labelReq && !isPolicy) {
            // IFC4BC - DNSU
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(src).getRegLabel());
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = jsBoolean(jsIsObjectType(callFrame->r(src).jsValue()));
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = jsBoolean(jsIsObjectType(callFrame->r(src).jsValue()));            
        }
        vPC += OPCODE_LENGTH(op_is_object);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_is_function) {
        /* is_function dst(r) src(r)
         
         Determines whether the type string for src according to
         the ECMAScript rules is "function", and puts the result
         in register dst.
         */
        int dst = vPC[1].u.operand;
        int src = vPC[2].u.operand;
        if (labelReq && !isPolicy) {
            // IFC4BC - DNSU
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(src).getRegLabel());
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = jsBoolean(jsIsFunctionType(callFrame->r(src).jsValue()));
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = jsBoolean(jsIsFunctionType(callFrame->r(src).jsValue()));
        }
        vPC += OPCODE_LENGTH(op_is_function);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_in) {
        /* in dst(r) property(r) base(r)
         
         Tests whether register base has a property named register
         property, and puts the boolean result in register dst.
         
         Raises an exception if register constructor is not an
         object.
         */
        int dst = vPC[1].u.operand;
        int property = vPC[2].u.operand;
        int base = vPC[3].u.operand;
        
        JSValue baseVal = callFrame->r(base).jsValue();
        JSValue propName = callFrame->r(property).jsValue();
        JSValue result;
        
        if (isInvalidParamForIn(callFrame, baseVal, exceptionValue)) {
            // IFC4BC - Setting the exception value label.
            exceptionValue.setValueLabel(callFrame->r(base).getRegLabel().Join(callFrame->r(property).getRegLabel()));
            goto vm_throw;
        }
        
        JSObject* baseObj = asObject(baseVal);
        
        // IFC4BC - Set the context and send it in hasProperty
        JSLabel context = pcLabel/*.Join(codeBlock->contextLabel)*/;
        
        uint32_t i;
        if (propName.getUInt32(i))
            result = jsBoolean(baseObj->hasPropertyIFC(callFrame, i, &context));
        else if (isName(propName))
            result = jsBoolean(baseObj->hasPropertyIFC(callFrame, jsCast<NameInstance*>(propName.asCell())->privateName(), &context));
        else {
            Identifier property(callFrame, propName.toString(callFrame)->value(callFrame));
        CHECK_FOR_EXCEPTION(context);
            result = jsBoolean(baseObj->hasPropertyIFC(callFrame, property, &context));
        }
        if (context.Val() != pcLabel/*.Join(codeBlock->contextLabel)*/.Val())
        {
            labelReq = true;
        }
        if (labelReq && !isPolicy) {
            // IFC4BC - NSU check
            JSLabel dstLabel = context.Join(callFrame->r(base).getRegLabel().Join(callFrame->r(property).getRegLabel()));
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = result;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = result;
        }
        vPC += OPCODE_LENGTH(op_in);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_resolve) {
        /* resolve dst(r) property(id)
         
         Looks up the property named by identifier property in the
         scope chain, and writes the resulting value to register
         dst. If the property is not found, raises an exception.
         */
        int dst = vPC[1].u.operand;
        bool isLabeled = false;
        if (labelReq && !isPolicy) {
            isLabeled = true;
        }
        if (UNLIKELY(!resolve(callFrame, vPC, exceptionValue, &labelReq)))
            goto vm_throw;
        if (labelReq && !isLabeled) {
            labelRegistersMinusDst (callFrame, codeBlock, pcLabel, dst);
        }
        vPC += OPCODE_LENGTH(op_resolve);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_resolve_skip) {
        /* resolve_skip dst(r) property(id) skip(n)
         
         Looks up the property named by identifier property in the
         scope chain skipping the top 'skip' levels, and writes the resulting
         value to register dst. If the property is not found, raises an exception.
         */
        int dst = vPC[1].u.operand;
        bool isLabeled = false;
        if (labelReq && !isPolicy) {
            isLabeled = true;
        }
        if (UNLIKELY(!resolveSkip(callFrame, vPC, exceptionValue, &labelReq)))
            goto vm_throw;
        if (labelReq && !isLabeled && !isPolicy) {
            labelRegistersMinusDst (callFrame, codeBlock, pcLabel, dst);
        }
        
        vPC += OPCODE_LENGTH(op_resolve_skip);
        
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_resolve_global) {
        /* resolve_skip dst(r) globalObject(c) property(id) structure(sID) offset(n)
         
         Performs a dynamic property lookup for the given property, on the provided
         global object.  If structure matches the Structure of the global then perform
         a fast lookup using the case offset, otherwise fall back to a full resolve and
         cache the new structure and offset
         */
        int dst = vPC[1].u.operand;
        bool isLabeled = false;
        if (labelReq && !isPolicy) {
            isLabeled = true;
        }
        if (UNLIKELY(!resolveGlobal(callFrame, vPC, exceptionValue, &labelReq)))
            goto vm_throw;
        if (labelReq && !isLabeled && !isPolicy) {
            labelRegistersMinusDst (callFrame, codeBlock, pcLabel, dst);
        }
        if (isPolicy)
        {
            isGlobalRVar = true;
            vIdent = codeBlock->identifier(vPC[2].u.operand);
            PropertySlot slot(codeBlock->globalObject());
            vValue = slot.slotBase().asCell();
        }
        vPC += OPCODE_LENGTH(op_resolve_global);
        
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_resolve_global_dynamic) {
        /* resolve_skip dst(r) globalObject(c) property(id) structure(sID) offset(n), depth(n)
         
         Performs a dynamic property lookup for the given property, on the provided
         global object.  If structure matches the Structure of the global then perform
         a fast lookup using the case offset, otherwise fall back to a full resolve and
         cache the new structure and offset.
         
         This walks through n levels of the scope chain to verify that none of those levels
         in the scope chain include dynamically added properties.
         */
        int dst = vPC[1].u.operand;
        bool isLabeled = false;
        if (labelReq && !isPolicy) {
            isLabeled = true;
        }
        if (UNLIKELY(!resolveGlobalDynamic(callFrame, vPC, exceptionValue, &labelReq)))
            goto vm_throw;
        if (labelReq && !isLabeled && !isPolicy) {
            labelRegistersMinusDst (callFrame, codeBlock, pcLabel, dst);
        }
        
        vPC += OPCODE_LENGTH(op_resolve_global_dynamic);
        
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_get_global_var) {
        /* get_global_var dst(r) globalObject(c) registerPointer(n)
         
         Gets the global var at global slot index and places it in register dst.
         */
        int dst = vPC[1].u.operand;
        WriteBarrier<Unknown>* registerPointer = vPC[2].u.registerPointer;
        
        // IFC4BC
        JSValue rVal = registerPointer->get();
        // For global objects with label 0, it would be the pcLabel and hence proceed properly.
        // rVal.setValueLabel(rVal.joinValueLabel(pcLabel));

        if (isPolicy) {
            isGlobalVar = true;
            rPointer = vPC[2].u.registerPointer;
        }
        
        if (rVal.getValueLabel().Val() && rVal.getValueLabel() != pcLabel/*.Join(codeBlock->contextLabel)*/ && !labelReq) {
            labelReq = true;
            labelRegisters (callFrame, codeBlock, pcLabel);
        }
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(rVal.getValueLabel());
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = rVal;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = rVal;
        }
        //---
        // Original
        // callFrame->uncheckedR(dst) = registerPointer->get();
        
        vPC += OPCODE_LENGTH(op_get_global_var);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_get_global_var_watchable) {
        /* get_global_var_watchable dst(r) globalObject(c) registerPointer(n)
         
         Gets the global var at global slot index and places it in register dst.
         */
        int dst = vPC[1].u.operand;
        WriteBarrier<Unknown>* registerPointer = vPC[2].u.registerPointer;
        // IFC4BC
        JSValue rVal = registerPointer->get();
        // For global objects with label 0, it would be the pcLabel and hence proceed properly.
        // rVal.setValueLabel(rVal.joinValueLabel(pcLabel));
        if (rVal.getValueLabel().Val() && rVal.getValueLabel() != pcLabel/*.Join(codeBlock->contextLabel)*/ && !labelReq) {
            labelReq = true;
            labelRegisters (callFrame, codeBlock, pcLabel);
        }
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(rVal.getValueLabel());
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = rVal;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = rVal;        
        }
        //---
        // Original
        // callFrame->uncheckedR(dst) = registerPointer->get();
        vPC += OPCODE_LENGTH(op_get_global_var_watchable);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_put_global_var) {
        /* put_global_var globalObject(c) registerPointer(n) value(r)
         
         Puts value into global slot index.
         */
        JSGlobalObject* scope = codeBlock->globalObject();
        ASSERT(scope->isGlobalObject());
        WriteBarrier<Unknown>* registerPointer = vPC[1].u.registerPointer;
        int value = vPC[2].u.operand;
        
        // IFC4BC - NSU
                // IFC4BC - We allow partial leaks in the heap now
//        if (!pcLabel.NSU(registerPointer->get().getValueLabel())){
//            ABORT_TRANSACTION();
//        }
        JSLabel dstLabel = pcLabel;
        if (!noSensitiveUpgrade(registerPointer->get().getValueLabel())){
            printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, registerPointer->get().getValueLabel().Val(), pcLabel.Val());
            dstLabel.setStar(true);
        }
        
        JSValue val = callFrame->r(value).jsValue();
        // JSLabel lbl = pcLabel/*.Join(codeBlock->contextLabel)*/;
        if (labelReq && !isPolicy) {
            dstLabel = dstLabel.Join(val.getValueLabel());
//            if (lbl.Star()){
//                ABORT_TRANSACTION();
//            }
        }
        
        val.setValueLabel(dstLabel);
        registerPointer->set(*globalData, scope, val);
        //----------------------
        // Original
        // registerPointer->set(*globalData, scope, callFrame->r(value).jsValue());
        vPC += OPCODE_LENGTH(op_put_global_var);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_put_global_var_check) {
        /* put_global_var_check globalObject(c) registerPointer(n) value(r)
         
         Puts value into global slot index. In JIT configurations this will
         perform a watchpoint check. If we're running with the old interpreter,
         this is not necessary; the interpreter never uses these watchpoints.
         */
        JSGlobalObject* scope = codeBlock->globalObject();
        ASSERT(scope->isGlobalObject());
        WriteBarrier<Unknown>* registerPointer = vPC[1].u.registerPointer;
        int value = vPC[2].u.operand;

        // IFC4BC - NSU
//        if (!pcLabel.NSU(registerPointer->get().getValueLabel())){
//            ABORT_TRANSACTION();
//        }
        
        JSLabel dstLabel = pcLabel;
        if (!noSensitiveUpgrade(registerPointer->get().getValueLabel())){
            printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, registerPointer->get().getValueLabel().Val(), pcLabel.Val());
            dstLabel.setStar(true);
        }
        JSValue val = callFrame->r(value).jsValue();
        // JSLabel lbl = pcLabel/*.Join(codeBlock->contextLabel)*/;
        if (labelReq && !isPolicy) {
            dstLabel = dstLabel.Join(val.getValueLabel());
//            if (lbl.Star()){
//                ABORT_TRANSACTION();
//            }
        }
        val.setValueLabel(dstLabel);
        registerPointer->set(*globalData, scope, val);
        //----------------------
        // Original
        // registerPointer->set(*globalData, scope, callFrame->r(value).jsValue());
        vPC += OPCODE_LENGTH(op_put_global_var_check);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_get_scoped_var) {
        /* get_scoped_var dst(r) index(n) skip(n)
         
         Loads the contents of the index-th local from the scope skip nodes from
         the top of the scope chain, and places it in register dst.
         */
        int dst = vPC[1].u.operand;
        int index = vPC[2].u.operand;
        int skip = vPC[3].u.operand;
        
        //IFC4BC
        JSLabel increasingContextLabel = pcLabel;
        
        ScopeChainNode* scopeChain = callFrame->scopeChain();
        ScopeChainIterator iter = scopeChain->begin();
        ScopeChainIterator end = scopeChain->end();
        ASSERT_UNUSED(end, iter != end);
        ASSERT(codeBlock == callFrame->codeBlock());
        bool checkTopLevel = codeBlock->codeType() == FunctionCode && codeBlock->needsFullScopeChain();
        ASSERT(skip || !checkTopLevel);
        if (checkTopLevel && skip--) {
            //IFC4BC
            if (callFrame->r(codeBlock->activationRegister()).jsValue()){
                increasingContextLabel = increasingContextLabel.Join(iter.getCurrentNode()->scopeNextLabel);
                increasingContextLabel = increasingContextLabel.Join(iter->get()->getObjectLabel());
                ++iter;
            }
            //-------
            // Original
            // if (callFrame->r(codeBlock->activationRegister()).jsValue())
            //     ++iter;
        }
        while (skip--) {
            //IFC4BC
            increasingContextLabel = increasingContextLabel.Join(iter.getCurrentNode()->scopeNextLabel);
            increasingContextLabel = increasingContextLabel.Join(iter->get()->getObjectLabel());
            //------
            ++iter;
            ASSERT_UNUSED(end, iter != end);
        }
        ASSERT((*iter)->isVariableObject());
        JSVariableObject* scope = jsCast<JSVariableObject*>(iter->get());
        //IFC4BC
        JSValue ret = scope->registerAt(index).get();
        increasingContextLabel = increasingContextLabel.Join(scope->getObjectLabel());
        if (increasingContextLabel != pcLabel && !labelReq) {
            labelReq = true;
            labelRegisters (callFrame, codeBlock, pcLabel);
        }

        if (labelReq && !isPolicy) {
            JSLabel dstLabel = ret.joinValueLabel(increasingContextLabel);
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = ret;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = ret;   
        }
        //------
        // Original
        // callFrame->uncheckedR(dst) = scope->registerAt(index).get();
        ASSERT(callFrame->r(dst).jsValue());
        vPC += OPCODE_LENGTH(op_get_scoped_var);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_put_scoped_var) {
        /* put_scoped_var index(n) skip(n) value(r)
         
         */
        int index = vPC[1].u.operand;
        int skip = vPC[2].u.operand;
        int value = vPC[3].u.operand;
        
        //IFC4BC
        JSLabel increasingContextLabel = pcLabel;
        //------
        
        ScopeChainNode* scopeChain = callFrame->scopeChain();
        ScopeChainIterator iter = scopeChain->begin();
        ScopeChainIterator end = scopeChain->end();
        ASSERT(codeBlock == callFrame->codeBlock());
        ASSERT_UNUSED(end, iter != end);
        bool checkTopLevel = codeBlock->codeType() == FunctionCode && codeBlock->needsFullScopeChain();
        ASSERT(skip || !checkTopLevel);
        if (checkTopLevel && skip--) {
            //IFC4BC
            if (callFrame->r(codeBlock->activationRegister()).jsValue()){
                increasingContextLabel = increasingContextLabel.Join(iter.getCurrentNode()->scopeNextLabel);
                increasingContextLabel = increasingContextLabel.Join(iter->get()->getObjectLabel());
                ++iter;
            }
            //-------
            // Original
            // if (callFrame->r(codeBlock->activationRegister()).jsValue())
            //     ++iter;
        }
        while (skip--) {
            //IFC4BC
            increasingContextLabel = increasingContextLabel.Join(iter.getCurrentNode()->scopeNextLabel);
            increasingContextLabel = increasingContextLabel.Join(iter->get()->getObjectLabel());
            //------
            ++iter;
            ASSERT_UNUSED(end, iter != end);
        }
        
        ASSERT((*iter)->isVariableObject());
        JSVariableObject* scope = jsCast<JSVariableObject*>(iter->get());
        ASSERT(callFrame->r(value).jsValue());
        // IFC4BC
        increasingContextLabel = increasingContextLabel.Join(scope->getObjectLabel());
        JSValue ret = callFrame->r(value).jsValue();
        ret.setValueLabel(ret.joinValueLabel(increasingContextLabel));
        scope->registerAt(index).set(*globalData, scope, ret);
        // ------
        // Original
        // scope->registerAt(index).set(*globalData, scope, callFrame->r(value).jsValue());
        vPC += OPCODE_LENGTH(op_put_scoped_var);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_resolve_base) {
        /* resolve_base dst(r) property(id) isStrict(bool)
         
         Searches the scope chain for an object containing
         identifier property, and if one is found, writes it to
         register dst. If none is found and isStrict is false, the
         outermost scope (which will be the global object) is
         stored in register dst.
         */
        // IFC4BC -- NSU check
        int dst = vPC[1].u.operand;
        bool isLabeled = false;
        if (labelReq && !isPolicy) {
            isLabeled = true;
        }
        resolveBase(callFrame, vPC, &labelReq);
        if (labelReq && !isLabeled && !isPolicy) {
            labelRegistersMinusDst (callFrame, codeBlock, pcLabel, dst);
        }
        
        CHECK_FOR_EXCEPTION(callFrame->globalData().exception.getValueLabel());
        
        vPC += OPCODE_LENGTH(op_resolve_base);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_ensure_property_exists) {
        /* ensure_property_exists base(r) property(id)
         
         Throws an exception if property does not exist on base
         */
        int base = vPC[1].u.operand;
        int property = vPC[2].u.operand;
        Identifier& ident = codeBlock->identifier(property);
        
        JSValue baseVal = callFrame->r(base).jsValue();
        JSObject* baseObject = asObject(baseVal);
        // IFC4BC - Set the context label
        JSLabel contextLabel = pcLabel;
        PropertySlot slot(baseVal);
        if (!baseObject->getPropertySlotIFC(callFrame, ident, slot, &contextLabel)) {
            exceptionValue = createErrorForInvalidGlobalAssignment(callFrame, ident.ustring());
            // IFC4BC - Set the exception label
            exceptionValue.setValueLabel(contextLabel.Join(baseObject->getObjectLabel()));
            goto vm_throw;
        }
        
        vPC += OPCODE_LENGTH(op_ensure_property_exists);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_resolve_with_base) {
        /* resolve_with_base baseDst(r) propDst(r) property(id)
         
         Searches the scope chain for an object containing
         identifier property, and if one is found, writes it to
         register srcDst, and the retrieved property value to register
         propDst. If the property is not found, raises an exception.
         
         This is more efficient than doing resolve_base followed by
         resolve, or resolve_base followed by get_by_id, as it
         avoids duplicate hash lookups.
         */
        // IFC4BC -- NSU check
        int bdst = vPC[1].u.operand;
        int pdst = vPC[2].u.operand;
        bool isLabeled = false;
        if (labelReq && !isPolicy) {
            isLabeled = true;
        }
        if (UNLIKELY(!resolveBaseAndProperty(callFrame, vPC, exceptionValue, &labelReq)))
            goto vm_throw;
        if (labelReq && !isLabeled && !isPolicy) {
            for (int i = 0; i < codeBlock->m_numCalleeRegisters; i++)
                if (i != bdst && i != pdst)
                    callFrame->uncheckedR(i).setRegLabel(pcLabel);
            for(int i = -7, j = 1; j <= codeBlock->numParameters(); j++, i--)
                callFrame->uncheckedR(i).setRegLabel(pcLabel);
        }
        vPC += OPCODE_LENGTH(op_resolve_with_base);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_resolve_with_this) {
        /* resolve_with_this thisDst(r) propDst(r) property(id)
         
         Searches the scope chain for an object containing
         identifier property, and if one is found, writes the
         retrieved property value to register propDst, and the
         this object to pass in a call to thisDst.
         
         If the property is not found, raises an exception.
         */
        // IFC4BC -- NSU check
        int tdst = vPC[1].u.operand;
        int pdst = vPC[2].u.operand;
        bool isLabeled = false;
        if (labelReq && !isPolicy) {
            isLabeled = true;
        }
        if (UNLIKELY(!resolveThisAndProperty(callFrame, vPC, exceptionValue, &labelReq)))
            goto vm_throw;
        if (labelReq && !isLabeled && !isPolicy) {
            for (int i = 0; i < codeBlock->m_numCalleeRegisters; i++)
                if (i != tdst && i != pdst)
                    callFrame->uncheckedR(i).setRegLabel(pcLabel);
            for(int i = -7, j = 1; j <= codeBlock->numParameters(); j++, i--)
                callFrame->uncheckedR(i).setRegLabel(pcLabel);
        }
        
        vPC += OPCODE_LENGTH(op_resolve_with_this);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_get_by_id_out_of_line)
    DEFINE_OPCODE(op_get_by_id) {
        /* get_by_id dst(r) base(r) property(id) structure(sID) nop(n) nop(n) nop(n)
         
         Generic property access: Gets the property named by identifier
         property from the value base, and puts the result in register dst.
         */
        int dst = vPC[1].u.operand;
        int base = vPC[2].u.operand;
        int property = vPC[3].u.operand;
        
        Identifier& ident = codeBlock->identifier(property);
        JSValue baseValue = callFrame->r(base).jsValue();
        PropertySlot slot(baseValue);
        
        if (isPolicy && isGlobalVar) // Did the policy set the label for global variable?
        {
            isGlobalVar = false;
            if (strcmp(ident.ustring().utf8().data(),"setLabel") == 0) // If yes then set the value label here.
            {
                isSetLabel = true;
            }
        }
        else if (isPolicy && isGlobalRVar)
        {
            isGlobalRVar = false;
            if (strcmp(ident.ustring().utf8().data(),"setLabel") == 0) // If yes then set the value label here.
            {
                isSetLabel = true;
            }
        }
        
        // IFC4BC
        JSLabel context = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(base).getRegLabel());
        JSValue result = baseValue.getIFC(callFrame, ident, slot, &context);
        // result.setValueLabel(result.joinValueLabel(baseValue.getValueLabel()));
        context = context.Join(result.getValueLabel());
        if (JSLabel::ABORT_FLAG) {
            JSLabel::ABORT_FLAG = false;
            // ABORT_TRANSACTION();
        }
        CHECK_FOR_EXCEPTION(context);
        if (context.Val() != pcLabel.Val() && !labelReq) {
            labelReq = true;
            labelRegisters (callFrame, codeBlock, pcLabel);
        }
        if (labelReq && !isPolicy) {
            // context.setStar(false);
            JSLabel dstLabel = context;
            
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else
            {
                // dstLabel.setStar(false);
            }
            callFrame->uncheckedR(dst) = result;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = result;
        }
        // Original
        // JSValue result = baseValue.get(callFrame, ident, slot);
        
        // IFC4BC - Do not cache, so other opcodes might nt be used
        // tryCacheGetByID(callFrame, codeBlock, vPC, baseValue, ident, slot);

        vPC += OPCODE_LENGTH(op_get_by_id);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_get_by_id_self) {
        /* op_get_by_id_self dst(r) base(r) property(id) structure(sID) offset(n) nop(n) nop(n)
         
         Cached property access: Attempts to get a cached property from the
         value base. If the cache misses, op_get_by_id_self reverts to
         op_get_by_id.
         */
        int base = vPC[2].u.operand;
        JSValue baseValue = callFrame->r(base).jsValue();
        
        if (LIKELY(baseValue.isCell())) {
            JSCell* baseCell = baseValue.asCell();
            Structure* structure = vPC[4].u.structure.get();
            
            if (LIKELY(baseCell->structure() == structure)) {
                ASSERT(baseCell->isObject());
                JSObject* baseObject = asObject(baseCell);
                int dst = vPC[1].u.operand;
                int offset = vPC[5].u.operand;
                
                ASSERT(baseObject->get(callFrame, codeBlock->identifier(vPC[3].u.operand)) == baseObject->getDirectOffset(offset));
                callFrame->uncheckedR(dst) = JSValue(baseObject->getDirectOffset(offset));
                
                vPC += OPCODE_LENGTH(op_get_by_id_self);
                 NEXT_INSTRUCTION();
            }
        }
        
        uncacheGetByID(codeBlock, vPC);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_get_by_id_proto) {
        /* op_get_by_id_proto dst(r) base(r) property(id) structure(sID) prototypeStructure(sID) offset(n) nop(n)
         
         Cached property access: Attempts to get a cached property from the
         value base's prototype. If the cache misses, op_get_by_id_proto
         reverts to op_get_by_id.
         */
        int base = vPC[2].u.operand;
        JSValue baseValue = callFrame->r(base).jsValue();
        
        if (LIKELY(baseValue.isCell())) {
            JSCell* baseCell = baseValue.asCell();
            Structure* structure = vPC[4].u.structure.get();
            
            if (LIKELY(baseCell->structure() == structure)) {
                ASSERT(structure->prototypeForLookup(callFrame).isObject());
                JSObject* protoObject = asObject(structure->prototypeForLookup(callFrame));
                Structure* prototypeStructure = vPC[5].u.structure.get();
                
                if (LIKELY(protoObject->structure() == prototypeStructure)) {
                    int dst = vPC[1].u.operand;
                    int offset = vPC[6].u.operand;
                    
                    ASSERT(protoObject->get(callFrame, codeBlock->identifier(vPC[3].u.operand)) == protoObject->getDirectOffset(offset));
                    ASSERT(baseValue.get(callFrame, codeBlock->identifier(vPC[3].u.operand)) == protoObject->getDirectOffset(offset));
                    callFrame->uncheckedR(dst) = JSValue(protoObject->getDirectOffset(offset));
                    
                    vPC += OPCODE_LENGTH(op_get_by_id_proto);
                     NEXT_INSTRUCTION();
                }
            }
        }
        
        uncacheGetByID(codeBlock, vPC);
         NEXT_INSTRUCTION();
    }
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
    goto *(&&skip_id_getter_proto);
#endif
    DEFINE_OPCODE(op_get_by_id_getter_proto) {
        /* op_get_by_id_getter_proto dst(r) base(r) property(id) structure(sID) prototypeStructure(sID) offset(n) nop(n)
         
         Cached property access: Attempts to get a cached getter property from the
         value base's prototype. If the cache misses, op_get_by_id_getter_proto
         reverts to op_get_by_id.
         */
        int base = vPC[2].u.operand;
        JSValue baseValue = callFrame->r(base).jsValue();
        
        if (LIKELY(baseValue.isCell())) {
            JSCell* baseCell = baseValue.asCell();
            Structure* structure = vPC[4].u.structure.get();
            
            if (LIKELY(baseCell->structure() == structure)) {
                ASSERT(structure->prototypeForLookup(callFrame).isObject());
                JSObject* protoObject = asObject(structure->prototypeForLookup(callFrame));
                Structure* prototypeStructure = vPC[5].u.structure.get();
                
                if (LIKELY(protoObject->structure() == prototypeStructure)) {
                    int dst = vPC[1].u.operand;
                    int offset = vPC[6].u.operand;
                    if (GetterSetter* getterSetter = asGetterSetter(protoObject->getDirectOffset(offset).asCell())) {
                        JSObject* getter = getterSetter->getter();
                        CallData callData;
                        CallType callType = getter->methodTable()->getCallData(getter, callData);
                        JSValue result = call(callFrame, getter, callType, callData, asObject(baseCell), ArgList());
                        CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                        callFrame->uncheckedR(dst) = result;
                    } else
                        callFrame->uncheckedR(dst) = jsUndefined();
                    vPC += OPCODE_LENGTH(op_get_by_id_getter_proto);
                     NEXT_INSTRUCTION();
                }
            }
        }
        uncacheGetByID(codeBlock, vPC);
         NEXT_INSTRUCTION();
    }
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
skip_id_getter_proto:
#endif
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
    goto *(&&skip_id_custom_proto);
#endif
    DEFINE_OPCODE(op_get_by_id_custom_proto) {
        /* op_get_by_id_custom_proto dst(r) base(r) property(id) structure(sID) prototypeStructure(sID) offset(n) nop(n)
         
         Cached property access: Attempts to use a cached named property getter
         from the value base's prototype. If the cache misses, op_get_by_id_custom_proto
         reverts to op_get_by_id.
         */
        int base = vPC[2].u.operand;
        JSValue baseValue = callFrame->r(base).jsValue();
        
        if (LIKELY(baseValue.isCell())) {
            JSCell* baseCell = baseValue.asCell();
            Structure* structure = vPC[4].u.structure.get();
            
            if (LIKELY(baseCell->structure() == structure)) {
                ASSERT(structure->prototypeForLookup(callFrame).isObject());
                JSObject* protoObject = asObject(structure->prototypeForLookup(callFrame));
                Structure* prototypeStructure = vPC[5].u.structure.get();
                
                if (LIKELY(protoObject->structure() == prototypeStructure)) {
                    int dst = vPC[1].u.operand;
                    int property = vPC[3].u.operand;
                    Identifier& ident = codeBlock->identifier(property);
                    
                    PropertySlot::GetValueFunc getter = vPC[6].u.getterFunc;
                    JSValue result = getter(callFrame, protoObject, ident);
                    CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                    callFrame->uncheckedR(dst) = result;
                    vPC += OPCODE_LENGTH(op_get_by_id_custom_proto);
                     NEXT_INSTRUCTION();
                }
            }
        }
        uncacheGetByID(codeBlock, vPC);
         NEXT_INSTRUCTION();
    }
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
skip_id_custom_proto:
#endif
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
    goto *(&&skip_get_by_id_chain);
#endif
    DEFINE_OPCODE(op_get_by_id_chain) {
        /* op_get_by_id_chain dst(r) base(r) property(id) structure(sID) structureChain(chain) count(n) offset(n)
         
         Cached property access: Attempts to get a cached property from the
         value base's prototype chain. If the cache misses, op_get_by_id_chain
         reverts to op_get_by_id.
         */
        int base = vPC[2].u.operand;
        JSValue baseValue = callFrame->r(base).jsValue();
        
        if (LIKELY(baseValue.isCell())) {
            JSCell* baseCell = baseValue.asCell();
            Structure* structure = vPC[4].u.structure.get();
            
            if (LIKELY(baseCell->structure() == structure)) {
                WriteBarrier<Structure>* it = vPC[5].u.structureChain->head();
                size_t count = vPC[6].u.operand;
                WriteBarrier<Structure>* end = it + count;
                
                while (true) {
                    JSObject* baseObject = asObject(baseCell->structure()->prototypeForLookup(callFrame));
                    
                    if (UNLIKELY(baseObject->structure() != (*it).get()))
                        break;
                    
                    if (++it == end) {
                        int dst = vPC[1].u.operand;
                        int offset = vPC[7].u.operand;
                        
                        ASSERT(baseObject->get(callFrame, codeBlock->identifier(vPC[3].u.operand)) == baseObject->getDirectOffset(offset));
                        ASSERT(baseValue.get(callFrame, codeBlock->identifier(vPC[3].u.operand)) == baseObject->getDirectOffset(offset));
                        callFrame->uncheckedR(dst) = JSValue(baseObject->getDirectOffset(offset));
                        
                        vPC += OPCODE_LENGTH(op_get_by_id_chain);
                         NEXT_INSTRUCTION();
                    }
                    
                    // Update baseCell, so that next time around the loop we'll pick up the prototype's prototype.
                    baseCell = baseObject;
                }
            }
        }
        
        uncacheGetByID(codeBlock, vPC);
         NEXT_INSTRUCTION();
    }
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
skip_get_by_id_chain:
    goto *(&&skip_id_getter_self);
#endif
    DEFINE_OPCODE(op_get_by_id_getter_self) {
        /* op_get_by_id_self dst(r) base(r) property(id) structure(sID) offset(n) nop(n) nop(n)
         
         Cached property access: Attempts to get a cached property from the
         value base. If the cache misses, op_get_by_id_getter_self reverts to
         op_get_by_id.
         */
        int base = vPC[2].u.operand;
        JSValue baseValue = callFrame->r(base).jsValue();
        
        if (LIKELY(baseValue.isCell())) {
            JSCell* baseCell = baseValue.asCell();
            Structure* structure = vPC[4].u.structure.get();
            
            if (LIKELY(baseCell->structure() == structure)) {
                ASSERT(baseCell->isObject());
                JSObject* baseObject = asObject(baseCell);
                int dst = vPC[1].u.operand;
                int offset = vPC[5].u.operand;
                
                if (GetterSetter* getterSetter = asGetterSetter(baseObject->getDirectOffset(offset).asCell())) {
                    JSObject* getter = getterSetter->getter();
                    CallData callData;
                    CallType callType = getter->methodTable()->getCallData(getter, callData);
                    JSValue result = call(callFrame, getter, callType, callData, baseObject, ArgList());
                    CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                    callFrame->uncheckedR(dst) = result;
                } else
                    callFrame->uncheckedR(dst) = jsUndefined();
                
                vPC += OPCODE_LENGTH(op_get_by_id_getter_self);
                 NEXT_INSTRUCTION();
            }
        }
        uncacheGetByID(codeBlock, vPC);
         NEXT_INSTRUCTION();
    }
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
skip_id_getter_self:
#endif
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
    goto *(&&skip_id_custom_self);
#endif
    DEFINE_OPCODE(op_get_by_id_custom_self) {
        /* op_get_by_id_custom_self dst(r) base(r) property(id) structure(sID) offset(n) nop(n) nop(n)
         
         Cached property access: Attempts to use a cached named property getter
         from the value base. If the cache misses, op_get_by_id_custom_self reverts to
         op_get_by_id.
         */
        int base = vPC[2].u.operand;
        JSValue baseValue = callFrame->r(base).jsValue();
        
        if (LIKELY(baseValue.isCell())) {
            JSCell* baseCell = baseValue.asCell();
            Structure* structure = vPC[4].u.structure.get();
            
            if (LIKELY(baseCell->structure() == structure)) {
                ASSERT(baseCell->isObject());
                int dst = vPC[1].u.operand;
                int property = vPC[3].u.operand;
                Identifier& ident = codeBlock->identifier(property);
                
                PropertySlot::GetValueFunc getter = vPC[5].u.getterFunc;
                JSValue result = getter(callFrame, baseValue, ident);
                CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                callFrame->uncheckedR(dst) = result;
                vPC += OPCODE_LENGTH(op_get_by_id_custom_self);
                 NEXT_INSTRUCTION();
            }
        }
        uncacheGetByID(codeBlock, vPC);
         NEXT_INSTRUCTION();
    }
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
skip_id_custom_self:
#endif
    DEFINE_OPCODE(op_get_by_id_generic) {
        /* op_get_by_id_generic dst(r) base(r) property(id) nop(sID) nop(n) nop(n) nop(n)
         
         Generic property access: Gets the property named by identifier
         property from the value base, and puts the result in register dst.
         */
        int dst = vPC[1].u.operand;
        int base = vPC[2].u.operand;
        int property = vPC[3].u.operand;
        
        Identifier& ident = codeBlock->identifier(property);
        JSValue baseValue = callFrame->r(base).jsValue();
        PropertySlot slot(baseValue);
        
        // IFC4BC
        JSLabel context = pcLabel.Join(callFrame->r(base).getRegLabel());
        JSValue result = baseValue.getIFC(callFrame, ident, slot, &context);
        context = context.Join(result.getValueLabel());
        if (JSLabel::ABORT_FLAG) {
            JSLabel::ABORT_FLAG = false;
            // ABORT_TRANSACTION();
        }
        CHECK_FOR_EXCEPTION(context);
        if (context.Val() != pcLabel.Val() && !labelReq) {
            labelReq = true;
            labelRegisters (callFrame, codeBlock, pcLabel);
        }
        if (labelReq && !isPolicy) {
            // context.setStar(false);
            JSLabel dstLabel = context;
            
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else
            {
                // dstLabel.setStar(false);
            }
            callFrame->uncheckedR(dst) = result;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = result;
        }

        vPC += OPCODE_LENGTH(op_get_by_id_generic);
         NEXT_INSTRUCTION();
    }
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
    goto *(&&skip_id_getter_chain);
#endif
    DEFINE_OPCODE(op_get_by_id_getter_chain) {
        /* op_get_by_id_getter_chain dst(r) base(r) property(id) structure(sID) structureChain(chain) count(n) offset(n)
         
         Cached property access: Attempts to get a cached property from the
         value base's prototype chain. If the cache misses, op_get_by_id_getter_chain
         reverts to op_get_by_id.
         */
        int base = vPC[2].u.operand;
        JSValue baseValue = callFrame->r(base).jsValue();
        
        if (LIKELY(baseValue.isCell())) {
            JSCell* baseCell = baseValue.asCell();
            Structure* structure = vPC[4].u.structure.get();
            
            if (LIKELY(baseCell->structure() == structure)) {
                WriteBarrier<Structure>* it = vPC[5].u.structureChain->head();
                size_t count = vPC[6].u.operand;
                WriteBarrier<Structure>* end = it + count;
                
                while (true) {
                    JSObject* baseObject = asObject(baseCell->structure()->prototypeForLookup(callFrame));
                    
                    if (UNLIKELY(baseObject->structure() != (*it).get()))
                        break;
                    
                    if (++it == end) {
                        int dst = vPC[1].u.operand;
                        int offset = vPC[7].u.operand;
                        if (GetterSetter* getterSetter = asGetterSetter(baseObject->getDirectOffset(offset).asCell())) {
                            JSObject* getter = getterSetter->getter();
                            CallData callData;
                            CallType callType = getter->methodTable()->getCallData(getter, callData);
                            JSValue result = call(callFrame, getter, callType, callData, baseValue, ArgList());
                            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
                            callFrame->uncheckedR(dst) = result;
                        } else
                            callFrame->uncheckedR(dst) = jsUndefined();
                        vPC += OPCODE_LENGTH(op_get_by_id_getter_chain);
                         NEXT_INSTRUCTION();
                    }
                    
                    // Update baseCell, so that next time around the loop we'll pick up the prototype's prototype.
                    baseCell = baseObject;
                }
            }
        }
        uncacheGetByID(codeBlock, vPC);
         NEXT_INSTRUCTION();
    }
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
skip_id_getter_chain:
#endif
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
    goto *(&&skip_id_custom_chain);
#endif
    DEFINE_OPCODE(op_get_by_id_custom_chain) {
        /* op_get_by_id_custom_chain dst(r) base(r) property(id) structure(sID) structureChain(chain) count(n) offset(n)
         
         Cached property access: Attempts to use a cached named property getter on the
         value base's prototype chain. If the cache misses, op_get_by_id_custom_chain
         reverts to op_get_by_id.
         */
        int base = vPC[2].u.operand;
        JSValue baseValue = callFrame->r(base).jsValue();
        
        if (LIKELY(baseValue.isCell())) {
            JSCell* baseCell = baseValue.asCell();
            Structure* structure = vPC[4].u.structure.get();
            
            if (LIKELY(baseCell->structure() == structure)) {
                WriteBarrier<Structure>* it = vPC[5].u.structureChain->head();
                size_t count = vPC[6].u.operand;
                WriteBarrier<Structure>* end = it + count;
                
                while (true) {
                    JSObject* baseObject = asObject(baseCell->structure()->prototypeForLookup(callFrame));
                    
                    if (UNLIKELY(baseObject->structure() != (*it).get()))
                        break;
                    
                    if (++it == end) {
                        int dst = vPC[1].u.operand;
                        int property = vPC[3].u.operand;
                        Identifier& ident = codeBlock->identifier(property);
                        
                        PropertySlot::GetValueFunc getter = vPC[7].u.getterFunc;
                        JSValue result = getter(callFrame, baseObject, ident);
                        CHECK_FOR_EXCEPTION(pcLabel);
                        callFrame->uncheckedR(dst) = result;
                        vPC += OPCODE_LENGTH(op_get_by_id_custom_chain);
                         NEXT_INSTRUCTION();
                    }
                    
                    // Update baseCell, so that next time around the loop we'll pick up the prototype's prototype.
                    baseCell = baseObject;
                }
            }
        }
        uncacheGetByID(codeBlock, vPC);
         NEXT_INSTRUCTION();
    }
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
skip_id_custom_chain:
    goto *(&&skip_get_array_length);
#endif
    DEFINE_OPCODE(op_get_array_length) {
        /* op_get_array_length dst(r) base(r) property(id) nop(sID) nop(n) nop(n) nop(n)
         
         Cached property access: Gets the length of the array in register base,
         and puts the result in register dst. If register base does not hold
         an array, op_get_array_length reverts to op_get_by_id.
         */
        
        int base = vPC[2].u.operand;
        JSValue baseValue = callFrame->r(base).jsValue();
        if (LIKELY(isJSArray(baseValue))) {
            int dst = vPC[1].u.operand;
            callFrame->uncheckedR(dst) = jsNumber(asArray(baseValue)->length());
            vPC += OPCODE_LENGTH(op_get_array_length);
             NEXT_INSTRUCTION();
        }
        
        uncacheGetByID(codeBlock, vPC);
         NEXT_INSTRUCTION();
    }
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
skip_get_array_length:
    goto *(&&skip_get_string_length);
#endif
    DEFINE_OPCODE(op_get_string_length) {
        /* op_get_string_length dst(r) base(r) property(id) nop(sID) nop(n) nop(n) nop(n)
         
         Cached property access: Gets the length of the string in register base,
         and puts the result in register dst. If register base does not hold
         a string, op_get_string_length reverts to op_get_by_id.
         */
        
        int base = vPC[2].u.operand;
        JSValue baseValue = callFrame->r(base).jsValue();
        if (LIKELY(isJSString(baseValue))) {
            int dst = vPC[1].u.operand;
            callFrame->uncheckedR(dst) = jsNumber(asString(baseValue)->length());
            vPC += OPCODE_LENGTH(op_get_string_length);
             NEXT_INSTRUCTION();
        }
        
        uncacheGetByID(codeBlock, vPC);
         NEXT_INSTRUCTION();
    }
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
skip_get_string_length:
    goto *(&&skip_put_by_id);
#endif
    DEFINE_OPCODE(op_put_by_id_out_of_line)
    DEFINE_OPCODE(op_put_by_id) {
        /* put_by_id base(r) property(id) value(r) nop(n) nop(n) nop(n) nop(n) direct(b)
         
         Generic property access: Sets the property named by identifier
         property, belonging to register base, to register value.
         
         Unlike many opcodes, this one does not write any output to
         the register file.
         
         The "direct" flag should only be set this put_by_id is to initialize
         an object literal.
         */
        
        int base = vPC[1].u.operand;
        int property = vPC[2].u.operand;
        int value = vPC[3].u.operand;
        int direct = vPC[8].u.operand;
        // IFC4BC - Set the flag for aborting the run if NSU fails in putIFC
        bool abortRun = false;
        bool isStructChanged = false;
        JSLabel sentContextLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
        // ------
        JSValue baseValue = callFrame->r(base).jsValue();
        JSValue sentValue = callFrame->r(value).jsValue();
        
        if (labelReq && !isPolicy) {
            sentValue.setValueLabel(sentContextLabel.Join(callFrame->r(value).getRegLabel()));
            // if (sentValue.getValueLabel().Star())
            //     ABORT_TRANSACTION();
        }
        else {
            sentValue.setValueLabel(sentContextLabel);
        }
        
        JSLabel::argLabel[0] = sentValue.getValueLabel().getPair();
        Identifier& ident = codeBlock->identifier(property);
        PutPropertySlot slot(codeBlock->isStrictMode());
        
        if (direct) {
            ASSERT(baseValue.isObject());
            if(!isPolicy)
            {
                asObject(baseValue)->putDirectIFC(*globalData, ident, sentValue, slot, &isStructChanged);
            }
            else
            // Original
                asObject(baseValue)->putDirect(*globalData, ident, callFrame->r(value).jsValue(), slot);
        } else{
            if(!isPolicy)
            {
            baseValue.putIFC(callFrame, ident, sentValue, slot, &sentContextLabel, &abortRun, &isStructChanged);
            if (abortRun || JSLabel::ABORT_FLAG){
                JSLabel::ABORT_FLAG = false;
                ABORT_TRANSACTION();
            }
            }
            else
            // Original
                baseValue.put(callFrame, ident, callFrame->r(value).jsValue(), slot);
        }
        CHECK_FOR_EXCEPTION(sentContextLabel);
        JSLabel::argLabel[0] = JSLabel().getPair();;
        
        if (isStructChanged && asObject(baseValue)->getObjectLabel().Val()) {
            asObject(baseValue)->setObjectLabel(asObject(baseValue)->joinObjectLabel(sentContextLabel));
            if (labelReq && !isPolicy) 
                callFrame->uncheckedR(base).setRegLabel(asObject(baseValue)->getObjectLabel());
        }
        
        // IFC4BC-Do not cache, so the other opcodes would not be used
        // tryCachePutByID(callFrame, codeBlock, vPC, baseValue, slot);
        
        vPC += OPCODE_LENGTH(op_put_by_id);
         NEXT_INSTRUCTION();
    }
#if USE(GCC_COMPUTED_GOTO_WORKAROUND)
skip_put_by_id:
#endif
    DEFINE_OPCODE(op_put_by_id_transition_direct)
    DEFINE_OPCODE(op_put_by_id_transition_normal)
    DEFINE_OPCODE(op_put_by_id_transition_direct_out_of_line)
    DEFINE_OPCODE(op_put_by_id_transition_normal_out_of_line)
    DEFINE_OPCODE(op_put_by_id_transition) {
        /* op_put_by_id_transition base(r) property(id) value(r) oldStructure(sID) newStructure(sID) structureChain(chain) offset(n) direct(b)
         
         Cached property access: Attempts to set a new property with a cached transition
         property named by identifier property, belonging to register base,
         to register value. If the cache misses, op_put_by_id_transition
         reverts to op_put_by_id_generic.
         
         Unlike many opcodes, this one does not write any output to
         the register file.
         */
        int base = vPC[1].u.operand;
        JSValue baseValue = callFrame->r(base).jsValue();
        
        if (LIKELY(baseValue.isCell())) {
            JSCell* baseCell = baseValue.asCell();
            Structure* oldStructure = vPC[4].u.structure.get();
            Structure* newStructure = vPC[5].u.structure.get();
            
            if (LIKELY(baseCell->structure() == oldStructure)) {
                ASSERT(baseCell->isObject());
                JSObject* baseObject = asObject(baseCell);
                int direct = vPC[8].u.operand;
                
                if (!direct) {
                    WriteBarrier<Structure>* it = vPC[6].u.structureChain->head();
                    
                    JSValue proto = baseObject->structure()->prototypeForLookup(callFrame);
                    while (!proto.isNull()) {
                        if (UNLIKELY(asObject(proto)->structure() != (*it).get())) {
                            uncachePutByID(codeBlock, vPC);
                             NEXT_INSTRUCTION();
                        }
                        ++it;
                        proto = asObject(proto)->structure()->prototypeForLookup(callFrame);
                    }
                }
                baseObject->setStructureAndReallocateStorageIfNecessary(*globalData, newStructure);
                
                int value = vPC[3].u.operand;
                int offset = vPC[7].u.operand;
                ASSERT(baseObject->offsetForLocation(baseObject->getDirectLocation(*globalData, codeBlock->identifier(vPC[2].u.operand))) == offset);
                baseObject->putDirectOffset(callFrame->globalData(), offset, callFrame->r(value).jsValue());
                
                vPC += OPCODE_LENGTH(op_put_by_id_transition);
                 NEXT_INSTRUCTION();
            }
        }
        
        uncachePutByID(codeBlock, vPC);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_put_by_id_replace) {
        /* op_put_by_id_replace base(r) property(id) value(r) structure(sID) offset(n) nop(n) nop(n) direct(b)
         
         Cached property access: Attempts to set a pre-existing, cached
         property named by identifier property, belonging to register base,
         to register value. If the cache misses, op_put_by_id_replace
         reverts to op_put_by_id.
         
         Unlike many opcodes, this one does not write any output to
         the register file.
         */
        int base = vPC[1].u.operand;
        JSValue baseValue = callFrame->r(base).jsValue();
        
        if (LIKELY(baseValue.isCell())) {
            JSCell* baseCell = baseValue.asCell();
            Structure* structure = vPC[4].u.structure.get();
            
            if (LIKELY(baseCell->structure() == structure)) {
                ASSERT(baseCell->isObject());
                JSObject* baseObject = asObject(baseCell);
                int value = vPC[3].u.operand;
                int offset = vPC[5].u.operand;
                
                ASSERT(baseObject->offsetForLocation(baseObject->getDirectLocation(*globalData, codeBlock->identifier(vPC[2].u.operand))) == offset);
                baseObject->putDirectOffset(callFrame->globalData(), offset, callFrame->r(value).jsValue());
                
                vPC += OPCODE_LENGTH(op_put_by_id_replace);
                 NEXT_INSTRUCTION();
            }
        }
        
        uncachePutByID(codeBlock, vPC);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_put_by_id_generic) {
        /* op_put_by_id_generic base(r) property(id) value(r) nop(n) nop(n) nop(n) nop(n) direct(b)
         
         Generic property access: Sets the property named by identifier
         property, belonging to register base, to register value.
         
         Unlike many opcodes, this one does not write any output to
         the register file.
         */
        int base = vPC[1].u.operand;
        int property = vPC[2].u.operand;
        int value = vPC[3].u.operand;
        int direct = vPC[8].u.operand;
        // IFC4BC - Set the flag for aborting the run if NSU fails in putIFC
        bool abortRun = false;
        bool isStructChanged = false;
        JSLabel sentContextLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
        // ------
        JSValue baseValue = callFrame->r(base).jsValue();
        JSValue sentValue = callFrame->r(value).jsValue();
        // baseValue.setValueLabel(sentContextLabel);
        if (labelReq && !isPolicy) {
            sentValue.setValueLabel(sentContextLabel.Join(callFrame->r(value).getRegLabel()));
            // if (sentValue.getValueLabel().Star())
            //     ABORT_TRANSACTION();
        }
        else {
            sentValue.setValueLabel(sentContextLabel);
        }
        
        Identifier& ident = codeBlock->identifier(property);
        PutPropertySlot slot(codeBlock->isStrictMode());
        
        if (direct) {
            ASSERT(baseValue.isObject());
            if(!isPolicy)
                asObject(baseValue)->putDirectIFC(*globalData, ident, sentValue, slot, &isStructChanged);
            // Original
            else
                asObject(baseValue)->putDirect(*globalData, ident, callFrame->r(value).jsValue(), slot);
        } else{
            if(!isPolicy)
            {
                baseValue.putIFC(callFrame, ident, sentValue, slot, &sentContextLabel, &abortRun, &isStructChanged);
                if (abortRun || JSLabel::ABORT_FLAG){
                    JSLabel::ABORT_FLAG = false;
                    ABORT_TRANSACTION();
                }
            }
            else
            // Original
                baseValue.put(callFrame, ident, callFrame->r(value).jsValue(), slot);
        }
        CHECK_FOR_EXCEPTION(sentContextLabel);

        if (isStructChanged && (asObject(baseValue)->getObjectLabel().Val())) {
            asObject(baseValue)->setObjectLabel(asObject(baseValue)->joinObjectLabel(sentContextLabel));
                if (labelReq && !isPolicy)
                    callFrame->uncheckedR(base).setRegLabel(asObject(baseValue)->getObjectLabel());
        }
        
        vPC += OPCODE_LENGTH(op_put_by_id_generic);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_del_by_id) {
        /* del_by_id dst(r) base(r) property(id)
         
         Converts register base to Object, deletes the property
         named by identifier property from the object, and writes a
         boolean indicating success (if true) or failure (if false)
         to register dst.
         */
        int dst = vPC[1].u.operand;
        int base = vPC[2].u.operand;
        int property = vPC[3].u.operand;
        
        JSObject* baseObj = callFrame->r(base).jsValue().toObject(callFrame);
        Identifier& ident = codeBlock->identifier(property);
        //IFC4BC
        if(!pcLabel.NSU(baseObj->getObjectLabel()))
            ABORT_TRANSACTION();
        
        // ------
        // TODO - Check if deleteProperty traverses the chain. If so, pass context
        bool result = baseObj->methodTable()->deleteProperty(baseObj, callFrame, ident);
        if (!result && codeBlock->isStrictMode()) {
            exceptionValue = createTypeError(callFrame, "Unable to delete property.");
            exceptionValue.setValueLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            goto vm_throw;
        }
        CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
            if(!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else
            {
                // dstLabel.setStar(false);
            }
            callFrame->uncheckedR(dst) = jsBoolean(result);
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = jsBoolean(result);            
        }
        vPC += OPCODE_LENGTH(op_del_by_id);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_get_by_pname) {
        int dst = vPC[1].u.operand;
        int base = vPC[2].u.operand;
        int property = vPC[3].u.operand;
        int expected = vPC[4].u.operand;
        int iter = vPC[5].u.operand;
        int i = vPC[6].u.operand;
        
        JSLabel context = pcLabel/*.Join(codeBlock->contextLabel)*/;
        
        JSValue baseValue = callFrame->r(base).jsValue();
        JSPropertyNameIterator* it = callFrame->r(iter).propertyNameIterator();
        JSValue subscript = callFrame->r(property).jsValue();
        JSValue expectedSubscript = callFrame->r(expected).jsValue();
        int index = callFrame->r(i).i() - 1;
        JSValue result;
        PropertyOffset offset = 0;
        if (subscript == expectedSubscript && baseValue.isCell() && (baseValue.asCell()->structure() == it->cachedStructure()) && it->getOffset(index, offset)) {
            // IFC4BC - Joining the labels
            JSValue res = JSValue(asObject(baseValue)->getDirectOffset(offset));
            if (labelReq && !isPolicy) {
                JSLabel resLabel = res.getValueLabel();
                // if (resLabel.Star()) {
                    // resLabel.setStar(false);
                // }
                
                JSLabel dstLabel = resLabel.Join(pcLabel/*.Join(codeBlock->contextLabel)*/.Join(baseValue.joinValueLabel(subscript.joinValueLabel(expectedSubscript.getValueLabel()))));
                if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
                {
                    printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                    dstLabel.setStar(true);
                }
                else
                {
                    // dstLabel.setStar(false);
                }
                callFrame->uncheckedR(dst) = res;
                callFrame->uncheckedR(dst).setRegLabel(dstLabel);
            }
            else {
                callFrame->uncheckedR(dst) = res;
            }
            vPC += OPCODE_LENGTH(op_get_by_pname);
             NEXT_INSTRUCTION();
        }
        {
            Identifier propertyName(callFrame, subscript.toString(callFrame)->value(callFrame));
            // IFC4BC
            result = baseValue.getIFC(callFrame, propertyName, &context);
            // if (result.getValueLabel().Star()) {
            context = context.Join(result.getValueLabel());
                // context.setStar(false);
            // }
            // Original
            // result = baseValue.get(callFrame, propertyName);
        }
        CHECK_FOR_EXCEPTION(context);
        if (context.Val() != pcLabel.Val() && !labelReq) {
            labelReq = true;
            labelRegisters(callFrame, codeBlock, pcLabel);
        }
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = context;
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else
            {
                // dstLabel.setStar(false);
            }
            callFrame->uncheckedR(dst) = result;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = result;            
        }
        vPC += OPCODE_LENGTH(op_get_by_pname);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_get_arguments_length) {
        int dst = vPC[1].u.operand;
        int argumentsRegister = vPC[2].u.operand;
        int property = vPC[3].u.operand;
        JSValue arguments = callFrame->r(argumentsRegister).jsValue();
        JSLabel context = pcLabel/*.Join(codeBlock->contextLabel)*/;
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = context;
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else
            {
                // dstLabel.setStar(false);
            }
            if (arguments) {
                Identifier& ident = codeBlock->identifier(property);
                PropertySlot slot(arguments);
                JSValue result = arguments.getIFC(callFrame, ident, slot, &context);
                // if (result.getValueLabel().Star()) {
                    context = context.Join(result.getValueLabel());
                    // context.setStar(false);
                // }
                CHECK_FOR_EXCEPTION(context);
                callFrame->uncheckedR(dst) = result;
            } else
                callFrame->uncheckedR(dst) = jsNumber(callFrame->argumentCount());
            callFrame->uncheckedR(dst).setRegLabel(dstLabel.Join(context));
        }
        else {
            if (arguments) {
                Identifier& ident = codeBlock->identifier(property);
                PropertySlot slot(arguments);
                JSValue result = arguments.getIFC(callFrame, ident, slot, &context);
                // if (result.getValueLabel().Star()) {
                context = context.Join(result.getValueLabel());
                    // context.setStar(false);
                // }
                if (context.Val() != pcLabel.Val() && !labelReq) {
                    labelReq = true;
                    labelRegisters(callFrame, codeBlock, pcLabel);
                }
                CHECK_FOR_EXCEPTION(context);
                callFrame->uncheckedR(dst) = result;
            } else
                callFrame->uncheckedR(dst) = jsNumber(callFrame->argumentCount());
            if (labelReq && !isPolicy)
                callFrame->uncheckedR(dst).setRegLabel(context);
        }
        
        vPC += OPCODE_LENGTH(op_get_arguments_length);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_get_argument_by_val) {
        int dst = vPC[1].u.operand;
        int argumentsRegister = vPC[2].u.operand;
        int property = vPC[3].u.operand;
        JSValue arguments = callFrame->r(argumentsRegister).jsValue();
        JSValue subscript = callFrame->r(property).jsValue();
        if (!arguments && subscript.isUInt32() && subscript.asUInt32() < callFrame->argumentCount()) {
            // IFC4BC - DNSU. Might require more functionality
            if (labelReq && !isPolicy) {
                JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
                if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
                {

                    printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                    dstLabel.setStar(true);
                }
                else
                {
                    // dstLabel.setStar(false);
                }
                callFrame->uncheckedR(dst) = callFrame->argument(subscript.asUInt32());
                callFrame->uncheckedR(dst).setRegLabel(dstLabel);
            }
            else {
                callFrame->uncheckedR(dst) = callFrame->argument(subscript.asUInt32());                
            }
            vPC += OPCODE_LENGTH(op_get_argument_by_val);
             NEXT_INSTRUCTION();
        }
        
        if (!arguments) {
            Arguments* arguments = Arguments::create(*globalData, callFrame);
            // IFC4BC - Assigning label to arguments object
            arguments->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            arguments->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            if (labelReq && !isPolicy) {
                JSLabel argLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
                JSLabel argULabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
                if(!noSensitiveUpgrade(callFrame->r(argumentsRegister).getRegLabel()))
                {
                    printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(argumentsRegister).getRegLabel().Val(), pcLabel.Val());
                    argLabel.setStar(true);
                }
                if(!noSensitiveUpgrade(callFrame->r(unmodifiedArgumentsRegister(argumentsRegister)).getRegLabel()))
                {
                    printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(argumentsRegister).getRegLabel().Val(), pcLabel.Val());
                    argULabel.setStar(true);
                }
                callFrame->uncheckedR(argumentsRegister) = JSValue(arguments);
                callFrame->uncheckedR(unmodifiedArgumentsRegister(argumentsRegister)) = JSValue(arguments);
                callFrame->uncheckedR(argumentsRegister).setRegLabel(argLabel);
                callFrame->uncheckedR(unmodifiedArgumentsRegister(argumentsRegister)).setRegLabel(argULabel);
            }
            else {
                callFrame->uncheckedR(argumentsRegister) = JSValue(arguments);
                callFrame->uncheckedR(unmodifiedArgumentsRegister(argumentsRegister)) = JSValue(arguments);
            }
        }
        // fallthrough
    }
    DEFINE_OPCODE(op_get_by_val) {
        /* get_by_val dst(r) base(r) property(r)
         
         Converts register base to Object, gets the property named
         by register property from the object, and puts the result
         in register dst. property is nominally converted to string
         but numbers are treated more efficiently.
         */
        int dst = vPC[1].u.operand;
        int base = vPC[2].u.operand;
        int property = vPC[3].u.operand;
        
        JSValue baseValue = callFrame->r(base).jsValue();
        JSValue subscript = callFrame->r(property).jsValue();
        
        // IFC4BC
        JSLabel context = pcLabel/*.Join(codeBlock->contextLabel)*/;
        
        JSValue result;
        
        if (LIKELY(subscript.isUInt32())) {
            uint32_t i = subscript.asUInt32();
            if (isJSArray(baseValue)) {
                JSArray* jsArray = asArray(baseValue);
                if (jsArray->canGetIndex(i))
                    result = jsArray->getIndex(i);
                else
                    result = jsArray->JSArray::getIFC(callFrame, i, &context);
            } else if (isJSString(baseValue) && asString(baseValue)->canGetIndex(i))
                result = asString(baseValue)->getIndex(callFrame, i);
            else
                result = baseValue.getIFC(callFrame, i, &context);
            // Original
            // result = baseValue.get(callFrame, i);
        } else if (isName(subscript))
            result = baseValue.getIFC(callFrame, jsCast<NameInstance*>(subscript.asCell())->privateName(), &context);
        // Original
        // result = baseValue.get(callFrame, jsCast<NameInstance*>(subscript.asCell())->privateName());
        else {
            Identifier property(callFrame, subscript.toString(callFrame)->value(callFrame));
            // IFC4BC - Changed to include context label
            result = baseValue.getIFC(callFrame, property, &context);
            // Original
            // result = baseValue.get(callFrame, property);
        }
        // if (result.getValueLabel().Star()) {
        context = context.Join(result.getValueLabel());
            // context.setStar(false);
        // }
        if (context.Val() != pcLabel/*.Join(codeBlock->contextLabel)*/.Val() && !labelReq)
        {
            labelReq = true;
            labelRegisters(callFrame, codeBlock, pcLabel/*.Join(codeBlock->contextLabel)*/);
        }
        CHECK_FOR_EXCEPTION(context);
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = result.joinValueLabel(baseValue.joinValueLabel(context));
            if (baseValue.isCell())
            {
                dstLabel = dstLabel.Join(baseValue.asCell()->getObjectLabel());
            }
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else
            {
                // dstLabel.setStar(false);
            }
            callFrame->uncheckedR(dst) = result;
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = result;
        }
        vPC += OPCODE_LENGTH(op_get_by_val);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_put_by_val) {
        /* put_by_val base(r) property(r) value(r)
         
         Sets register value on register base as the property named
         by register property. Base is converted to object
         first. register property is nominally converted to string
         but numbers are treated more efficiently.
         
         Unlike many opcodes, this one does not write any output to
         the register file.
         */
        int base = vPC[1].u.operand;
        int property = vPC[2].u.operand;
        int value = vPC[3].u.operand;
        
        JSValue baseValue = callFrame->r(base).jsValue();
        JSValue subscript = callFrame->r(property).jsValue();
        JSValue sentValue = callFrame->r(value).jsValue();
        if (labelReq && !isPolicy) {
            sentValue.setValueLabel(pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(value).getRegLabel()));
            // if (sentValue.getValueLabel().Star())
            //     ABORT_TRANSACTION();
        }
        else {
            sentValue.setValueLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
        }
        // IFC4BC
        JSLabel context = pcLabel/*.Join(codeBlock->contextLabel)*/;
        bool abortRun = false;
        bool isStructChanged = false;
        
        if (LIKELY(subscript.isUInt32())) {
            uint32_t i = subscript.asUInt32();
            if (isJSArray(baseValue)) {
                JSArray* jsArray = asArray(baseValue);
                if (jsArray->canSetIndex(i))
                {
                    jsArray->setIndex(*globalData, i, sentValue);
                    // IFC4BC - adds at a particular index in the array
                    isStructChanged = true;
                }
                else
                    jsArray->JSArray::putByIndexIFC(jsArray, callFrame, i, sentValue, codeBlock->isStrictMode(),
                                                    &context, &abortRun, &isStructChanged);
            } else
                baseValue.putByIndexIFC(callFrame, i, sentValue, codeBlock->isStrictMode(), &context, &abortRun, &isStructChanged);
        } else if (isName(subscript)) {
            PutPropertySlot slot(codeBlock->isStrictMode());
            if(!isPolicy)
                baseValue.putIFC(callFrame, jsCast<NameInstance*>(subscript.asCell())->privateName(), sentValue, slot, &context, &abortRun, &isStructChanged);
            else
                baseValue.put(callFrame, jsCast<NameInstance*>(subscript.asCell())->privateName(), callFrame->r(value).jsValue(), slot);
        } else {
            Identifier property(callFrame, subscript.toString(callFrame)->value(callFrame));
            if (!globalData->exception) { // Don't put to an object if toString threw an exception.
                PutPropertySlot slot(codeBlock->isStrictMode());
                if(!isPolicy)
                    baseValue.putIFC(callFrame, property, sentValue, slot, &context, &abortRun, &isStructChanged);
                else
                    baseValue.put(callFrame, property, callFrame->r(value).jsValue(), slot);
            }
        }
        
        // IFC4BC - Setting labels and aborting if something failed
        if (abortRun || JSLabel::ABORT_FLAG) {
            JSLabel::ABORT_FLAG = false;
            ABORT_TRANSACTION();
        }
        
        if (isStructChanged && (asObject(baseValue)->getObjectLabel().Val())) {
            asObject(baseValue)->setObjectLabel(asObject(baseValue)->joinObjectLabel(context));
            if (labelReq && !isPolicy)
                callFrame->uncheckedR(base).setRegLabel(asObject(baseValue)->getObjectLabel());
        }
        
        CHECK_FOR_EXCEPTION(context);
        vPC += OPCODE_LENGTH(op_put_by_val);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_del_by_val) {
        /* del_by_val dst(r) base(r) property(r)
         
         Converts register base to Object, deletes the property
         named by register property from the object, and writes a
         boolean indicating success (if true) or failure (if false)
         to register dst.
         */
        int dst = vPC[1].u.operand;
        int base = vPC[2].u.operand;
        int property = vPC[3].u.operand;
        
        JSObject* baseObj = callFrame->r(base).jsValue().toObject(callFrame); // may throw
        
        // IFC4BC - Should we not check for the property's label also before deleting?
        // TODO - Also should we send context?
        if(!pcLabel.NSU(baseObj->getObjectLabel()))
            ABORT_TRANSACTION();
        // ------
        
        JSValue subscript = callFrame->r(property).jsValue();
        bool result;
        uint32_t i;
        if (subscript.getUInt32(i))
            result = baseObj->methodTable()->deletePropertyByIndex(baseObj, callFrame, i);
        else if (isName(subscript))
            result = baseObj->methodTable()->deleteProperty(baseObj, callFrame, jsCast<NameInstance*>(subscript.asCell())->privateName());
        else {
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
            Identifier property(callFrame, subscript.toString(callFrame)->value(callFrame));
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
            result = baseObj->methodTable()->deleteProperty(baseObj, callFrame, property);
        }
        if (!result && codeBlock->isStrictMode()) {
            exceptionValue = createTypeError(callFrame, "Unable to delete property.");
            exceptionValue.setValueLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            goto vm_throw;
        }
        CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else
            {
                // dstLabel.setStar(false);
            }
            callFrame->uncheckedR(dst) = jsBoolean(result);
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = jsBoolean(result);            
        }
        vPC += OPCODE_LENGTH(op_del_by_val);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_put_by_index) {
        /* put_by_index base(r) property(n) value(r)
         
         Sets register value on register base as the property named
         by the immediate number property. Base is converted to
         object first.
         
         Unlike many opcodes, this one does not write any output to
         the register file.
         
         This opcode is mainly used to initialize array literals.
         */
        int base = vPC[1].u.operand;
        unsigned property = vPC[2].u.operand;
        int value = vPC[3].u.operand;
        
        JSValue arrayValue = callFrame->r(base).jsValue();
        JSValue sentValue = callFrame->r(value).jsValue();
        // IFC4BC - Set the label and check for star
        if (labelReq && !isPolicy) {
            sentValue.setValueLabel(pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(value).getRegLabel()));
            // if (sentValue.getValueLabel().Star())
            //    ABORT_TRANSACTION();
        }
        else {
            sentValue.setValueLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
        }
        
        ASSERT(isJSArray(arrayValue));
        // TODO - IFC4BC - Should we check contexts and arrayValue?
        asArray(arrayValue)->putDirectIndex(callFrame, property, sentValue, false);
        
        vPC += OPCODE_LENGTH(op_put_by_index);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_loop) {
        /* loop target(offset)
         
         Jumps unconditionally to offset target from the current
         instruction.
         
         Additionally this loop instruction may terminate JS execution is
         the JS timeout is reached.
         */
#if ENABLE(OPCODE_STATS)
        OpcodeStats::resetLastInstruction();
#endif
        int target = vPC[1].u.operand;
        CHECK_FOR_TIMEOUT();
        vPC += target;
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_jmp) {
        /* jmp target(offset)
         
         Jumps unconditionally to offset target from the current
         instruction.
         */
#if ENABLE(OPCODE_STATS)
        OpcodeStats::resetLastInstruction();
#endif
        int target = vPC[1].u.operand;
        
        vPC += target;
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_loop_hint) {
        // This is a no-op unless we intend on doing OSR from the interpreter.
        vPC += OPCODE_LENGTH(op_loop_hint);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_loop_if_true) {
        /* loop_if_true cond(r) target(offset)
         
         Jumps to offset target from the current instruction, if and
         only if register cond converts to boolean as true.
         
         Additionally this loop instruction may terminate JS execution is
         the JS timeout is reached.
         */
        int cond = vPC[1].u.operand;
        int target = vPC[2].u.operand;
        
        // IFC4BC -- To push context label on the pcstack
        if (labelReq && !isPolicy) {
            JSLabel contextLabel = callFrame->r(cond).getRegLabel();
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
        }
        // IFC4BC ---------------------------------------
        
        if (callFrame->r(cond).jsValue().toBoolean()) {
            vPC += target;
            CHECK_FOR_TIMEOUT();
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_loop_if_true);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_loop_if_false) {
        /* loop_if_true cond(r) target(offset)
         
         Jumps to offset target from the current instruction, if and
         only if register cond converts to boolean as false.
         
         Additionally this loop instruction may terminate JS execution is
         the JS timeout is reached.
         */
        int cond = vPC[1].u.operand;
        int target = vPC[2].u.operand;
        
        // IFC4BC -- To push context label on the pcstack
        if (labelReq && !isPolicy) {
            JSLabel contextLabel = callFrame->r(cond).getRegLabel();
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
        }
        // IFC4BC ---------------------------------------
        
        if (!callFrame->r(cond).jsValue().toBoolean()) {
            vPC += target;
            CHECK_FOR_TIMEOUT();
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_loop_if_true);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_jtrue) {
        /* jtrue cond(r) target(offset)
         
         Jumps to offset target from the current instruction, if and
         only if register cond converts to boolean as true.
         */
        int cond = vPC[1].u.operand;
        int target = vPC[2].u.operand;
        
        // IFC4BC -- To push context label on the pcstack
        if (labelReq && !isPolicy) {
            JSLabel contextLabel = callFrame->r(cond).getRegLabel();
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
        }
        // IFC4BC ---------------------------------------
        
        if (callFrame->r(cond).jsValue().toBoolean()) {
            vPC += target;
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_jtrue);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_jfalse) {
        /* jfalse cond(r) target(offset)
         
         Jumps to offset target from the current instruction, if and
         only if register cond converts to boolean as false.
         */
        int cond = vPC[1].u.operand;
        int target = vPC[2].u.operand;
        
        // IFC4BC -- To push context label on the pcstack
        if (labelReq && !isPolicy) {
            JSLabel contextLabel = callFrame->r(cond).getRegLabel();
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
        }
        // IFC4BC ---------------------------------------
        
        if (!callFrame->r(cond).jsValue().toBoolean()) {
            vPC += target;
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_jfalse);
         NEXT_INSTRUCTION();
    }
    
    // Abhi -- Functionality for opcode - op_jempty
    // Used exclusively for a redefined finally block
    // Do not use this for any other purpose
    DEFINE_OPCODE(op_jempty) {
        /* jempty src(r) target(offset)
         
         Jumps to offset target from the current instruction, if and
         only if the register is empty
         */
        int cond = vPC[1].u.operand;
        int target = vPC[2].u.operand;
        
        JSValue result = callFrame->r(cond).jsValue();
        
        // IFC4BC -- To push context label on the pcstack
        if (labelReq && !isPolicy) {
           JSLabel contextLabel = callFrame->r(cond).getRegLabel();
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
        }
        // IFC4BC ---------------------------------------
        
        // The register is empty. This is just for making finally block work
        if (result.isEmpty()) {
            vPC += target;
             NEXT_INSTRUCTION();
        }
        vPC += OPCODE_LENGTH(op_jempty);
         NEXT_INSTRUCTION();
    }
    // Abhi ---------------------------------------
    
    DEFINE_OPCODE(op_jeq_null) {
        /* jeq_null src(r) target(offset)
         
         Jumps to offset target from the current instruction, if and
         only if register src is null.
         */
        int src = vPC[1].u.operand;
        int target = vPC[2].u.operand;
        JSValue srcValue = callFrame->r(src).jsValue();
        
        // IFC4BC -- To push context label on the pcstack
        if (labelReq && !isPolicy) {
           JSLabel contextLabel = callFrame->r(src).getRegLabel();
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
        }
        // IFC4BC ---------------------------------------
        
        if (srcValue.isUndefinedOrNull() || (srcValue.isCell() && srcValue.asCell()->structure()->typeInfo().masqueradesAsUndefined())) {
            vPC += target;
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_jeq_null);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_jneq_null) {
        /* jneq_null src(r) target(offset)
         
         Jumps to offset target from the current instruction, if and
         only if register src is not null.
         */
        int src = vPC[1].u.operand;
        int target = vPC[2].u.operand;
        JSValue srcValue = callFrame->r(src).jsValue();
        
        // IFC4BC -- To push context label on the pcstack
        if (labelReq && !isPolicy) {
            JSLabel contextLabel = callFrame->r(src).getRegLabel();
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
        }
        // IFC4BC ---------------------------------------
        
        if (!srcValue.isUndefinedOrNull() && (!srcValue.isCell() || !srcValue.asCell()->structure()->typeInfo().masqueradesAsUndefined())) {
            vPC += target;
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_jneq_null);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_jneq_ptr) {
        /* jneq_ptr src(r) ptr(jsCell) target(offset)
         
         Jumps to offset target from the current instruction, if the value r is equal
         to ptr, using pointer equality.
         */
        int src = vPC[1].u.operand;
        int target = vPC[3].u.operand;
        JSValue srcValue = callFrame->r(src).jsValue();
        
        // IFC4BC -- To push context label on the pcstack
        if (labelReq && !isPolicy) {
            JSLabel contextLabel = callFrame->r(src).getRegLabel();
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
        }
        // IFC4BC ---------------------------------------
        
        if (srcValue != vPC[2].u.jsCell.get()) {
            vPC += target;
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_jneq_ptr);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_loop_if_less) {
        /* loop_if_less src1(r) src2(r) target(offset)
         
         Checks whether register src1 is less than register src2, as
         with the ECMAScript '<' operator, and then jumps to offset
         target from the current instruction, if and only if the
         result of the comparison is true.
         
         Additionally this loop instruction may terminate JS execution is
         the JS timeout is reached.
         */
        JSValue src1 = callFrame->r(vPC[1].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[2].u.operand).jsValue();
        int target = vPC[3].u.operand;
        
        // IFC4BC -- To push context label on the pcstack
        bool result = jsLess<true>(callFrame, src1, src2);
        if (labelReq && !isPolicy) {
            JSLabel contextLabel;
            JSLabel tdstLabel = (callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel()));
            uint64_t dstL = tdstLabel.Val();
            /*
            if (pcLabel <= tdstLabel) {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t bits = BitMap::Bitmap().getBits(i);
                        uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                        uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                        if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                            dstL = dstL | aLabel;
                        }
                        else {
                            BitMap::Bitmap().setBits(i, bits - 1);
                            dstL = dstL | dLabel;
                        }
                    }
                    i = i << 1;
                }
            }
            else {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                        dstL = dstL | dLabel;
                    }
                    i = i << 1;
                }
            }*/
            contextLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
            CHECK_FOR_EXCEPTION(contextLabel);
        }
        else {
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
        }
        // IFC4BC ---------------------------------------
                
        if (result) {
            vPC += target;
            CHECK_FOR_TIMEOUT();
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_loop_if_less);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_loop_if_lesseq) {
        /* loop_if_lesseq src1(r) src2(r) target(offset)
         
         Checks whether register src1 is less than or equal to register
         src2, as with the ECMAScript '<=' operator, and then jumps to
         offset target from the current instruction, if and only if the
         result of the comparison is true.
         
         Additionally this loop instruction may terminate JS execution is
         the JS timeout is reached.
         */
        JSValue src1 = callFrame->r(vPC[1].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[2].u.operand).jsValue();
        int target = vPC[3].u.operand;
        bool result = jsLessEq<true>(callFrame, src1, src2);
        
        if (labelReq && !isPolicy) {
//            JSLabel contextLabel = callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel());
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            JSLabel contextLabel;
            JSLabel tdstLabel = (callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel()));
            uint64_t dstL = tdstLabel.Val();
            /*
            if (pcLabel <= tdstLabel) {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t bits = BitMap::Bitmap().getBits(i);
                        uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                        uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                        if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                            dstL = dstL | aLabel;
                        }
                        else {
                            BitMap::Bitmap().setBits(i, bits - 1);
                            dstL = dstL | dLabel;
                        }
                    }
                    i = i << 1;
                }
            }
            else {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                        dstL = dstL | dLabel;
                    }
                    i = i << 1;
                }
            }*/
            contextLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            
            // IFC4BC -- To push context label on the pcstack
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
            CHECK_FOR_EXCEPTION(contextLabel);
        }
        else {
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
        }
        // IFC4BC ---------------------------------------
        
        if (result) {
            vPC += target;
            CHECK_FOR_TIMEOUT();
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_loop_if_lesseq);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_loop_if_greater) {
        /* loop_if_greater src1(r) src2(r) target(offset)
         
         Checks whether register src1 is greater than register src2, as
         with the ECMAScript '>' operator, and then jumps to offset
         target from the current instruction, if and only if the
         result of the comparison is true.
         
         Additionally this loop instruction may terminate JS execution is
         the JS timeout is reached.
         */
        JSValue src1 = callFrame->r(vPC[1].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[2].u.operand).jsValue();
        int target = vPC[3].u.operand;
        bool result = jsLess<false>(callFrame, src2, src1);
       
        if (labelReq && !isPolicy) {
//            JSLabel contextLabel = callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel());
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            JSLabel contextLabel;
            JSLabel tdstLabel = (callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel()));
            uint64_t dstL = tdstLabel.Val();
            /*
            if (pcLabel <= tdstLabel) {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t bits = BitMap::Bitmap().getBits(i);
                        uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                        uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                        if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                            dstL = dstL | aLabel;
                        }
                        else {
                            BitMap::Bitmap().setBits(i, bits - 1);
                            dstL = dstL | dLabel;
                        }
                    }
                    i = i << 1;
                }
            }
            else {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                        dstL = dstL | dLabel;
                    }
                    i = i << 1;
                }
            }*/
            contextLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            
            // IFC4BC -- To push context label on the pcstack
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
            CHECK_FOR_EXCEPTION(contextLabel);
        }
        else {
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
        }
        // IFC4BC ---------------------------------------
        
        if (result) {
            vPC += target;
            CHECK_FOR_TIMEOUT();
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_loop_if_greater);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_loop_if_greatereq) {
        /* loop_if_greatereq src1(r) src2(r) target(offset)
         
         Checks whether register src1 is greater than or equal to register
         src2, as with the ECMAScript '>=' operator, and then jumps to
         offset target from the current instruction, if and only if the
         result of the comparison is true.
         
         Additionally this loop instruction may terminate JS execution is
         the JS timeout is reached.
         */
        JSValue src1 = callFrame->r(vPC[1].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[2].u.operand).jsValue();
        int target = vPC[3].u.operand;
        bool result = jsLessEq<false>(callFrame, src2, src1);
      
        if (labelReq && !isPolicy) {
//            JSLabel contextLabel = callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel());
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            JSLabel contextLabel;
            JSLabel tdstLabel = (callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel()));
            uint64_t dstL = tdstLabel.Val();
            /*
            if (pcLabel <= tdstLabel) {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t bits = BitMap::Bitmap().getBits(i);
                        uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                        uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                        if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                            dstL = dstL | aLabel;
                        }
                        else {
                            BitMap::Bitmap().setBits(i, bits - 1);
                            dstL = dstL | dLabel;
                        }
                    }
                    i = i << 1;
                }
            }
            else {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                        dstL = dstL | dLabel;
                    }
                    i = i << 1;
                }
            }*/
            contextLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            
            // IFC4BC -- To push context label on the pcstack
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
            CHECK_FOR_EXCEPTION(contextLabel);
        }
        else {
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);

        }
        // IFC4BC ---------------------------------------

        if (result) {
            vPC += target;
            CHECK_FOR_TIMEOUT();
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_loop_if_greatereq);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_jless) {
        /* jless src1(r) src2(r) target(offset)
         
         Checks whether register src1 is less than register src2, as
         with the ECMAScript '<' operator, and then jumps to offset
         target from the current instruction, if and only if the
         result of the comparison is true.
         */
        JSValue src1 = callFrame->r(vPC[1].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[2].u.operand).jsValue();
        int target = vPC[3].u.operand;
        bool result = jsLess<true>(callFrame, src1, src2);
        
        if (labelReq && !isPolicy) {
//            JSLabel contextLabel = callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel());
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            JSLabel contextLabel;
            JSLabel tdstLabel = (callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel()));
            uint64_t dstL = tdstLabel.Val();
            /*
            if (pcLabel <= tdstLabel) {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t bits = BitMap::Bitmap().getBits(i);
                        uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                        uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                        if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                            dstL = dstL | aLabel;
                        }
                        else {
                            BitMap::Bitmap().setBits(i, bits - 1);
                            dstL = dstL | dLabel;
                        }
                    }
                    i = i << 1;
                }
            }
            else {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                        dstL = dstL | dLabel;
                    }
                    i = i << 1;
                }
            }*/
            contextLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            
            // IFC4BC -- To push context label on the pcstack
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
            CHECK_FOR_EXCEPTION(contextLabel);
        }
        else {
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
        }
        // IFC4BC ---------------------------------------
                
        if (result) {
            vPC += target;
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_jless);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_jlesseq) {
        /* jlesseq src1(r) src2(r) target(offset)
         
         Checks whether register src1 is less than or equal to
         register src2, as with the ECMAScript '<=' operator,
         and then jumps to offset target from the current instruction,
         if and only if the result of the comparison is true.
         */
        JSValue src1 = callFrame->r(vPC[1].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[2].u.operand).jsValue();
        int target = vPC[3].u.operand;
        bool result = jsLessEq<true>(callFrame, src1, src2);
        
        if (labelReq && !isPolicy) {
//            JSLabel contextLabel = callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel());
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            JSLabel contextLabel;
            JSLabel tdstLabel = (callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel()));
            uint64_t dstL = tdstLabel.Val();
            /*
            if (pcLabel <= tdstLabel) {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t bits = BitMap::Bitmap().getBits(i);
                        uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                        uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                        if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                            dstL = dstL | aLabel;
                        }
                        else {
                            BitMap::Bitmap().setBits(i, bits - 1);
                            dstL = dstL | dLabel;
                        }
                    }
                    i = i << 1;
                }
            }
            else {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                        dstL = dstL | dLabel;
                    }
                    i = i << 1;
                }
            }*/
            contextLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            
            // IFC4BC -- To push context label on the pcstack
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
            CHECK_FOR_EXCEPTION(contextLabel);
        }
        else {
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
        }
        // IFC4BC ---------------------------------------
        
        if (result) {
            vPC += target;
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_jlesseq);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_jgreater) {
        /* jgreater src1(r) src2(r) target(offset)
         
         Checks whether register src1 is greater than register src2, as
         with the ECMAScript '>' operator, and then jumps to offset
         target from the current instruction, if and only if the
         result of the comparison is true.
         */
        JSValue src1 = callFrame->r(vPC[1].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[2].u.operand).jsValue();
        int target = vPC[3].u.operand;
        bool result = jsLess<false>(callFrame, src2, src1);
        
        if (labelReq && !isPolicy) {
//            JSLabel contextLabel = callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel());
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            JSLabel contextLabel;
            JSLabel tdstLabel = (callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel()));
            uint64_t dstL = tdstLabel.Val();
            /*
            if (pcLabel <= tdstLabel) {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t bits = BitMap::Bitmap().getBits(i);
                        uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                        uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                        if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                            dstL = dstL | aLabel;
                        }
                        else {
                            BitMap::Bitmap().setBits(i, bits - 1);
                            dstL = dstL | dLabel;
                        }
                    }
                    i = i << 1;
                }
            }
            else {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                        dstL = dstL | dLabel;
                    }
                    i = i << 1;
                }
            }*/
            contextLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            
            // IFC4BC -- To push context label on the pcstack
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
            CHECK_FOR_EXCEPTION(contextLabel);
        }
        else {
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
        }
        // IFC4BC ---------------------------------------
        
        if (result) {
            vPC += target;
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_jgreater);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_jgreatereq) {
        /* jgreatereq src1(r) src2(r) target(offset)
         
         Checks whether register src1 is greater than or equal to
         register src2, as with the ECMAScript '>=' operator,
         and then jumps to offset target from the current instruction,
         if and only if the result of the comparison is true.
         */
        JSValue src1 = callFrame->r(vPC[1].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[2].u.operand).jsValue();
        int target = vPC[3].u.operand;
        bool result = jsLessEq<false>(callFrame, src2, src1);
        
        if (labelReq && !isPolicy) {
//            JSLabel contextLabel = callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel());
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            JSLabel contextLabel;
            JSLabel tdstLabel = (callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel()));
            uint64_t dstL = tdstLabel.Val();
            /*
            if (pcLabel <= tdstLabel) {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t bits = BitMap::Bitmap().getBits(i);
                        uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                        uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                        if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                            dstL = dstL | aLabel;
                        }
                        else {
                            BitMap::Bitmap().setBits(i, bits - 1);
                            dstL = dstL | dLabel;
                        }
                    }
                    i = i << 1;
                }
            }
            else {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                        dstL = dstL | dLabel;
                    }
                    i = i << 1;
                }
            }*/
            contextLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            
            // IFC4BC -- To push context label on the pcstack
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
            CHECK_FOR_EXCEPTION(contextLabel);
        }
        // IFC4BC ---------------------------------------
        else {
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
        }
        
        if (result) {
            vPC += target;
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_jgreatereq);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_jnless) {
        /* jnless src1(r) src2(r) target(offset)
         
         Checks whether register src1 is less than register src2, as
         with the ECMAScript '<' operator, and then jumps to offset
         target from the current instruction, if and only if the
         result of the comparison is false.
         */
        JSValue src1 = callFrame->r(vPC[1].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[2].u.operand).jsValue();
        int target = vPC[3].u.operand;
        bool result = jsLess<true>(callFrame, src1, src2);

        if (labelReq && !isPolicy) {
//            JSLabel contextLabel = callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel());
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            JSLabel contextLabel;
            JSLabel tdstLabel = (callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel()));
            uint64_t dstL = tdstLabel.Val();
            /*
            if (pcLabel <= tdstLabel) {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t bits = BitMap::Bitmap().getBits(i);
                        uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                        uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                        if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                            dstL = dstL | aLabel;
                        }
                        else {
                            BitMap::Bitmap().setBits(i, bits - 1);
                            dstL = dstL | dLabel;
                        }
                    }
                    i = i << 1;
                }
            }
            else {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                        dstL = dstL | dLabel;
                    }
                    i = i << 1;
                }
            }*/
            contextLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            
        // IFC4BC -- To push context label on the pcstack
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
            CHECK_FOR_EXCEPTION(contextLabel);
        }
        else {
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
        }
        // IFC4BC ---------------------------------------
                
        if (!result) {
            vPC += target;
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_jnless);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_jnlesseq) {
        /* jnlesseq src1(r) src2(r) target(offset)
         
         Checks whether register src1 is less than or equal to
         register src2, as with the ECMAScript '<=' operator,
         and then jumps to offset target from the current instruction,
         if and only if theresult of the comparison is false.
         */
        JSValue src1 = callFrame->r(vPC[1].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[2].u.operand).jsValue();
        int target = vPC[3].u.operand;
        bool result = jsLessEq<true>(callFrame, src1, src2);

        if (labelReq && !isPolicy) {
//            JSLabel contextLabel = callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel());
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            JSLabel contextLabel;
            JSLabel tdstLabel = (callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel()));
            uint64_t dstL = tdstLabel.Val();
            /*
            if (pcLabel <= tdstLabel) {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t bits = BitMap::Bitmap().getBits(i);
                        uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                        uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                        if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                            dstL = dstL | aLabel;
                        }
                        else {
                            BitMap::Bitmap().setBits(i, bits - 1);
                            dstL = dstL | dLabel;
                        }
                    }
                    i = i << 1;
                }
            }
            else {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                        dstL = dstL | dLabel;
                    }
                    i = i << 1;
                }
            }*/
            contextLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            
            // IFC4BC -- To push context label on the pcstack
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
            CHECK_FOR_EXCEPTION(contextLabel);
        }
        else {
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
            
        }
        // IFC4BC ---------------------------------------

        if (!result) {
            vPC += target;
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_jnlesseq);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_jngreater) {
        /* jngreater src1(r) src2(r) target(offset)
         
         Checks whether register src1 is greater than register src2, as
         with the ECMAScript '>' operator, and then jumps to offset
         target from the current instruction, if and only if the
         result of the comparison is false.
         */
        JSValue src1 = callFrame->r(vPC[1].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[2].u.operand).jsValue();
        int target = vPC[3].u.operand;
        bool result = jsLess<false>(callFrame, src2, src1);
        
        if (labelReq && !isPolicy) {
//            JSLabel contextLabel = callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel());
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            JSLabel contextLabel;
            JSLabel tdstLabel = (callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel()));
            uint64_t dstL = tdstLabel.Val();
            /*
            if (pcLabel <= tdstLabel) {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t bits = BitMap::Bitmap().getBits(i);
                        uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                        uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                        if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                            dstL = dstL | aLabel;
                        }
                        else {
                            BitMap::Bitmap().setBits(i, bits - 1);
                            dstL = dstL | dLabel;
                        }
                    }
                    i = i << 1;
                }
            }
            else {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                        dstL = dstL | dLabel;
                    }
                    i = i << 1;
                }
            }*/
            contextLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            
            // IFC4BC -- To push context label on the pcstack
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
            CHECK_FOR_EXCEPTION(contextLabel);
        }
        else {
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
        }
        // IFC4BC ---------------------------------------
        
        if (!result) {
            vPC += target;
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_jngreater);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_jngreatereq) {
        /* jngreatereq src1(r) src2(r) target(offset)
         
         Checks whether register src1 is greater than or equal to
         register src2, as with the ECMAScript '>=' operator,
         and then jumps to offset target from the current instruction,
         if and only if theresult of the comparison is false.
         */
        JSValue src1 = callFrame->r(vPC[1].u.operand).jsValue();
        JSValue src2 = callFrame->r(vPC[2].u.operand).jsValue();
        int target = vPC[3].u.operand;
        bool result = jsLessEq<false>(callFrame, src2, src1);
        
        if (labelReq && !isPolicy) {
//            JSLabel contextLabel = callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel());
//            if (contextLabel >= pcLabel) {
//                uint64_t i = 1;
//                uint64_t pLabel = contextLabel.pLabel;
//                for (int j = 1; j <= 64; j++) {
//                    if (pLabel & i) {
//                        uint64_t bits = BitMap::Bitmap().getBits(i);
//                        if (bits) {
//                            BitMap::Bitmap().setBits(i, bits - 1);
//                            pLabel = pLabel ^ i;
//                        }
//                    }
//                    i = i << 1;
//                }
//                contextLabel.pLabel = pLabel;
//            }
            JSLabel contextLabel;
            JSLabel tdstLabel = (callFrame->r(vPC[1].u.operand).getRegLabel().Join(callFrame->r(vPC[2].u.operand).getRegLabel()));
            uint64_t dstL = tdstLabel.Val();
            /*
            if (pcLabel <= tdstLabel) {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t bits = BitMap::Bitmap().getBits(i);
                        uint64_t dLabel = BitMap::Bitmap().getRelLabel(i);
                        uint64_t aLabel = BitMap::Bitmap().getVarLabel(i);
                        if (!bits || !(JSLabel(dLabel, 0) <= tdstLabel) || !(tdstLabel <= JSLabel(dLabel, 0))) {
                            dstL = dstL | aLabel;
                        }
                        else {
                            BitMap::Bitmap().setBits(i, bits - 1);
                            dstL = dstL | dLabel;
                        }
                    }
                    i = i << 1;
                }
            }
            else {
                uint64_t i = 1;
                uint64_t pLabel = tdstLabel.pLabel;
                tdstLabel.pLabel = 0;
                for (int j = 1; j <= 64; j++) {
                    if (pLabel & i) {
                        uint64_t dLabel = BitMap::Bitmap().getVarLabel(i);
                        dstL = dstL | dLabel;
                    }
                    i = i << 1;
                }
            }*/
            contextLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(JSLabel(dstL));
            
            // IFC4BC -- To push context label on the pcstack
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
            CHECK_FOR_EXCEPTION(contextLabel);
        }
        else {
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
        }
        // IFC4BC ---------------------------------------
                
        if (!result) {
            vPC += target;
             NEXT_INSTRUCTION();
        }
        
        vPC += OPCODE_LENGTH(op_jngreatereq);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_switch_imm) {
        /* switch_imm tableIndex(n) defaultOffset(offset) scrutinee(r)
         
         Performs a range checked switch on the scrutinee value, using
         the tableIndex-th immediate switch jump table.  If the scrutinee value
         is an immediate number in the range covered by the referenced jump
         table, and the value at jumpTable[scrutinee value] is non-zero, then
         that value is used as the jump offset, otherwise defaultOffset is used.
         */
        int tableIndex = vPC[1].u.operand;
        int defaultOffset = vPC[2].u.operand;
        JSValue scrutinee = callFrame->r(vPC[3].u.operand).jsValue();
        
        if (labelReq && !isPolicy) {
            JSLabel contextLabel = callFrame->r(vPC[3].u.operand).getRegLabel();
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
        }
        
        if (scrutinee.isInt32())
            vPC += codeBlock->immediateSwitchJumpTable(tableIndex).offsetForValue(scrutinee.asInt32(), defaultOffset);
        else if (scrutinee.isDouble() && scrutinee.asDouble() == static_cast<int32_t>(scrutinee.asDouble()))
            vPC += codeBlock->immediateSwitchJumpTable(tableIndex).offsetForValue(static_cast<int32_t>(scrutinee.asDouble()), defaultOffset);
        else
            vPC += defaultOffset;
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_switch_char) {
        /* switch_char tableIndex(n) defaultOffset(offset) scrutinee(r)
         
         Performs a range checked switch on the scrutinee value, using
         the tableIndex-th character switch jump table.  If the scrutinee value
         is a single character string in the range covered by the referenced jump
         table, and the value at jumpTable[scrutinee value] is non-zero, then
         that value is used as the jump offset, otherwise defaultOffset is used.
         */
        int tableIndex = vPC[1].u.operand;
        int defaultOffset = vPC[2].u.operand;
        JSValue scrutinee = callFrame->r(vPC[3].u.operand).jsValue();
        if (labelReq && !isPolicy) {
            JSLabel contextLabel = callFrame->r(vPC[3].u.operand).getRegLabel();
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
        }
        if (!scrutinee.isString())
            vPC += defaultOffset;
        else {
            StringImpl* value = asString(scrutinee)->value(callFrame).impl();
            if (value->length() != 1)
                vPC += defaultOffset;
            else
                vPC += codeBlock->characterSwitchJumpTable(tableIndex).offsetForValue((*value)[0], defaultOffset);
        }
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_switch_string) {
        /* switch_string tableIndex(n) defaultOffset(offset) scrutinee(r)
         
         Performs a sparse hashmap based switch on the value in the scrutinee
         register, using the tableIndex-th string switch jump table.  If the 
         scrutinee value is a string that exists as a key in the referenced 
         jump table, then the value associated with the string is used as the 
         jump offset, otherwise defaultOffset is used.
         */
        int tableIndex = vPC[1].u.operand;
        int defaultOffset = vPC[2].u.operand;
        JSValue scrutinee = callFrame->r(vPC[3].u.operand).jsValue();
        if (labelReq && !isPolicy) {
            JSLabel contextLabel = callFrame->r(vPC[3].u.operand).getRegLabel();
            if (contextLabel.Star())
                ABORT_TRANSACTION();
            OP_BRANCH(contextLabel);
        }
        if (!scrutinee.isString())
            vPC += defaultOffset;
        else 
            vPC += codeBlock->stringSwitchJumpTable(tableIndex).offsetForValue(asString(scrutinee)->value(callFrame).impl(), defaultOffset);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_new_func) {
        /* new_func dst(r) func(f)
         
         Constructs a new Function instance from function func and
         the current scope chain using the original Function
         constructor, using the rules for function declarations, and
         puts the result in register dst.
         */
        int dst = vPC[1].u.operand;
        int func = vPC[2].u.operand;
        int shouldCheck = vPC[3].u.operand;
        ASSERT(codeBlock->codeType() != FunctionCode || !codeBlock->needsFullScopeChain() || callFrame->r(codeBlock->activationRegister()).jsValue());
        
        //IFC4BC
        if (!shouldCheck || !callFrame->r(dst).jsValue()) {
            JSValue fV = JSValue(codeBlock->functionDecl(func)->make(callFrame, callFrame->scopeChain()));
            fV.asCell()->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            fV.asCell()->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            if (labelReq && !isPolicy) {
                JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
                if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                    printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                    dstLabel.setStar(true);
                }
                else
                {
                    // dstLabel.setStar(false);
                }
                callFrame->uncheckedR(dst) = fV;
                callFrame->uncheckedR(dst).setRegLabel(dstLabel);
            }
            else {
                callFrame->uncheckedR(dst) = fV;                
            }
            // Original
            // callFrame->uncheckedR(dst) = JSValue(codeBlock->functionDecl(func)->make(callFrame, callFrame->scopeChain()));
            
        }
        
        vPC += OPCODE_LENGTH(op_new_func);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_new_func_exp) {
        /* new_func_exp dst(r) func(f)
         
         Constructs a new Function instance from function func and
         the current scope chain using the original Function
         constructor, using the rules for function expressions, and
         puts the result in register dst.
         */
        int dst = vPC[1].u.operand;
        int funcIndex = vPC[2].u.operand;
        
        ASSERT(codeBlock->codeType() != FunctionCode || !codeBlock->needsFullScopeChain() || callFrame->r(codeBlock->activationRegister()).jsValue());
        
        FunctionExecutable* function = codeBlock->functionExpr(funcIndex);
        JSFunction* func = function->make(callFrame, callFrame->scopeChain());
        // IFC4BC - Set the object and prototype chain labels
        func->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
        func->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
        
        /* 
         The Identifier in a FunctionExpression can be referenced from inside
         the FunctionExpression's FunctionBody to allow the function to call
         itself recursively. However, unlike in a FunctionDeclaration, the
         Identifier in a FunctionExpression cannot be referenced from and
         does not affect the scope enclosing the FunctionExpression.
         */
        if (!function->name().isNull()) {
            JSStaticScopeObject* functionScopeObject = JSStaticScopeObject::create(callFrame, function->name(), func, ReadOnly | DontDelete);
            func->setScope(*globalData, func->scope()->push(functionScopeObject));
        }
        // IFC4BC - Setting the value label
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            else
            {
                // dstLabel.setStar(false);
            }
            callFrame->uncheckedR(dst) = JSValue(func);
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = JSValue(func);
        }
        
        vPC += OPCODE_LENGTH(op_new_func_exp);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_call_eval) {
        /* call_eval func(r) argCount(n) registerOffset(n)
         
         Call a function named "eval" with no explicit "this" value
         (which may therefore be the eval operator). If register
         thisVal is the global object, and register func contains
         that global object's original global eval function, then
         perform the eval operator in local scope (interpreting
         the argument registers as for the "call"
         opcode). Otherwise, act exactly as the "call" opcode would.
         */
        
        int func = vPC[1].u.operand;
        int argCount = vPC[2].u.operand;
        int registerOffset = vPC[3].u.operand;
        
        ASSERT(codeBlock->codeType() != FunctionCode || !codeBlock->needsFullScopeChain() || callFrame->r(codeBlock->activationRegister()).jsValue());
        JSValue funcVal = callFrame->r(func).jsValue();
        
        if (isHostFunction(funcVal, globalFuncEval)) {
            CallFrame* newCallFrame = CallFrame::create(callFrame->registers() + registerOffset);
            newCallFrame->init(0, vPC + OPCODE_LENGTH(op_call_eval), callFrame->scopeChain(), callFrame, argCount, jsCast<JSFunction*>(funcVal));
            
            // IFC4BC
            // We can use dummy values here because we're popping immediately
            // and we're guaranteed to not have anything left on the stack
            // by the Eval Call
            
            // Include exception handler value
            // Checking if handler exists in this function
            int num = 0;
            const size_t numHandlers = codeBlock->numberOfExceptionHandlers();
            HandlerInfo* hInfo;
            bool existsHandler = false;
            int pos = vPC - iBegin;
            // Get number of instructions
            while ((unsigned)num < numHandlers) {
                hInfo = &codeBlock->exceptionHandler(num++);
                if ((hInfo->start <= (unsigned)pos) && (hInfo->end > (unsigned)pos)) {
                    existsHandler = true;
                    break;
                }
            }
            
            // Pushing funcVal.getLabel for now. Need to check this, when testing eval.
            if (labelReq) {
                JSLabel funcLabel = asObject(funcVal)->getObjectLabel();
                if (funcLabel.Star())
                {
                    printf("Function object contains a star in call_eval\n");
                }
                funcLabel = funcLabel.Join(callFrame->r(func).getRegLabel());
                OP_CALLBRANCH(funcLabel, (existsHandler || pcstack.excHandler()), existsHandler);
            }
            //---------------------------------------------------------------//
            
            JSValue result = eval(newCallFrame);
            if ((exceptionValue = globalData->exception))
                goto vm_throw;
            functionReturnValue = result;
            
            vPC += OPCODE_LENGTH(op_call_eval);
             NEXT_INSTRUCTION();
        }
        
        // We didn't find the blessed version of eval, so process this
        // instruction as a normal function call.
        // fall through to op_call
    }
    DEFINE_OPCODE(op_call) {
        /* call func(r) argCount(n) registerOffset(n)
         
         Perform a function call.
         
         registerOffset is the distance the callFrame pointer should move
         before the VM initializes the new call frame's header.
         
         dst is where op_ret should store its result.
         */
        
        int func = vPC[1].u.operand;
        int argCount = vPC[2].u.operand;
        int registerOffset = vPC[3].u.operand;
        
        JSValue v = callFrame->r(func).jsValue();
        
        CallData callData;
        CallType callType = getCallData(v, callData);
        
        
        if (callType == CallTypeJS) {
            ScopeChainNode* callDataScopeChain = callData.js.scopeChain;
            
            JSObject* error = callData.js.functionExecutable->compileForCall(callFrame, callDataScopeChain);
            if (UNLIKELY(!!error)) {
                exceptionValue = error;
                goto vm_throw;
            }
            
            CallFrame* previousCallFrame = callFrame;
            CodeBlock* newCodeBlock = &callData.js.functionExecutable->generatedBytecodeForCall();
            
            // If it is a different function call, then we would need the label to be propagated.
            // IFC4BC - Checking for exception handlers
            int num = 0;
            const size_t numHandlers = codeBlock->numberOfExceptionHandlers();
            HandlerInfo* hInfo;
            bool existsHandler = false;
            int pos = vPC - iBegin;
            // Get number of instructions
            while ((unsigned)num < numHandlers) {
                hInfo = &codeBlock->exceptionHandler(num++);
                if ((hInfo->start <= (unsigned)pos) && (hInfo->end > (unsigned)pos)) {
                    existsHandler = true;
                    break;
                }
            }
            
            JSLabel funcLabel = asObject(v)->getObjectLabel();
            // newCodeBlock->contextLabel = JSLabel(URLMap::urlmap().getLabel(callData.js.functionExecutable->sourceURL().utf8().data()));
            /*
            if (funcLabel.Val() == 0)
            {
                funcLabel = JSLabel(URLMap::urlmap().getLabel(callData.js.functionExecutable->sourceURL().utf8().data()));
                newCodeBlock->contextLabel = funcLabel;
                funcLabel.setVal(0);
                asObject(v)->setObjectLabel(funcLabel);
                asObject(v)->structure()->setProtoLabel(funcLabel);
            }
             */
            
            // if ((pcLabel/*.Join(codeBlock->contextLabel)*/ != funcLabel || !(JSLabelMap::labelMap().isOrdered(pcLabel.Val(), funcLabel.Val()))) && !labelReq)
            if ((pcLabel != funcLabel) && !labelReq)
            {
                labelReq = true;
                labelRegisters(callFrame, codeBlock, pcLabel);
            }
            
            if (labelReq && !isPolicy) {
                if (funcLabel.Star())
                {
                    printf("Function object contains a star in call\n");
                }
                funcLabel = funcLabel.Join(callFrame->r(func).getRegLabel());
                OP_CALLBRANCH(funcLabel, (existsHandler || pcstack.excHandler()), existsHandler);
            }
            else {
                OP_CALLBRANCH(pcstack.Head(), (existsHandler || pcstack.excHandler()), existsHandler);
            }
            pcLabel = pcstack.Head();
            pcLabel.setStar(false);
            JSLabel::pcGlobalLabel = pcLabel.getPair();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();

            printf("Function call %p from %p at %ld with label %lld\n", newCodeBlock, codeBlock, vPC - iBegin, pcLabel.Val());
            // OP_CALLBRANCH(pcstack.Head(), (existsHandler || pcstack.excHandler()), existsHandler);
            
            // For cases when the call itself has two possible paths
            /*
            if ((int(vPC - iBegin) + OPCODE_LENGTH(op_call)) != pcIPD ||
                pcstack.Reg() != callFrame->registers())
            {
                pcstack.Join(pcstack.Head(), true);
            }
             */
            //-----------------------------------------
            // printf("The pc is %lld\n", pcstack.Head().Val());
            
            callFrame = slideRegisterWindowForCall(newCodeBlock, registerFile, callFrame, registerOffset, argCount);
            if (UNLIKELY(!callFrame)) {
                callFrame = previousCallFrame;
                exceptionValue = createStackOverflowError(callFrame);
                goto vm_throw;
            }
            
            // IFC4BC - Create CFG
            if (pcstack.excHandler()) {
                // SEN exists
                if (!newCodeBlock->has_SENanalysis) {
                    newCodeBlock->analyzerSEN.genContextTable(newCodeBlock, this, pcstack.excHandler());
                    newCodeBlock->has_SENanalysis = true;
                }
                newCodeBlock->analyzer = newCodeBlock->analyzerSEN;
            }
            else {
                // No exception handler
                if (!newCodeBlock->has_analysis) {
                    newCodeBlock->analyzerNOR.genContextTable(newCodeBlock, this, pcstack.excHandler());
                    newCodeBlock->has_analysis = true;
                }
                newCodeBlock->analyzer = newCodeBlock->analyzerNOR;
            }
            // -------------------------
            
            callFrame->init(newCodeBlock, vPC + OPCODE_LENGTH(op_call), callDataScopeChain, previousCallFrame, argCount, jsCast<JSFunction*>(v));
            
            // IFC4BC - Labelling the arguments with the context
            // -7 is the first register where the argument resides. 6 is the callframe header size.
            /*
            if (labelReq) {
                for(int i = -7, j = 1; j <= newCodeBlock->numParameters(); j++, i--)
                {
                    // Can assign just pc as it is already a join
                    if (j <= argCount)
                        callFrame->uncheckedR(i).setRegLabel(callFrame->r(i).getRegLabel().Join(pcLabel));
                }
            }
             */
            //------
            
            codeBlock = newCodeBlock;
            ASSERT(codeBlock == callFrame->codeBlock());
            *topCallFrameSlot = callFrame;
            vPC = newCodeBlock->instructions().begin();
            iBegin = newCodeBlock->instructions().begin();
            
#if ENABLE(OPCODE_STATS)
            OpcodeStats::resetLastInstruction();
#endif
            
             NEXT_INSTRUCTION();
        }
        
        if (callType == CallTypeHost) {
            // IFC4BC - Passing the label to WebCore
            JSLabel::pcGlobalLabel = pcLabel.getPair();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
            ScopeChainNode* scopeChain = callFrame->scopeChain();
            CallFrame* newCallFrame = CallFrame::create(callFrame->registers() + registerOffset);
            newCallFrame->init(0, vPC + OPCODE_LENGTH(op_call), scopeChain, callFrame, argCount, asObject(v));
            JSValue returnValue;
            JSLabel argumentsLabel = JSLabel();
            
            if (labelReq && !isPolicy) {
                // IFC4BC - Passing the argument labels
                for (int i = 0, j = -7; i < argCount; i++, j--) {
                    if (i == 100) {
                        printf("More than 100 arguments to native function call\n");
                        // ABORT_CALL();
                        break;
                    }
                    
                    if (i != 0)
                    {
                        JSLabel::argLabel[i] = newCallFrame->r(j).getRegLabel().Join(pcLabel/*.Join(codeBlock->contextLabel)*/).getPair();
                    }
                    else
                    {
                        JSLabel::argLabel[i] = newCallFrame->r(j).getRegLabel().getPair();
                    }
                     
                    argumentsLabel = argumentsLabel.Join(newCallFrame->r(j).getRegLabel());
                }
            }
            
            {
                *topCallFrameSlot = newCallFrame;
                SamplingTool::HostCallRecord callRecord(m_sampler.get());
                returnValue = (callData.native.function(newCallFrame));
                *topCallFrameSlot = callFrame;
            }
            
            if (!isPolicy)
                for (int i = -1; i >= -6; i--)
                    newCallFrame->uncheckedR(i).setRegLabel(pcLabel);
            
            // IFC4BC
            if (isPolicy && isSetLabel) // Did the policy set the label for global variable?
            {
                isSetLabel = false;
                if (rPointer != 0) {
                    JSGlobalObject* scope = codeBlock->globalObject();
                    ASSERT(scope->isGlobalObject());
                    JSValue rVal = rPointer->get();
                    if (rVal == returnValue) {
                        rPointer->set(*globalData, scope, returnValue);
                        rPointer = 0;
                    }
                }
                else if (strcmp(vIdent.ustring().utf8().data(),"NULL") != 0) {
                    PutPropertySlot slot(codeBlock->isStrictMode());
                    vValue.put(callFrame, vIdent, returnValue, slot);
                    vIdent = Identifier(callFrame, "NULL");
                }
            }
                
            if (JSLabel::ABORT_FLAG) {
                JSLabel::ABORT_FLAG = false;
                ABORT_TRANSACTION();
            }
            
            // Join the return value with the pc in which it was performed
            // !!!!!! - Do not join the pc. It does not give the right label
            // TODO
            if (!isPolicy)
            {
                returnValue.setValueLabel(returnValue.joinValueLabel(pcLabel/*.Join(codeBlock->contextLabel)*/.Join(argumentsLabel)));
            }
            returnValue.setValueLabel(returnValue.joinValueLabel(JSLabel::returnLabel));
            JSLabel::returnLabel = JSLabel().getPair();
            if (returnValue.getValueLabel().Val() != pcLabel/*.Join(codeBlock->contextLabel)*/.Val() && !labelReq)
            {
                labelReq = true;
                labelRegisters(callFrame, codeBlock, pcLabel);
            }
            
            // Reset the argLabel to 0.
            if (!isPolicy)
                for (int i = 0; i < argCount; i++) {
                    JSLabel::argLabel[i] = JSLabel().getPair();
                }
            
            JSLabel::pcGlobalLabel = pcLabel.getPair();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
            
            CHECK_FOR_EXCEPTION(returnValue.getValueLabel());
            
            functionReturnValue = returnValue;
            
            vPC += OPCODE_LENGTH(op_call);
             NEXT_INSTRUCTION();
        }
        
        ASSERT(callType == CallTypeNone);
        
        exceptionValue = createNotAFunctionError(callFrame, v);
        goto vm_throw;
    }
    DEFINE_OPCODE(op_call_varargs) {
        /* call_varargs callee(r) thisValue(r) arguments(r) firstFreeRegister(n)
         
         Perform a function call with a dynamic set of arguments.
         
         registerOffset is the distance the callFrame pointer should move
         before the VM initializes the new call frame's header, excluding
         space for arguments.
         
         dst is where op_ret should store its result.
         */
        
        JSValue v = callFrame->r(vPC[1].u.operand).jsValue();
        JSValue thisValue = callFrame->r(vPC[2].u.operand).jsValue();
        JSValue arguments = callFrame->r(vPC[3].u.operand).jsValue();
        int firstFreeRegister = vPC[4].u.operand;
        
        CallFrame* newCallFrame = loadVarargs(callFrame, registerFile, thisValue, arguments, firstFreeRegister);
        if ((exceptionValue = globalData->exception))
            goto vm_throw;
        int argCount = newCallFrame->argumentCountIncludingThis();
        
        CallData callData;
        CallType callType = getCallData(v, callData);
        
        if (callType == CallTypeJS) {
            ScopeChainNode* callDataScopeChain = callData.js.scopeChain;
            
            JSObject* error = callData.js.functionExecutable->compileForCall(callFrame, callDataScopeChain);
            if (UNLIKELY(!!error)) {
                exceptionValue = error;
                goto vm_throw;
            }
            
            CodeBlock* newCodeBlock = &callData.js.functionExecutable->generatedBytecodeForCall();
            newCallFrame = slideRegisterWindowForCall(newCodeBlock, registerFile, newCallFrame, 0, argCount);
            if (UNLIKELY(!newCallFrame)) {
                exceptionValue = createStackOverflowError(callFrame);
                goto vm_throw;
            }
            
            // If it is a different function call, then we would need the label to be propagated.
            // IFC4BC - Checking for exception handlers
            int num = 0;
            const size_t numHandlers = codeBlock->numberOfExceptionHandlers();
            HandlerInfo* hInfo;
            bool existsHandler = false;
            int pos = vPC - iBegin;
            // Get number of instructions
            while ((unsigned)num < numHandlers) {
                hInfo = &codeBlock->exceptionHandler(num++);
                if ((hInfo->start <= (unsigned)pos) && (hInfo->end > (unsigned)pos)) {
                    existsHandler = true;
                    break;
                }
            }
            
            JSLabel funcLabel = asObject(v)->getObjectLabel();
            // newCodeBlock->contextLabel = JSLabel(URLMap::urlmap().getLabel(callData.js.functionExecutable->sourceURL().utf8().data()));
//            if (funcLabel.Val() == 0) {
//                // IFC4BC - Getting the label for functions defined globally
//                //const char* sURl2 = callData.js.functionExecutable->sourceURL().utf8().data();
//                //char *temp1 = strstr(sURl2, ".policy");
//                
//                //if(temp1) funcLabel = JSLabel(URLMap::urlmap().getLabel(sURl2, 1));
//                funcLabel = JSLabel(URLMap::urlmap().getLabel(callData.js.functionExecutable->sourceURL().utf8().data()));
//
//                asObject(v)->setObjectLabel(funcLabel);
//                asObject(v)->structure()->setProtoLabel(funcLabel);
//            }
//            newCodeBlock->contextLabel = funcLabel;
            /*
            if (funcLabel.iVal() == 0xffffffffffffffff)
            {
                funcLabel = JSLabel(URLMap::urlmap().getLabel(callData.js.functionExecutable->sourceURL().utf8().data()));
                newCodeBlock->contextLabel = funcLabel;
                funcLabel.setVal(0);
                asObject(v)->setObjectLabel(funcLabel);
                asObject(v)->structure()->setProtoLabel(funcLabel);
                // newCodeBlock->contextLabel = funcLabel;
            }
            */
            // if ((funcLabel != pcLabel || !(JSLabelMap::labelMap().isOrdered(pcLabel.Val(), funcLabel.Val()))) && !labelReq)
            if ((funcLabel != pcLabel) && !labelReq)
            {
                labelReq = true;
                labelRegisters(callFrame, codeBlock, pcLabel);
            }
            if (labelReq && !isPolicy) {
                if (funcLabel.Star())
                {
                    printf("Function object contains a star in call\n");
                }
                funcLabel = funcLabel.Join(callFrame->r(vPC[1].u.operand).getRegLabel());
                OP_CALLBRANCH(funcLabel, (existsHandler || pcstack.excHandler()), existsHandler);
            }
            else {
                OP_CALLBRANCH(pcstack.Head(), (existsHandler || pcstack.excHandler()), existsHandler);
            }
            
            pcLabel = pcstack.Head();
            pcLabel.setStar(false);
            JSLabel::pcGlobalLabel = pcLabel.getPair();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
            // printf("Function call with label %lld\n", pcLabel.Val());
            // printf("Function call varargs %p from %p at %ld with label %lld\n", newCodeBlock,
                   // codeBlock, vPC - iBegin, pcLabel.Val());

            OP_CALLBRANCH(pcstack.Head(), (existsHandler || pcstack.excHandler()), existsHandler);
            
            // For cases when the call_varargs itself has two possible paths
            /*
            if ((int(vPC - iBegin) + OPCODE_LENGTH(op_call_varargs)) != pcIPD ||
                pcstack.Reg() != callFrame->registers())
            {
                pcstack.Join(pcstack.Head(), true);
            }
             */
            
            if (pcstack.excHandler()) {
                // SEN exists
                if (!newCodeBlock->has_SENanalysis) {
                    newCodeBlock->analyzerSEN.genContextTable(newCodeBlock, this, pcstack.excHandler());
                    newCodeBlock->has_SENanalysis = true;
                }
                newCodeBlock->analyzer = newCodeBlock->analyzerSEN;
            }
            else {
                // No exception handler
                if (!newCodeBlock->has_analysis) {
                    newCodeBlock->analyzerNOR.genContextTable(newCodeBlock, this, pcstack.excHandler());
                    newCodeBlock->has_analysis = true;
                }
                newCodeBlock->analyzer = newCodeBlock->analyzerNOR;
            }
            // -------------------------
            
            newCallFrame->init(newCodeBlock, vPC + OPCODE_LENGTH(op_call_varargs), callDataScopeChain, callFrame, argCount, jsCast<JSFunction*>(v));
            
            codeBlock = newCodeBlock;
            callFrame = newCallFrame;
            ASSERT(codeBlock == callFrame->codeBlock());
            *topCallFrameSlot = callFrame;
            vPC = newCodeBlock->instructions().begin();
            iBegin = newCodeBlock->instructions().begin();

            // IFC4BC - Labelling the arguments with the context
            // -7 is the first register where the argument resides. 6 is the callframe header size.
            /*
            if (labelReq) {
                for(int i = -7, j = 1; j <= newCodeBlock->numParameters(); j++, i--)
                    if (j <= argCount)
                        callFrame->uncheckedR(i).setRegLabel(callFrame->r(i).getRegLabel().Join(pcLabel));
            }
             */
            //------
            
#if ENABLE(OPCODE_STATS)
            OpcodeStats::resetLastInstruction();
#endif
            
             NEXT_INSTRUCTION();
        }
        
        if (callType == CallTypeHost) {
            JSLabel::pcGlobalLabel = pcLabel.getPair();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
            ScopeChainNode* scopeChain = callFrame->scopeChain();
            newCallFrame->init(0, vPC + OPCODE_LENGTH(op_call_varargs), scopeChain, callFrame, argCount, asObject(v));
            
            JSValue returnValue;
            JSLabel argumentsLabel = JSLabel();
            
            if (labelReq && !isPolicy) {
                // IFC4BC - Passing the argument labels
                for (int i = 0, j = -7; i < argCount; i++, j--) {
                    if (i == 100) {
                        printf("More than 100 arguments to native function call_varargs\n");
                        // ABORT_CALL();
                        break;
                    }
                    
                    if (i != 0)
                    {
                        JSLabel::argLabel[i] = newCallFrame->r(j).getRegLabel().Join(pcLabel).getPair();
                    }
                    else
                    {
                        JSLabel::argLabel[i] = newCallFrame->r(j).getRegLabel().getPair();
                    }
                     
                    argumentsLabel = argumentsLabel.Join(newCallFrame->r(j).getRegLabel());
                }
            }
            {
                *topCallFrameSlot = newCallFrame;
                SamplingTool::HostCallRecord callRecord(m_sampler.get());
                returnValue = (callData.native.function(newCallFrame));
                *topCallFrameSlot = callFrame;
            }
            if (!isPolicy)
                for (int i = -1; i >= -6; i--)
                    newCallFrame->uncheckedR(i).setRegLabel(pcLabel);
            
            // IFC4BC
            if (JSLabel::ABORT_FLAG) {
                JSLabel::ABORT_FLAG = false;
                ABORT_TRANSACTION();
            }
            
            // Join the return value with the pc in which it was performed
            returnValue.setValueLabel(returnValue.joinValueLabel(pcLabel/*.Join(codeBlock->contextLabel)*/.Join(argumentsLabel)));
            returnValue.setValueLabel(returnValue.joinValueLabel(JSLabel::returnLabel));
            JSLabel::returnLabel = JSLabel().getPair();
            if (returnValue.getValueLabel().Val() != pcLabel/*.Join(codeBlock->contextLabel)*/.Val() && !labelReq)
            {
                labelReq = true;
                labelRegisters(callFrame, codeBlock, pcLabel/*.Join(codeBlock->contextLabel)*/);
            }
            // Reset the argLabel to 0.
            
            for (int i = 0; i < argCount; i++) {
                JSLabel::argLabel[i] = JSLabel().getPair();
            }
            
            JSLabel::pcGlobalLabel = pcLabel.getPair();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
            
            CHECK_FOR_EXCEPTION(returnValue.getValueLabel());
            
            functionReturnValue = returnValue;
            
            vPC += OPCODE_LENGTH(op_call_varargs);
             NEXT_INSTRUCTION();
        }
        
        ASSERT(callType == CallTypeNone);
        
        exceptionValue = createNotAFunctionError(callFrame, v);
        goto vm_throw;
    }
    DEFINE_OPCODE(op_tear_off_activation) {
        /* tear_off_activation activation(r) arguments(r)
         
         Copy locals and named parameters from the register file to the heap.
         Point the bindings in 'activation' and 'arguments' to this new backing
         store. (Note that 'arguments' may not have been created. If created,
         'arguments' already holds a copy of any extra / unnamed parameters.)
         
         This opcode appears before op_ret in functions that require full scope chains.
         */
        
        int activation = vPC[1].u.operand;
        int arguments = vPC[2].u.operand;
        ASSERT(codeBlock->needsFullScopeChain());
        JSValue activationValue = callFrame->r(activation).jsValue();
        // IFC4BC - Need to check if the value contains star in DNSU. Do we need to check anything else before writing to the heap?
        // Label the activation object being copied
        
        if (activationValue) {
            if (callFrame->r(activation).getRegLabel().Star())
                ABORT_TRANSACTION();
            
            asActivation(activationValue)->tearOff(*globalData);
            
            if (JSValue argumentsValue = callFrame->r(unmodifiedArgumentsRegister(arguments)).jsValue())
                asArguments(argumentsValue)->didTearOffActivation(*globalData, asActivation(activationValue));
        } else if (JSValue argumentsValue = callFrame->r(unmodifiedArgumentsRegister(arguments)).jsValue()) {
            if (!codeBlock->isStrictMode())
                asArguments(argumentsValue)->tearOff(callFrame);
        }
        
        vPC += OPCODE_LENGTH(op_tear_off_activation);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_tear_off_arguments) {
        /* tear_off_arguments arguments(r)
         
         Copy named parameters from the register file to the heap. Point the
         bindings in 'arguments' to this new backing store. (Note that
         'arguments' may not have been created. If created, 'arguments' already
         holds a copy of any extra / unnamed parameters.)
         
         This opcode appears before op_ret in functions that don't require full
         scope chains, but do use 'arguments'.
         */
        
        int src1 = vPC[1].u.operand;
        ASSERT(!codeBlock->needsFullScopeChain() && codeBlock->ownerExecutable()->usesArguments());
        
        if (callFrame->r(src1).getRegLabel().Star())
            ABORT_TRANSACTION();
        
        if (JSValue arguments = callFrame->r(unmodifiedArgumentsRegister(src1)).jsValue())
            asArguments(arguments)->tearOff(callFrame);
        
        vPC += OPCODE_LENGTH(op_tear_off_arguments);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_ret) {
        /* ret result(r)
         
         Return register result as the return value of the current
         function call, writing it into functionReturnValue.
         In addition, unwind one call frame and restore the scope
         chain, code block instruction pointer and register base
         to those of the calling function.
         */
        
        int count = (int) (codeBlock->instructions().end() - iBegin);
        int current = (int) (vPC - iBegin);
        bool popNow = false;
        bool dontPop = false;
        
        // With multiple rets, IPD will be the last ret always. Checking for last ret.
        if ((pcstack.Reg() == callFrame->registers()))
        {
            if (((pcIPD == count - 2) || (pcIPD == count - 3)) && ((current == count - 2 || current == count - 3)))
            {
                popNow = true;
            }
        }
        else
        {
            dontPop = true;
        }
        if (popNow)
        {
            pcstack.Pop();
            pcIPD = pcstack.Loc();
            pcSLen = pcstack.Len();
            pcReg = pcstack.Reg();
            pcLabel = pcstack.Head();
            pcLabel.setStar(false);
            JSLabel::pcGlobalLabel = pcLabel.getPair();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
        }
        int result = vPC[1].u.operand;
        
        JSValue returnValue = callFrame->r(result).jsValue();
        returnValue.setValueLabel(callFrame->r(result).getRegLabel().Join(pcLabel/*.Join(codeBlock->contextLabel)*/));
        
        CallFrame* prevCallFrame = callFrame;
        
        if (!popNow && !dontPop)
        {
            pcstack.Pop();
            pcLabel = pcstack.Head();
            pcIPD = pcstack.Loc();
            pcSLen = pcstack.Len();
            pcReg = pcstack.Reg();
            pcLabel.setStar(false);
            JSLabel::pcGlobalLabel = pcLabel.getPair();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
        }

        vPC = callFrame->returnVPC();
        callFrame = callFrame->callerFrame();
        
        if (callFrame->hasHostCallFrameFlag())
            return returnValue;
        
        *topCallFrameSlot = callFrame;
        functionReturnValue = returnValue;
        codeBlock = callFrame->codeBlock();
        iBegin = codeBlock->instructions().begin();

        ASSERT(codeBlock == callFrame->codeBlock());
        
        // IFC4BC - Reset the callframe header space in reg to undefined
        // Prevents issue when labelling and some arbitrary value is present in the register
        for (int i = -1; i >= -6; i--)
            prevCallFrame->uncheckedR(i) = jsUndefined();
        
        // int numReg = codeBlock->m_numCalleeRegisters;
        // for (int i = numReg - 6; i < numReg; i++) {
        //   callFrame->uncheckedR(i) = jsUndefined();
        // }
        
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_call_put_result) {
        /* op_call_put_result result(r)
         
         Move call result from functionReturnValue to caller's
         expected return value register.
         */
        pcLabel = pcstack.Head();
        pcLabel.setStar(false);
        JSLabel retLabel = functionReturnValue.getValueLabel();
        
        if (functionReturnValue.getValueLabel().Val() != pcLabel/*.Join(codeBlock->contextLabel)*/.Val() && !labelReq)
        {
            labelReq = true;
            labelRegisters(callFrame, codeBlock, pcLabel/*.Join(codeBlock->contextLabel)*/);
        }
        if (labelReq && !isPolicy) {
            if (!noSensitiveUpgrade(callFrame->uncheckedR(vPC[1].u.operand).getRegLabel())) {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->uncheckedR(vPC[1].u.operand).getRegLabel().Val(), pcLabel.Val());
                retLabel.setStar(true);
            }
            else {
                retLabel.setStar(false);
            }
            callFrame->uncheckedR(vPC[1].u.operand) = functionReturnValue;
            callFrame->uncheckedR(vPC[1].u.operand).setRegLabel(retLabel);
        }
        else {
            callFrame->uncheckedR(vPC[1].u.operand) = functionReturnValue;            
        }
        
        vPC += OPCODE_LENGTH(op_call_put_result);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_ret_object_or_this) {
        /* ret result(r)
         
         Return register result as the return value of the current
         function call, writing it into the caller's expected return
         value register. In addition, unwind one call frame and
         restore the scope chain, code block instruction pointer and
         register base to those of the calling function.
         */
        int count = (int) (codeBlock->instructions().end() - iBegin);
        int current = (int) (vPC - iBegin);
        bool popNow = false;
        bool dontPop = false;
        
        // With multiple rets, IPD will be the last ret always. Checking for last ret.
        if (pcstack.Reg() == callFrame->registers())
        {
            if (((pcIPD == count - 2) || (pcIPD == count - 3)) && ((current == count - 2 || current == count - 3)))
            {
                popNow = true;
            }
        }
        else
        {
            dontPop = true;
        }
        if (popNow)
        {
            pcstack.Pop();
            pcLabel = pcstack.Head();
            pcIPD = pcstack.Loc();
            pcSLen = pcstack.Len();
            pcReg = pcstack.Reg();
            pcLabel.setStar(false);
            JSLabel::pcGlobalLabel = pcLabel.getPair();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
        }
        
        int result = vPC[1].u.operand;
        
        JSValue returnValue = callFrame->r(result).jsValue();
        returnValue.setValueLabel(callFrame->r(result).getRegLabel().Join(pcLabel/*.Join(codeBlock->contextLabel)*/));
        
        // IFC4BC
        CallFrame* prevCallFrame = callFrame;
        
        if (UNLIKELY(!returnValue.isObject())) {
            returnValue = callFrame->r(vPC[2].u.operand).jsValue();
            returnValue.setValueLabel(callFrame->r(vPC[2].u.operand).getRegLabel());
        }

        if (!popNow && !dontPop)
        {
            pcstack.Pop();
            pcLabel = pcstack.Head();
            pcIPD = pcstack.Loc();
            pcSLen = pcstack.Len();
            pcReg = pcstack.Reg();
            pcLabel.setStar(false);
            JSLabel::pcGlobalLabel = pcLabel.getPair();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
        }

        vPC = callFrame->returnVPC();
        callFrame = callFrame->callerFrame();
        
        if (callFrame->hasHostCallFrameFlag())
            return returnValue;
        
        *topCallFrameSlot = callFrame;
        functionReturnValue = returnValue;
        codeBlock = callFrame->codeBlock();
        ASSERT(codeBlock == callFrame->codeBlock());

        iBegin = codeBlock->instructions().begin();

        // IFC4BC - Reset the callframe header space in reg to undefined
        for (int i = -1; i >= -6; i--)
            prevCallFrame->uncheckedR(i) = jsUndefined();
        
        // int numReg = codeBlock->m_numCalleeRegisters;
        // for (int i = numReg - 6; i < numReg; i++) {
        //     callFrame->uncheckedR(i) = jsUndefined();
        // }
        
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_enter) {
        /* enter
         
         Initializes local variables to undefined. If the code block requires
         an activation, enter_with_activation is used instead.
         
         This opcode appears only at the beginning of a code block.
         */
        
        size_t i = 0;
        for (i = 0; i < (size_t)codeBlock->m_numCalleeRegisters; i++)
            callFrame->uncheckedR(i) = jsUndefined();
        
        // IFC4BC -- Adding labels to the value in the registers
        // Sparse Labelling - We can do without labelling, but keeping it until alternative is found for getting the labels
        if (!isPolicy)
            for (i = 0; i < (size_t)codeBlock->m_numCalleeRegisters; i++) {
                callFrame->uncheckedR(i).setRegLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            }
        // Setting the labels for the constant registers
        // This happens during move anyways, but might have vague labels
//        unsigned index = FirstConstantRegisterIndex;
//        for (i = 0; i < codeBlock->numberOfConstantRegisters(); i++) {
//            JSValue v = callFrame->r(index).jsValue();
//            if (v.isCell()) {
//                v.asCell()->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
//                v.asCell()->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
//            }
//            callFrame->r(index++).setRegLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
//        }
        // IFC4BC -------------------------------------------------------- */
        i = 0;
//        while (true) {
//            if (i == codeBlock->numberOfIdentifiers())
//                break;
//            Identifier& ident = codeBlock->identifier(i++);
//            printf("P:%s\n", ident.ustring().utf8().data());
//        }
        if (JSLabel::ABORT_FLAG) {
            JSLabel::ABORT_FLAG = false;
        }
        vPC += OPCODE_LENGTH(op_enter);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_create_activation) {
        /* create_activation dst(r)
         
         If the activation object for this callframe has not yet been created,
         this creates it and writes it back to dst.
         */
        int activationReg = vPC[1].u.operand;
        
        if (!callFrame->r(activationReg).jsValue()) {
            /* IFC4BC - Check the function's label with the current context.
             JSFunction* executingFunction = jsCast<JSFunction*>(callFrame->callee());
             if (labelReq)
             if(!noSensitiveUpgrade(executingFunction->getObjectLabel()))
             ABORT_TRANSACTION();
             // ------*/
            
            JSActivation* activation = JSActivation::create(*globalData, callFrame, static_cast<FunctionExecutable*>(codeBlock->ownerExecutable()));
            // IFC4BC - Let the label be set
            activation->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            activation->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            if (labelReq && !isPolicy) {
                JSLabel actLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
                if (!noSensitiveUpgrade(callFrame->r(activationReg).getRegLabel())) {
                    printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(activationReg).getRegLabel().Val(), pcLabel.Val());
                    actLabel.setStar(true);
                }
                else {
                    // actLabel.setStar(false);
                }
                callFrame->r(activationReg) = JSValue(activation);
                callFrame->r(activationReg).setRegLabel(actLabel);
            }
            else {
                callFrame->r(activationReg) = JSValue(activation);
            }
            // ------
            callFrame->setScopeChain(callFrame->scopeChain()->push(activation));
            callFrame->scopeChain()->scopeNextLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
        }
        vPC += OPCODE_LENGTH(op_create_activation);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_create_this) {
        /* op_create_this this(r) proto(r)
         
         Allocate an object as 'this', fr use in construction.
         
         This opcode should only be used at the beginning of a code
         block.
         */
        
        int thisRegister = vPC[1].u.operand;
        
        JSFunction* constructor = jsCast<JSFunction*>(callFrame->callee());
#if !ASSERT_DISABLED
        ConstructData constructData;
        ASSERT(constructor->methodTable()->getConstructData(constructor, constructData) == ConstructTypeJS);
#endif
        
        Structure* structure = constructor->cachedInheritorID(callFrame);
        // IFC4BC -----------------
        // setting the prototype chain (pointer) label to the context
        structure->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
        
        JSObject* newlyCreatedObject = constructEmptyObject(callFrame, structure);
        newlyCreatedObject->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/) ;
        newlyCreatedObject->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
        if (labelReq && !isPolicy) {
            JSLabel thisLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
            if (!noSensitiveUpgrade(callFrame->r(thisRegister).getRegLabel())) {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(thisRegister).getRegLabel().Val(), pcLabel.Val());
                thisLabel.setStar(true);
            }
            else {
                // thisLabel.setStar(false);
            }
            callFrame->uncheckedR(thisRegister) = JSValue(newlyCreatedObject);
            callFrame->uncheckedR(thisRegister).setRegLabel(thisLabel);
        }
        else {
            callFrame->uncheckedR(thisRegister) = JSValue(newlyCreatedObject);
        }
        // ----------------------------------------
        // Original
        // callFrame->uncheckedR(thisRegister) = constructEmptyObject(callFrame, structure);
        
        vPC += OPCODE_LENGTH(op_create_this);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_convert_this) {
        /* convert_this this(r)
         
         Takes the value in the 'this' register, converts it to a
         value that is suitable for use as the 'this' value, and
         stores it in the 'this' register. This opcode is emitted
         to avoid doing the conversion in the caller unnecessarily.
         
         This opcode should only be used at the beginning of a code
         block.
         */
        
        int thisRegister = vPC[1].u.operand;
        JSValue thisVal = callFrame->r(thisRegister).jsValue();
        
        if (thisVal.isPrimitive()){
            if (labelReq && !isPolicy) {
                JSLabel thisLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
                if(!noSensitiveUpgrade(callFrame->r(thisRegister).getRegLabel())) {
                    printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(thisRegister).getRegLabel().Val(), pcLabel.Val());
                    thisLabel.setStar(true);
                }
                else {
                    // thisLabel.setStar(false);
                }
                callFrame->uncheckedR(thisRegister) = JSValue(thisVal.toThisObject(callFrame));
                callFrame->uncheckedR(thisRegister).setRegLabel(thisLabel);
            }
            else {
                callFrame->uncheckedR(thisRegister) = JSValue(thisVal.toThisObject(callFrame));                
            }
        }
        // ------
        // Original
        // if (thisVal.isPrimitive())
        //     callFrame->uncheckedR(thisRegister) = JSValue(thisVal.toThisObject(callFrame));
        
        vPC += OPCODE_LENGTH(op_convert_this);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_init_lazy_reg) {
        /* init_lazy_reg dst(r)
         
         Initialises dst(r) to JSValue().
         
         This opcode appears only at the beginning of a code block.
         */
        int dst = vPC[1].u.operand;
        
        // IFC4BC - Set the label to the pcstack head as this is at the beginning of the code block.
        callFrame->uncheckedR(dst) = JSValue();
        if (labelReq && !isPolicy)
            callFrame->uncheckedR(dst).setRegLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
        // ------
        vPC += OPCODE_LENGTH(op_init_lazy_reg);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_create_arguments) {
        /* create_arguments dst(r)
         
         Creates the 'arguments' object and places it in both the
         'arguments' call frame slot and the local 'arguments'
         register, if it has not already been initialised.
         */
        
        int dst = vPC[1].u.operand;
        
        // IFC4BC
        if (!callFrame->r(dst).jsValue()) {
            Arguments* arguments = Arguments::create(*globalData, callFrame);
            // IFC4BC - Assigning label to arguments object
            arguments->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            arguments->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/);
            if (labelReq && !isPolicy) {
                JSLabel argLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
                JSLabel argULabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
                if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())) {
                    printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                    argLabel.setStar(true);
                }
                else {
                    // argLabel.setStar(false);
                }
                if (!noSensitiveUpgrade(callFrame->r(unmodifiedArgumentsRegister(dst)).getRegLabel())) {
                    printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                    argULabel.setStar(true);
                }
                else {
                    // argULabel.setStar(false);
                }
                callFrame->uncheckedR(dst) = JSValue(arguments);
                callFrame->uncheckedR(unmodifiedArgumentsRegister(dst)) = JSValue(arguments);
                callFrame->r(dst).setRegLabel(argLabel);
                callFrame->r(unmodifiedArgumentsRegister(dst)).setRegLabel(argULabel);
            }
            else {
                callFrame->uncheckedR(dst) = JSValue(arguments);
                callFrame->uncheckedR(unmodifiedArgumentsRegister(dst)) = JSValue(arguments);                
            }
            // --------------------------------------------
        }
        /* Original
         if (!callFrame->r(dst).jsValue()) {
         Arguments* arguments = Arguments::create(*globalData, callFrame);
         callFrame->uncheckedR(dst) = JSValue(arguments);
         callFrame->uncheckedR(unmodifiedArgumentsRegister(dst)) = JSValue(arguments);
         }*/
        vPC += OPCODE_LENGTH(op_create_arguments);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_construct) {
        /* construct func(r) argCount(n) registerOffset(n) proto(r) thisRegister(r)
         
         Invoke register "func" as a constructor. For JS
         functions, the calling convention is exactly as for the
         "call" opcode, except that the "this" value is a newly
         created Object. For native constructors, no "this"
         value is passed. In either case, the argCount and registerOffset
         registers are interpreted as for the "call" opcode.
         
         Register proto must contain the prototype property of
         register func. This is to enable polymorphic inline
         caching of this lookup.
         */
        
        int func = vPC[1].u.operand;
        int argCount = vPC[2].u.operand;
        int registerOffset = vPC[3].u.operand;
        
        JSValue v = callFrame->r(func).jsValue();
        
        ConstructData constructData;
        ConstructType constructType = getConstructData(v, constructData);
        
        
        if (constructType == ConstructTypeJS) {
            ScopeChainNode* callDataScopeChain = constructData.js.scopeChain;
            
            JSObject* error = constructData.js.functionExecutable->compileForConstruct(callFrame, callDataScopeChain);
            if (UNLIKELY(!!error)) {
                exceptionValue = error;
                goto vm_throw;
            }
            
            CallFrame* previousCallFrame = callFrame;
            CodeBlock* newCodeBlock = &constructData.js.functionExecutable->generatedBytecodeForConstruct();
            
            // If it is a different function call, then we would need the label to be propagated.
            // IFC4BC - Checking if handler exists
            int num = 0;
            const size_t numHandlers = codeBlock->numberOfExceptionHandlers();
            HandlerInfo* hInfo;
            bool existsHandler = false;
            int pos = vPC - iBegin;
            // Get number of instructions
            while ((unsigned)num < numHandlers) {
                hInfo = &codeBlock->exceptionHandler(num++);
                if ((hInfo->start <= (unsigned)pos) && (hInfo->end > (unsigned)pos)) {
                    existsHandler = true;
                    break;
                }
            }
            
            JSLabel funcLabel = asObject(v)->getObjectLabel();
            // newCodeBlock->contextLabel = JSLabel(URLMap::urlmap().getLabel(constructData.js.functionExecutable->sourceURL().utf8().data()));

//            if (funcLabel.Val() == 0) {
//                // IFC4BC - Getting the label for functions defined globally
//                //const char* sURl = 
//                //char *temp1 = strstr(sURl, ".policy");
//                
//                //if(temp1) funcLabel = JSLabel(URLMap::urlmap().getLabel(sURl, 1));
//                funcLabel = JSLabel(URLMap::urlmap().getLabel(constructData.js.functionExecutable->sourceURL().utf8().data()));
//                asObject(v)->setObjectLabel(funcLabel);
//                asObject(v)->structure()->setProtoLabel(funcLabel);
//            }
            
            //newCodeBlock->contextLabel = funcLabel;
            /*
            if (funcLabel.iVal() == 0xffffffffffffffff)
            {
                funcLabel = JSLabel(URLMap::urlmap().getLabel(constructData.js.functionExecutable->sourceURL().utf8().data()));
                newCodeBlock->contextLabel = funcLabel;
                funcLabel.setVal(0);
                asObject(v)->setObjectLabel(funcLabel);
                asObject(v)->structure()->setProtoLabel(funcLabel);
                // newCodeBlock->contextLabel = funcLabel;
            }*/
            
            // if ((pcLabel != funcLabel || !(JSLabelMap::labelMap().isOrdered(pcLabel.Val(), funcLabel.Val()))) && !labelReq)
            if ((pcLabel != funcLabel) && !labelReq)
            {
                labelReq = true;
                labelRegisters(callFrame, codeBlock, pcLabel);
            }
            if (labelReq && !isPolicy) {
                if (funcLabel.Star())
                {
                    printf("Function object contains a star in call\n");
                }
                funcLabel = funcLabel.Join(callFrame->r(func).getRegLabel());
                OP_CALLBRANCH(funcLabel, (existsHandler || pcstack.excHandler()), existsHandler);
            }
            else {
                OP_CALLBRANCH(pcstack.Head(), (existsHandler || pcstack.excHandler()), existsHandler);
            }
            
            pcLabel = pcstack.Head();
            pcLabel.setStar(false);
            JSLabel::pcGlobalLabel = pcLabel.getPair();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
            // printf("Function call construct with label %lld\n", pcLabel.Val());
            // printf("Function construct %p from %p at %ld with label %lld\n", newCodeBlock,
                   // codeBlock, vPC - iBegin, pcLabel.Val());

            // OP_CALLBRANCH(pcstack.Head(), (existsHandler || pcstack.excHandler()), existsHandler);
            
            // For cases when the construct itself has two possible paths
            /*
            if ((int(vPC - iBegin) + OPCODE_LENGTH(op_construct)) != pcIPD ||
                pcstack.Reg() != callFrame->registers())
            {
                pcstack.Join(pcstack.Head(), true);
            }
            */
            if (pcstack.excHandler()) {
                // SEN exists
                if (!newCodeBlock->has_SENanalysis) {
                    newCodeBlock->analyzerSEN.genContextTable(newCodeBlock, this, pcstack.excHandler());
                    newCodeBlock->has_SENanalysis = true;
                }
                newCodeBlock->analyzer = newCodeBlock->analyzerSEN;
            }
            else {
                // No exception handler
                if (!newCodeBlock->has_analysis) {
                    newCodeBlock->analyzerNOR.genContextTable(newCodeBlock, this, pcstack.excHandler());
                    newCodeBlock->has_analysis = true;
                }
                newCodeBlock->analyzer = newCodeBlock->analyzerNOR;
            }
            // -------------------------
            
            callFrame = slideRegisterWindowForCall(newCodeBlock, registerFile, callFrame, registerOffset, argCount);
            if (UNLIKELY(!callFrame)) {
                callFrame = previousCallFrame;
                exceptionValue = createStackOverflowError(callFrame);
                goto vm_throw;
            }
            callFrame->init(newCodeBlock, vPC + OPCODE_LENGTH(op_construct), callDataScopeChain, previousCallFrame, argCount, jsCast<JSFunction*>(v));
            
            // IFC4BC - Labelling the arguments with the context
            // Check if there is argument passing.
            // -7 is the first register where the argument resides. 6 is the callframe header size.
            /*
            if (labelReq) {
                for(int i = -7, j = 1; j <= newCodeBlock->numParameters(); j++, i--)
                    if (j <= argCount)
                        callFrame->uncheckedR(i).setRegLabel(callFrame->r(i).getRegLabel().Join(pcLabel));
            }
             */
            //------
            
            codeBlock = newCodeBlock;
            *topCallFrameSlot = callFrame;
            vPC = newCodeBlock->instructions().begin();
            iBegin = newCodeBlock->instructions().begin();

#if ENABLE(OPCODE_STATS)
            OpcodeStats::resetLastInstruction();
#endif
            
             NEXT_INSTRUCTION();
        }
        
        if (constructType == ConstructTypeHost) {
            JSLabel::pcGlobalLabel = pcLabel.getPair();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
            ScopeChainNode* scopeChain = callFrame->scopeChain();
            CallFrame* newCallFrame = CallFrame::create(callFrame->registers() + registerOffset);
            newCallFrame->init(0, vPC + OPCODE_LENGTH(op_construct), scopeChain, callFrame, argCount, asObject(v));
            
            JSValue returnValue;
            JSLabel argumentsLabel = JSLabel();
            if (labelReq && !isPolicy) {
                // IFC4BC - Passing the argument labels
                for (int i = 0, j = -7; i < argCount; i++, j--) {
                    if (i == 100) {
                        printf("More than 100 arguments to native function construct\n");
                        // ABORT_CALL();
                        break;
                    }
                    
                    if (i != 0)
                    {
                        JSLabel::argLabel[i] = newCallFrame->r(j).getRegLabel().Join(pcLabel).getPair();
                    }
                    else
                    {
                        JSLabel::argLabel[i] = newCallFrame->r(j).getRegLabel().getPair();
                    }
                     
                    argumentsLabel = argumentsLabel.Join(newCallFrame->r(j).getRegLabel());
                }
            }
            {
                *topCallFrameSlot = newCallFrame;
                SamplingTool::HostCallRecord callRecord(m_sampler.get());
                returnValue = (constructData.native.function(newCallFrame));
                *topCallFrameSlot = callFrame;
            }
            if (!isPolicy)
                for (int i = -1; i >= -6; i--)
                    newCallFrame->uncheckedR(i).setRegLabel(pcLabel);
            
            if (JSLabel::ABORT_FLAG) {
                JSLabel::ABORT_FLAG = false;
                ABORT_TRANSACTION();
            }
            
            // Join the return value with the pc in which it was performed
            returnValue.setValueLabel(returnValue.joinValueLabel(pcLabel/*.Join(codeBlock->contextLabel)*/.Join(argumentsLabel)));
            returnValue.setValueLabel(returnValue.joinValueLabel(JSLabel::returnLabel));
            JSLabel::returnLabel = JSLabel().getPair();
            if (returnValue.getValueLabel().Val() != pcLabel.Val() && !labelReq)
            {
                labelReq = true;
                labelRegisters(callFrame, codeBlock, pcLabel);
            }
            // Reset the argLabel to 0.
            
            for (int i = 0; i < argCount; i++) {
                JSLabel::argLabel[i] = JSLabel().getPair();
            }
            
            JSLabel::pcGlobalLabel = pcLabel.getPair();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
            
            CHECK_FOR_EXCEPTION(returnValue.getValueLabel());
            functionReturnValue = returnValue;
            
            vPC += OPCODE_LENGTH(op_construct);
             NEXT_INSTRUCTION();
        }
        
        ASSERT(constructType == ConstructTypeNone);
        
        exceptionValue = createNotAConstructorError(callFrame, v);
        goto vm_throw;
    }
    DEFINE_OPCODE(op_strcat) {
        /* strcat dst(r) src(r) count(n)
         
         Construct a new String instance using the original
         constructor, and puts the result in register dst.
         The string will be the result of concatenating count
         strings with values taken from registers starting at
         register src.
         */
        int dst = vPC[1].u.operand;
        int src = vPC[2].u.operand;
        int count = vPC[3].u.operand;
        
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel;
            int i = src;
            int total = src + count;
            while (i < total){
                dstLabel = dstLabel.Join(callFrame->r(i++).getRegLabel());
            }
            // IFC4BC -- DNSU check
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = concatenateStrings(callFrame, &callFrame->registers()[src], count);
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
            CHECK_FOR_EXCEPTION(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = concatenateStrings(callFrame, &callFrame->registers()[src], count);
            CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/);
        }
        vPC += OPCODE_LENGTH(op_strcat);
        
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_to_primitive) {
        int dst = vPC[1].u.operand;
        int src = vPC[2].u.operand;
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(src).getRegLabel());
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel())){
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            callFrame->uncheckedR(dst) = callFrame->r(src).jsValue().toPrimitive(callFrame);
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
        }
        else {
            callFrame->uncheckedR(dst) = callFrame->r(src).jsValue().toPrimitive(callFrame);            
        }
        vPC += OPCODE_LENGTH(op_to_primitive);
        
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_push_scope) {
        /* push_scope scope(r)
         
         Converts register scope to object, and pushes it onto the top
         of the current scope chain.  The contents of the register scope
         are replaced by the result of toObject conversion of the scope.
         */
        int scope = vPC[1].u.operand;
        JSValue v = callFrame->r(scope).jsValue();
        JSObject* o = v.toObject(callFrame);
        
        o->setObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(scope).getRegLabel()));
        o->structure()->setProtoLabel(pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(scope).getRegLabel()));
        
        CHECK_FOR_EXCEPTION(pcLabel/*.Join(codeBlock->contextLabel)*/.Join(callFrame->r(scope).getRegLabel()));
        
        callFrame->uncheckedR(scope) = JSValue(o);
        
        JSLabel scopeLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
        if (callFrame->scopeChain()->scopeNextLabel.Star()) {
            scopeLabel.setStar(true);
        }
        if (!pcLabel.NSU(callFrame->scopeChain()->scopeNextLabel)) {
            printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->scopeChain()->scopeNextLabel.Val(), pcLabel.Val());
            scopeLabel.setStar(true);
        }
        else {
            // scopeLabel.setStar(false);
        }
        callFrame->setScopeChain(callFrame->scopeChain()->push(o));
        //IFC4BC
        callFrame->scopeChain()->scopeNextLabel = scopeLabel;
        //------
        
        vPC += OPCODE_LENGTH(op_push_scope);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_pop_scope) {
        /* pop_scope
         
         Removes the top item from the current scope chain.
         */
        // IFC4BC - Do we need to check the object's label also
        if (callFrame->scopeChain()->scopeNextLabel.Star() &&
            !pcLabel.NSU(callFrame->scopeChain()->scopeNextLabel))
            ABORT_TRANSACTION();
        //------
        callFrame->setScopeChain(callFrame->scopeChain()->pop());
        
        vPC += OPCODE_LENGTH(op_pop_scope);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_get_pnames) {
        /* get_pnames dst(r) base(r) i(n) size(n) breakTarget(offset)
         
         Creates a property name list for register base and puts it
         in register dst, initializing i and size for iteration. If
         base is undefined or null, jumps to breakTarget.
         */
        int dst = vPC[1].u.operand;
        int base = vPC[2].u.operand;
        int i = vPC[3].u.operand;
        int size = vPC[4].u.operand;
        int breakTarget = vPC[5].u.operand;
        
        JSValue v = callFrame->r(base).jsValue();
        if (v.isUndefinedOrNull()) {
            vPC += breakTarget;
             NEXT_INSTRUCTION();
        }
        
        JSObject* o = v.toObject(callFrame);
        Structure* structure = o->structure();
        JSPropertyNameIterator* jsPropertyNameIterator = structure->enumerationCache();
        if (!jsPropertyNameIterator || jsPropertyNameIterator->cachedPrototypeChain() != structure->prototypeChain(callFrame))
            jsPropertyNameIterator = JSPropertyNameIterator::create(callFrame, o);
        
        // Iterate through all the properties and set the context label to join of all
        // Doing it in next_pname for now.
        // OP_BRANCH(pcLabel);
        if (labelReq && !isPolicy) {
            JSLabel dstLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
            JSLabel iLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
            JSLabel sLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
            if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
            {

                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                dstLabel.setStar(true);
            }
            
            if (!noSensitiveUpgrade(callFrame->r(i).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(i).getRegLabel().Val(), pcLabel.Val());
                iLabel.setStar(true);
            }
            else {
                // iLabel.setStar(false);
            }
            if (!noSensitiveUpgrade(callFrame->r(size).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(size).getRegLabel().Val(), pcLabel.Val());
                sLabel.setStar(true);
            }
            else {
                // sLabel.setStar(false);
            }
            callFrame->uncheckedR(dst) = jsPropertyNameIterator;
            callFrame->uncheckedR(base) = JSValue(o);
            callFrame->uncheckedR(i) = Register::withInt(0);
            callFrame->uncheckedR(size) = Register::withInt(jsPropertyNameIterator->size());
            callFrame->uncheckedR(dst).setRegLabel(dstLabel);
            callFrame->uncheckedR(i).setRegLabel(iLabel);
            callFrame->uncheckedR(size).setRegLabel(sLabel);
        }
        else {
            callFrame->uncheckedR(dst) = jsPropertyNameIterator;
            callFrame->uncheckedR(base) = JSValue(o);
            callFrame->uncheckedR(i) = Register::withInt(0);
            callFrame->uncheckedR(size) = Register::withInt(jsPropertyNameIterator->size());
        }
        vPC += OPCODE_LENGTH(op_get_pnames);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_next_pname) {
        /* next_pname dst(r) base(r) i(n) size(n) iter(r) target(offset)
         
         Copies the next name from the property name list in
         register iter to dst, then jumps to offset target. If there are no
         names left, invalidates the iterator and continues to the next
         instruction.
         */
        int dst = vPC[1].u.operand;
        int base = vPC[2].u.operand;
        int i = vPC[3].u.operand;
        int size = vPC[4].u.operand;
        int iter = vPC[5].u.operand;
        int target = vPC[6].u.operand;
        
        JSPropertyNameIterator* it = callFrame->r(iter).propertyNameIterator();
        // IFC4BC-----
        JSLabel context = pcLabel/*.Join(codeBlock->contextLabel)*/;
        OP_BRANCH(context);
        
        while (callFrame->r(i).i() != callFrame->r(size).i()) {
            // TODO - Might need getIFC here.
            JSValue key = it->get(callFrame, asObject(callFrame->r(base).jsValue()), callFrame->r(i).i());
            context = key.joinValueLabel(context);
            context.setStar(false);
            CHECK_FOR_EXCEPTION(context);
            pcstack.Join(context, true); // Add the label to the context. Ideally, to be done in get_pnames
            pcLabel = pcstack.Head();
            pcLabel.setStar(false);
            JSLabel::pcGlobalLabel = pcLabel.getPair();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
            if (labelReq && !isPolicy) {
                JSLabel iLabel = context;
                if (!noSensitiveUpgrade(callFrame->r(i).getRegLabel()))
                {
                    printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(i).getRegLabel().Val(), pcLabel.Val());
                    iLabel.setStar(true);
                }
                else {
                    // iLabel.setStar(false);
                }
                callFrame->uncheckedR(i) = Register::withInt(callFrame->r(i).i() + 1);
                callFrame->uncheckedR(i).setRegLabel(iLabel);
            }
            else {
                callFrame->uncheckedR(i) = Register::withInt(callFrame->r(i).i() + 1);                
            }
            if (key) {
                CHECK_FOR_TIMEOUT();
                key.setValueLabel(JSLabel());
                // Check for labelreq here, if context changes
                pcstack.Join(context, true); // Add the label to the context. Ideally, to be done in get_pnames
                pcLabel = pcstack.Head();
                pcLabel.setStar(false);
                JSLabel::pcGlobalLabel = pcLabel.getPair();
                JSLabel::BRANCH_FLAG = pcstack.branchFlag();
                if (labelReq && !isPolicy) {
                    JSLabel dstLabel = context;
                    if (!noSensitiveUpgrade(callFrame->r(dst).getRegLabel()))
                    {
                        printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->r(dst).getRegLabel().Val(), pcLabel.Val());
                        dstLabel.setStar(true);
                    }
                    else {
                        // dstLabel.setStar(false);
                    }
                    callFrame->uncheckedR(dst) = key;
                    callFrame->uncheckedR(dst).setRegLabel(dstLabel);
                }
                else {
                    callFrame->uncheckedR(dst) = key;
                }
                vPC += target;
                 NEXT_INSTRUCTION();
            }
        }
        
        vPC += OPCODE_LENGTH(op_next_pname);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_jmp_scopes) {
        /* jmp_scopes count(n) target(offset)
         
         Removes the a number of items from the current scope chain
         specified by immediate number count, then jumps to offset
         target.
         */
        int count = vPC[1].u.operand;
        int target = vPC[2].u.operand;
        
        ScopeChainNode* tmp = callFrame->scopeChain();
        while (count--) {
            if (callFrame->scopeChain()->scopeNextLabel.Star() &&
                !pcLabel.NSU(callFrame->scopeChain()->scopeNextLabel))
                ABORT_TRANSACTION();
            tmp = tmp->pop();
        }
        callFrame->setScopeChain(tmp);
        
        vPC += target;
         NEXT_INSTRUCTION();
    }
#if ENABLE(COMPUTED_GOTO_CLASSIC_INTERPRETER)
    // Appease GCC
    goto *(&&skip_new_scope);
#endif
    DEFINE_OPCODE(op_push_new_scope) {
        /* new_scope dst(r) property(id) value(r)
         
         Constructs a new StaticScopeObject with property set to value.  That scope
         object is then pushed onto the ScopeChain.  The scope object is then stored
         in dst for GC.
         */
        // TODO - Change createExceptionScope to handle the labels and NSU
        JSLabel scopeLabel = pcLabel/*.Join(codeBlock->contextLabel)*/;
        if (callFrame->scopeChain()->scopeNextLabel.Star()) {
            scopeLabel.setStar(true);
        }
        if (!pcLabel.NSU(callFrame->scopeChain()->scopeNextLabel)) {
            printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->scopeChain()->scopeNextLabel.Val(), pcLabel.Val());
            scopeLabel.setStar(true);
        }
        else {
            // scopeLabel.setStar(false);
        }
        
        callFrame->setScopeChain(createExceptionScope(callFrame, vPC));
        //IFC4BC
        callFrame->scopeChain()->scopeNextLabel = scopeLabel;
        //------
        
        vPC += OPCODE_LENGTH(op_push_new_scope);
         NEXT_INSTRUCTION();
    }
#if ENABLE(COMPUTED_GOTO_CLASSIC_INTERPRETER)
skip_new_scope:
#endif
    DEFINE_OPCODE(op_catch) {
        /* catch ex(r)
         
         Retrieves the VM's current exception and puts it in register
         ex. This is only valid after an exception has been raised,
         and usually forms the beginning of an exception handler.
         */
        ASSERT(exceptionValue);
        ASSERT(!globalData->exception);
        int ex = vPC[1].u.operand;
        // IFC4BC - NSU check for writing the exc value to the reg
        if (labelReq && !isPolicy) {
            JSLabel exLabel = pcLabel/*.Join(codeBlock->contextLabel)*/.Join(exceptionValue.getValueLabel());
            if (!noSensitiveUpgrade(callFrame->uncheckedR(ex).getRegLabel()))
            {
                printf("Sensitive Upgrade at %ld in %p from label %lld to %lld\n", vPC - iBegin, codeBlock, callFrame->uncheckedR(ex).getRegLabel().Val(), pcLabel.Val());
                exLabel.setStar(true);
            }
            else {
                // exLabel.setStar(false);
            }
            callFrame->uncheckedR(ex) = exceptionValue;
            callFrame->uncheckedR(ex).setRegLabel(exLabel);
        }
        else {
            callFrame->uncheckedR(ex) = exceptionValue;            
        }
        // ------
        exceptionValue = JSValue();
        
        vPC += OPCODE_LENGTH(op_catch);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_throw) {
        /* throw ex(r)
         
         Throws register ex as an exception. This involves three
         steps: first, it is set as the current exception in the
         VM's internal state, then the stack is unwound until an
         exception handler or a native code boundary is found, and
         then control resumes at the exception handler if any or
         else the script returns control to the nearest native caller.
         */
        
        int ex = vPC[1].u.operand;
        exceptionValue = callFrame->r(ex).jsValue();
        
        handler = throwException(callFrame, exceptionValue, vPC - iBegin);
        if (!handler){
            // Abhi -- removing all entries from programcounter as an unhandled exception has occurred.
            while (pcSLen > 0) {
                pcstack.Pop();
                pcIPD = pcstack.Loc();
                pcSLen = pcstack.Len();
                pcReg = pcstack.Reg();
                pcLabel = pcstack.Head();
                pcLabel.setStar(false);
                JSLabel::pcGlobalLabel = pcLabel.getPair();
                JSLabel::BRANCH_FLAG = pcstack.branchFlag();
            }
            return throwError(callFrame, exceptionValue);
        }
        
        codeBlock = callFrame->codeBlock();
        iBegin = codeBlock->instructions().begin();
        vPC = iBegin + handler->target;
        
        /* Abhi -- For exception handling 
         // Popping the programcounter to the correct callframe
         while ((pcstack.Reg() != callFrame->registers()) && pcSLen > 0){
         pcstack.Pop();
         }
         while (pcSLen > 0 && (pcstack.Reg()==callFrame->registers()) && (pcIPD < (int)handler->target)){
         pcstack.Pop();
         }
         */
        if (pcSLen > 0){
            pcstack.Join(exceptionValue.getValueLabel());
            pcLabel = pcstack.Head();
            pcLabel.setStar(false);
            JSLabel::pcGlobalLabel = pcLabel.getPair();
            JSLabel::BRANCH_FLAG = pcstack.branchFlag();
        }
        // Check this! This might not be right.
        else { // Do not remove the curly braces
            OP_BRANCH(exceptionValue.getValueLabel());
        }
        pcLabel = pcstack.Head();
        pcIPD = pcstack.Loc();
        pcSLen = pcstack.Len();
        pcReg = pcstack.Reg();
        pcLabel.setStar(false);
        JSLabel::pcGlobalLabel = pcLabel.getPair();
        JSLabel::BRANCH_FLAG = pcstack.branchFlag();
        // IFC4BC ------------------------------------------------
        
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_throw_reference_error) {
        /* op_throw_reference_error message(k)
         
         Constructs a new reference Error instance using the
         original constructor, using constant message as the
         message string. The result is thrown.
         */
        UString message = callFrame->r(vPC[1].u.operand).jsValue().toString(callFrame)->value(callFrame);
        exceptionValue = JSValue(createReferenceError(callFrame, message));
        goto vm_throw;
    }
    DEFINE_OPCODE(op_end) {
        /* end result(r)
         
         Return register result as the value of a global or eval
         program. Return control to the calling native code.
         */
        
        int result = vPC[1].u.operand;
        JSValue res = callFrame->r(result).jsValue();
        res.setValueLabel(callFrame->r(result).getRegLabel());
        JSLabel::pcGlobalLabel = JSLabel().getPair(); // Reset the pcGlobalLabel
        JSLabel::BRANCH_FLAG = false;
        return res;
    }
    DEFINE_OPCODE(op_put_getter_setter) {
        /* put_getter_setter base(r) property(id) getter(r) setter(r)
         
         Puts accessor descriptor to register base as the named
         identifier property. Base and function may be objects
         or undefined, this op should only be used for accessors
         defined in object literal form.
         
         Unlike many opcodes, this one does not write any output to
         the register file.
         */
        int base = vPC[1].u.operand;
        int property = vPC[2].u.operand;
        int getterReg = vPC[3].u.operand;
        int setterReg = vPC[4].u.operand;
        
        ASSERT(callFrame->r(base).jsValue().isObject());
        JSObject* baseObj = asObject(callFrame->r(base).jsValue());
        Identifier& ident = codeBlock->identifier(property);
        
        GetterSetter* accessor = GetterSetter::create(callFrame);
        
        JSValue getter = callFrame->r(getterReg).jsValue();
        JSValue setter = callFrame->r(setterReg).jsValue();
        ASSERT(getter.isObject() || getter.isUndefined());
        ASSERT(setter.isObject() || setter.isUndefined());
        ASSERT(getter.isObject() || setter.isObject());
        
        if (!getter.isUndefined())
            accessor->setGetter(callFrame->globalData(), asObject(getter));
        if (!setter.isUndefined())
            accessor->setSetter(callFrame->globalData(), asObject(setter));
        // IFC4BC
        if (!pcLabel.NSU(baseObj->getObjectLabel()))
            ABORT_TRANSACTION();
        baseObj->putDirectAccessor(callFrame->globalData(), ident, accessor, Accessor);
        baseObj->setObjectLabel(baseObj->joinObjectLabel(pcLabel/*.Join(codeBlock->contextLabel)*/));
        // ------
        // Original
        // baseObj->putDirectAccessor(callFrame->globalData(), ident, accessor, Accessor);
        
        vPC += OPCODE_LENGTH(op_put_getter_setter);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_method_check) {
        vPC++;
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_debug) {
        /* debug debugHookID(n) firstLine(n) lastLine(n)
         
         Notifies the debugger of the current state of execution. This opcode
         is only generated while the debugger is attached.
         */
        int debugHookID = vPC[1].u.operand;
        int firstLine = vPC[2].u.operand;
        int lastLine = vPC[3].u.operand;
        
        debug(callFrame, static_cast<DebugHookID>(debugHookID), firstLine, lastLine);
        
        vPC += OPCODE_LENGTH(op_debug);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_profile_will_call) {
        /* op_profile_will_call function(r)
         
         Notifies the profiler of the beginning of a function call. This opcode
         is only generated if developer tools are enabled.
         */
        int function = vPC[1].u.operand;
        
        if (Profiler* profiler = globalData->enabledProfiler())
            profiler->willExecute(callFrame, callFrame->r(function).jsValue());
        
        vPC += OPCODE_LENGTH(op_profile_will_call);
         NEXT_INSTRUCTION();
    }
    DEFINE_OPCODE(op_profile_did_call) {
        /* op_profile_did_call function(r)
         
         Notifies the profiler of the end of a function call. This opcode
         is only generated if developer tools are enabled.
         */
        int function = vPC[1].u.operand;
        
        if (Profiler* profiler = globalData->enabledProfiler())
            profiler->didExecute(callFrame, callFrame->r(function).jsValue());
        
        vPC += OPCODE_LENGTH(op_profile_did_call);
         NEXT_INSTRUCTION();
    }
vm_throw: {
    globalData->exception = JSValue();
    // IFC4BC
    // int bytecodeOffset = (int) (vPC - iBegin);
    // int lineNumber = codeBlock->lineNumberForBytecodeOffset(bytecodeOffset);
    // printf("Line %d: Error at %d in %p!\n", lineNumber, bytecodeOffset, codeBlock);
    JSValue excVal = exceptionValue;
    if (!tickCount) {
        // The exceptionValue is a lie! (GCC produces bad code for reasons I
        // cannot fathom if we don't assign to the exceptionValue before branching)
        exceptionValue = createInterruptedExecutionException(globalData);
    }
    // IFC4BC - If exceptionValue gets changed above, reset the label to excVal's
    exceptionValue.setValueLabel(excVal.getValueLabel());
    JSGlobalObject* globalObject = callFrame->lexicalGlobalObject();
    handler = throwException(callFrame, exceptionValue, vPC - iBegin);
    if (!handler) {
        // Abhi -- removing all entries from programcounter as an unhandled exception has occurred.
            while (pcSLen > 0) {
                pcstack.Pop();
                pcIPD = pcstack.Loc();
                pcSLen = pcstack.Len();
                pcReg = pcstack.Reg();
                pcLabel = pcstack.Head();
                pcLabel.setStar(false);
                JSLabel::pcGlobalLabel = pcLabel.getPair();
                JSLabel::BRANCH_FLAG = pcstack.branchFlag();
#if LDEBUG
                printf("Popping as no handler found\n");
#endif
            }
        // It is okay if we lose the label now. The return would finish execution with error.
            // Abhi ------------------------------------------------------------
        // Can't use the callframe at this point as the scopechain, etc have
        // been released.
        return throwError(globalObject->globalExec(), exceptionValue);
    }
    
    codeBlock = callFrame->codeBlock();
    iBegin = codeBlock->instructions().begin();
    vPC = iBegin + handler->target;
    
    /* IFC4BC -- Exception handling for pcstack
         // SEN is not pushed and it should be proper pushing
     // Abhi -- Pop labels until we reach the correct call frame
        while (pcstack.Reg() != callFrame->registers() && pcSLen > 0){
     pcstack.Pop();
     // Check if there is something in pc stack to pop
     // Check if there are other loops in the pc stack which might not get executed because of the exception
     // Joining labels mean they have same idom, which would be reached as soon as the exception is handled
     // ^this does not pose any problems as popping it means we have reached the common idom...
        while (pcSLen > 0 && (pcIPD < (int)(handler->target)) && (pcstack.Reg() == callFrame->registers())){
     pcstack.Pop();
     */
    // Abhi -- Joining the label with the current stack label or push it
    if (pcSLen > 0) {
        pcstack.Join(exceptionValue.getValueLabel());
        pcLabel = pcstack.Head();
        pcLabel.setStar(false);
        JSLabel::pcGlobalLabel = pcLabel.getPair();
        JSLabel::BRANCH_FLAG = pcstack.branchFlag();
    }
    else {  // Please do not remove the curly brackets.
        // This case if for sanity check. Must not occur!!!
        OP_BRANCH(exceptionValue.getValueLabel());   // Using OP_BRANCH for pushing the label
    }
    pcLabel = pcstack.Head();
    pcIPD = pcstack.Loc();
    pcSLen = pcstack.Len();
    pcReg = pcstack.Reg();
    pcLabel.setStar(false);
    JSLabel::pcGlobalLabel = pcLabel.getPair();
    JSLabel::BRANCH_FLAG = pcstack.branchFlag();
    // IFC4BC ------------------------------------------------------------
     NEXT_INSTRUCTION();
}
}
#if !ENABLE(COMPUTED_GOTO_CLASSIC_INTERPRETER)
} // iterator loop ends
#endif
    #undef NEXT_INSTRUCTION
    #undef DEFINE_OPCODE
    #undef CHECK_FOR_EXCEPTION
    #undef CHECK_FOR_TIMEOUT
#endif // ENABLE(CLASSIC_INTERPRETER)
}

JSValue Interpreter::retrieveArgumentsFromVMCode(CallFrame* callFrame, JSFunction* function) const
{
    CallFrame* functionCallFrame = findFunctionCallFrameFromVMCode(callFrame, function);
    if (!functionCallFrame)
        return jsNull();

    CodeBlock* codeBlock = functionCallFrame->someCodeBlockForPossiblyInlinedCode();
    if (codeBlock->usesArguments()) {
        ASSERT(codeBlock->codeType() == FunctionCode);
        int argumentsRegister = codeBlock->argumentsRegister();
        int realArgumentsRegister = unmodifiedArgumentsRegister(argumentsRegister);
        if (JSValue arguments = functionCallFrame->uncheckedR(argumentsRegister).jsValue())
            return arguments;
        JSValue arguments = JSValue(Arguments::create(callFrame->globalData(), functionCallFrame));
        functionCallFrame->r(argumentsRegister) = arguments;
        functionCallFrame->r(realArgumentsRegister) = arguments;
        return arguments;
    }

    Arguments* arguments = Arguments::create(functionCallFrame->globalData(), functionCallFrame);
    arguments->tearOff(functionCallFrame);
    return JSValue(arguments);
}

JSValue Interpreter::retrieveCallerFromVMCode(CallFrame* callFrame, JSFunction* function) const
{
    CallFrame* functionCallFrame = findFunctionCallFrameFromVMCode(callFrame, function);

    if (!functionCallFrame)
        return jsNull();
    
    int lineNumber;
    CallFrame* callerFrame = getCallerInfo(&callFrame->globalData(), functionCallFrame, lineNumber);
    if (!callerFrame)
        return jsNull();
    JSValue caller = callerFrame->callee();
    if (!caller)
        return jsNull();

    // Skip over function bindings.
    ASSERT(caller.isObject());
    while (asObject(caller)->inherits(&JSBoundFunction::s_info)) {
        callerFrame = getCallerInfo(&callFrame->globalData(), callerFrame, lineNumber);
        if (!callerFrame)
            return jsNull();
        caller = callerFrame->callee();
        if (!caller)
            return jsNull();
    }

    return caller;
}

void Interpreter::retrieveLastCaller(CallFrame* callFrame, int& lineNumber, intptr_t& sourceID, UString& sourceURL, JSValue& function) const
{
    function = JSValue();
    lineNumber = -1;
    sourceURL = UString();

    CallFrame* callerFrame = callFrame->callerFrame();
    if (callerFrame->hasHostCallFrameFlag())
        return;

    CodeBlock* callerCodeBlock = callerFrame->codeBlock();
    if (!callerCodeBlock)
        return;
    unsigned bytecodeOffset = 0;
#if ENABLE(CLASSIC_INTERPRETER)
    if (!callerFrame->globalData().canUseJIT())
        bytecodeOffset = callerCodeBlock->bytecodeOffset(callFrame->returnVPC());
#if ENABLE(JIT)
    else
        bytecodeOffset = callerCodeBlock->bytecodeOffset(callerFrame, callFrame->returnPC());
#endif
#else
    bytecodeOffset = callerCodeBlock->bytecodeOffset(callerFrame, callFrame->returnPC());
#endif
    lineNumber = callerCodeBlock->lineNumberForBytecodeOffset(bytecodeOffset - 1);
    sourceID = callerCodeBlock->ownerExecutable()->sourceID();
    sourceURL = callerCodeBlock->ownerExecutable()->sourceURL();
    function = callerFrame->callee();
}

CallFrame* Interpreter::findFunctionCallFrameFromVMCode(CallFrame* callFrame, JSFunction* function)
{
    for (CallFrame* candidate = callFrame->trueCallFrameFromVMCode(); candidate; candidate = candidate->trueCallerFrame()) {
        if (candidate->callee() == function)
            return candidate;
    }
    return 0;
}

void Interpreter::enableSampler()
{
#if ENABLE(OPCODE_SAMPLING)
    if (!m_sampler) {
        m_sampler = adoptPtr(new SamplingTool(this));
        m_sampler->setup();
    }
#endif
}
void Interpreter::dumpSampleData(ExecState* exec)
{
#if ENABLE(OPCODE_SAMPLING)
    if (m_sampler)
        m_sampler->dump(exec);
#else
    UNUSED_PARAM(exec);
#endif
}
void Interpreter::startSampling()
{
#if ENABLE(SAMPLING_THREAD)
    if (!m_sampleEntryDepth)
        SamplingThread::start();

    m_sampleEntryDepth++;
#endif
}
void Interpreter::stopSampling()
{
#if ENABLE(SAMPLING_THREAD)
    m_sampleEntryDepth--;
    if (!m_sampleEntryDepth)
        SamplingThread::stop();
#endif
}

} // namespace JSC
