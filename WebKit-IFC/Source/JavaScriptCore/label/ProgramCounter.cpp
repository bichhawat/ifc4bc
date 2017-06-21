/*
 *  ProgramCounter.cpp
 *  JavaScriptCore
 *
 *  Created by Alan Cleary on 6/24/11.
 *  Copyright 2011 Alan Cleary and Seth Just. All rights reserved.
 *
 */

#include "ProgramCounter.h"

namespace JSC {
	
	ProgramCounter::ProgramCounter() {
		/* Location is set to -1 to ensure we never pop the sentinel node, as we 
         * will never execute the opcode at location -1
         */
		node = new PCNode(NULL, JSLabel(), -1, NULL, false, false, false, false);
		len = 0;
	}
	
    // Abhi -- added pos, func to facilitate handling exceptions
	void ProgramCounter::Push(JSLabel l, int i, Register* r, bool eF, bool h, bool b) {
		node = new PCNode(node, Head().Join(l), i, r, eF, h, b, getLoop());   // Abhi -- Added h, eF for exceptions
		len++;
	}
	
	void ProgramCounter::Pop() {
		if(len>0){
			PCNode *temp = node;
			node = temp->Next();
			len--;
		}
	}
	
	JSLabel ProgramCounter::Head() {
		return node->Val();
	}
	
	int ProgramCounter::Loc() {
		return node->IPDLoc();
	}
	
	int ProgramCounter::Len() {
		return len;
	}
	
	void ProgramCounter::Join(JSLabel label) {
		node = new PCNode(node->Next(), node->Val().Join(label), node->IPDLoc(), node->reg,
                          node->excFlag, node->handler, node->branchFlag, node->isLoop);
	}
    
    void ProgramCounter::Join(JSLabel label, bool funHandler, bool excHandler) {
		node = new PCNode(node->Next(), node->Val().Join(label), node->IPDLoc(), node->reg,
                          excHandler, funHandler, node->branchFlag, node->isLoop);
	}
    
    void ProgramCounter::Join(JSLabel label, bool branch) {
		node = new PCNode(node->Next(), node->Val().Join(label), node->IPDLoc(), node->reg,
                          node->excFlag, node->handler, branch, node->isLoop);
	}
	
	Register* ProgramCounter::Reg() {
		return node->reg;
	}
    
    // Abhi -- Exception handling
    bool ProgramCounter::funHandler() {
        return node->handler;
    }

    bool ProgramCounter::excHandler() {
        return node->excFlag;
    }
    
    bool ProgramCounter::branchFlag() {
        // return true;
        return node->branchFlag;
    }
    
    bool ProgramCounter::getLoop(){
        return node->isLoop;
    }
    
    void ProgramCounter::setLoop(bool loop){
        node->isLoop = loop;
    }
    // Abhi ----
}
