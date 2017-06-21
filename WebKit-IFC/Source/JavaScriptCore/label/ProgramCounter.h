/*
 *  ProgramCounter.h
 *  JavaScriptCore
 *
 *  Created by Alan Cleary on 6/24/11.
 *  Copyright 2011 Alan Cleary and Seth Just. All rights reserved.
 *
 */

#ifndef ProgramCounter_h
#define ProgramCounter_h

#include "config.h"
#include "JSLabel.h"
#include "PCNode.h"

namespace JSC {
	class Register;
	
	class ProgramCounter {
		PCNode *node; // current node
		int len;
	public:
		ProgramCounter(); // constructor
		void Push(JSLabel, int, Register*, bool = false, bool = false, bool = false); // push node to stack
		void Pop(); // remove and return head
		JSLabel Head(); // return head
		int Loc();
		int Len();
        
		void Join(JSLabel);
		Register* Reg();
        
        bool funHandler(); // Abhi -- Exception Handling
        bool excHandler(); // Abhi -- Global exception handler
        bool branchFlag(); // Abhi -- Global exception handler
        void Join(JSLabel, bool, bool); // Abhi -- Join for function calls
        void Join(JSLabel, bool); // Abhi -- Join for branch calls
        
        void setLoop(bool);
        bool getLoop();
    };
}

#endif // ProgramCounter_h
