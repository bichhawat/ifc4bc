/*
 *  PCNode.h
 *  JavaScriptCore
 *
 *  Created by Alan Cleary on 6/28/11.
 *  Copyright 2011 Alan Cleary and Seth Just. All rights reserved.
 *
 */

#ifndef PCNode_h
#define PCNode_h

#include "JSLabel.h"

namespace JSC {
	class Register;

	class PCNode {
		PCNode *node; // pointer to previous node
		JSLabel value; // node value
		int ipdloc;
        
	public:
		PCNode(PCNode*, JSLabel, int, Register*, bool, bool, bool, bool); // constructor
		PCNode* Next(); // next node (for pop)
		JSLabel Val(); // return value
		int IPDLoc();
		Register* reg;
        
        bool handler; // Abhi -- exception details
        bool excFlag; // Abhi -- exception handler exists
        bool branchFlag; // Abhi -- branch flag
        
        bool isLoop;
    };
}

#endif // PCNode_h
