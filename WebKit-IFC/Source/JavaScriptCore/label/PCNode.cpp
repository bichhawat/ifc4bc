/*
 *  PCNode.cpp
 *  JavaScriptCore
 *
 *  Created by Alan Cleary on 6/28/11.
 *  Copyright 2011 Alan Cleary and Seth Just. All rights reserved.
 *
 */

#include "PCNode.h"
#include "config.h"

namespace JSC {
	
	PCNode::PCNode(PCNode *n, JSLabel l, int i, Register* r, bool eH, bool fH, bool branch, bool iL) {
		node = n;
		value = l;
		ipdloc = i;
		reg = r;
        handler = fH;
        excFlag = eH;
        branchFlag = branch;
        isLoop = iL;
	}
	
	JSLabel PCNode::Val() {
		return value;
	}
	
	int PCNode::IPDLoc() {
		return ipdloc;
	}
	
	PCNode* PCNode::Next() {
		return node;
	}
    
}
