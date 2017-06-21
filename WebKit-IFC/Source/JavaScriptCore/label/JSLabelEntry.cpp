//
//  JSLabelEntry.cpp
//  JavaScriptCore
//
//  Created by Abhishek Bichhawat on 3/9/15.
//
//

#include "JSLabelEntry.h"

namespace JSC {
    
	JSLabelEntry::JSLabelEntry(uint64_t top, uint64_t bottom) {
		topValue = top;
		bottomValue = bottom;
	}
	
	uint64_t JSLabelEntry::getTopValue() {
		return topValue;
	}

	uint64_t JSLabelEntry::getBottomValue() {
		return bottomValue;
	}
	
}
