//
//  JSLabelMap.cpp
//  JavaScriptCore
//
//  Created by Abhishek Bichhawat on 3/9/15.
//
//

#include "JSLabelMap.h"
#include "config.h"

namespace JSC {
	
	JSLabelMap* JSLabelMap::s_map = NULL;
    
	JSLabelMap::JSLabelMap() {
		map = new JSLabelEntry*[LABEL_MAP_SIZE];
		for (int i = 0; i < LABEL_MAP_SIZE; i++) {
			map[i] = NULL;
		};
		idx = 0; 
	}
	
	JSLabelMap& JSLabelMap::labelMap() {
		if (s_map == NULL) {
			s_map = new JSLabelMap();
		}
		return *s_map;
	}
	
	bool JSLabelMap::isOrdered(uint64_t top, uint64_t bottom) {
		for (int i = (idx - 1); i >= 0; i--) {
			if (map[i]->getTopValue() == top) {
                if (map[i]->getBottomValue() == bottom) {
                    return true;
                }
			}
		}
		return false;
	}
    	
	void JSLabelMap::append(uint64_t top, uint64_t bottom) {
		if (!isOrdered(top, bottom)) {
			if (capacity()) {
                map[idx] = new JSLabelEntry(top, bottom);
                idx++;
			} else { 
                printf("Map full in JSLabelMap.cpp?\n");
            }
		} 
	}
		
	JSLabelMap::~JSLabelMap() {
		for (int i = idx; i >= 0; i--) {
			delete map[i];
		}
		delete[] map; 
	}

}
