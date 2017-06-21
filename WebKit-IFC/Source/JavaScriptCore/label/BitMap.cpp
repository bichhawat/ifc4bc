//
//  BitMap.cpp
//  JavaScriptCore
//
//  Created by Abhishek Bichhawat on 1/29/16.
//
//

#include "BitMap.h"

#include "config.h"
#include <stdio.h>

namespace JSC {
	
	BitMap* BitMap::s_map = NULL; // initialize pointer
    
	BitMap::BitMap() {
		map = new BitEntry*[M_SIZE];
		for (int i = 0; i < M_SIZE; i++) { // initialize map
			map[i] = NULL;
		};
        map[0] = new BitEntry("NULL", 0, 0, 0);
		idx = 0;
		setLast(0);
	}
	
	BitMap& BitMap::Bitmap() {
		if (s_map == NULL) { // is this the first call?
			s_map = new BitMap(); // create sole instance
		}
		return *s_map; // return pointer to instance
	}
	
	// -----------Private----------- //
	
	int BitMap::append(const char* n, uint64_t b, uint64_t a, uint64_t d) { // append Bit to map
        idx++; // move current map lcoation
        map[idx] = new BitEntry(n, b, a, d); // set map head to new BitEntry
        setLast(idx);
        return idx;
	}
	
	void BitMap::setLast(int i) {
		if (lastIdx != i) {
			lastIdx = i;
		}
	}
    
    int BitMap::search(const char* n) {
		for (int i = idx; i >= 0; i--) { 
            int index = strcmp(map[i]->getName(), n);
			if (index == 0) {
				return i; 
			}
		}
		return OUT_OF_BOUND;
	}
	
	// -----------Public----------- //
	int BitMap::put(const char* n, uint64_t b, uint64_t a, uint64_t d) { 
        bool isPresent = false;
        char* domain = new char[strlen(n)];
        strcpy(domain, n);
        int loc = search(domain);
        if (loc == OUT_OF_BOUND) { 
            if (capacity()) {
                return append(n, b, a, d);
            } else { //TODO: remove this or comment after debug
                printf("Map full in BitMap?\n");
            }
        }
        return loc;
	}
    
	uint64_t BitMap::getBits(const char* n) { 
        char* domain = new char[strlen(n)];
        strcpy(domain, n);
        int i = search(domain);
		if (i == OUT_OF_BOUND) { 
            return 0;
        } else {
			return map[i]->getBit();
		}
	}
    
    void BitMap::setBits(int index, uint64_t bits) {
        map[index]->setBit(bits);
	}
    
    uint64_t BitMap::getBits(int index) {
        return map[index]->getBit();
	}

    uint64_t BitMap::getVarLabel(int index) {
        return map[index]->getActLabel();
	}

    uint64_t BitMap::getRelLabel(int index) {
        return map[index]->getDecLabel();
	}

    int BitMap::getIndex(const char* n) {
        char* domain = new char[strlen(n)];
        strcpy(domain, n);
        int i = search(domain);
		if (i == OUT_OF_BOUND) { 
            return 0;
        } else {
			return i;
		}
	}
	
	BitMap::~BitMap() { 
		for (int i = idx; i >= 0; i--) { 
			delete map[i];
		}
		delete[] map;
	}
	
}
