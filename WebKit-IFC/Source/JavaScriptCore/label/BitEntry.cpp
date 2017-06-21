//
//  BitEntry.cpp
//  JavaScriptCore
//
//  Created by Abhishek Bichhawat on 1/29/16.
//
//

#include "BitEntry.h"

namespace JSC {
    
	BitEntry::BitEntry(const char* n, uint64_t b, uint64_t a, uint64_t d) {
		name = strdup(n);
		this->bits = b;
        this->actLabel = a;
        this->decLabel = d;
	}
	
	uint64_t BitEntry::getBit() {
		return bits;
	}
    
    void BitEntry::setBit(uint64_t b) {
		bits = b;
	}
	
	const char* BitEntry::getName() const {
		return name;
	}
    
	uint64_t BitEntry::getActLabel() {
		return actLabel;
	}

	uint64_t BitEntry::getDecLabel() {
		return decLabel;
	}
	
}
