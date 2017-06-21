/*
 *  URLEntry.cpp
 *  JavaScriptCore
 *
 *  Created by Alan Cleary on 7/7/11.
 *  Copyright 2011 Alan Cleary and Seth Just. All rights reserved.
 *
 */

#include "URLEntry.h"

namespace JSC {

	URLEntry::URLEntry(const char* src, uint64_t value/*, uint64_t iValue*/) {
		// printf("URLEntry received %s\n", src);
		url = strdup(src);
		// printf("URLEntry stored %s as %s\n", src, url);
		this->value = JSLabel(value);
        // printf("URLEntry label %llu\n", this->value.Val());
	}
	
	const char* URLEntry::getURL() const {
		//printf("URLEntry is returning url %s\n", url);
		return url;
	}
	
	JSLabel URLEntry::getValue() {
		return value;
	}
    
	
}
