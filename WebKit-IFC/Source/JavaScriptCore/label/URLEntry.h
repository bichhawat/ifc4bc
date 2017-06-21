/*
 *  URLEntry.h
 *  JavaScriptCore
 *
 *  Created by Alan Cleary on 7/7/11.
 *  Copyright 2011 Alan Cleary and Seth Just. All rights reserved.
 *
 */

#ifndef URLEntry_h
#define URLEntry_h

#include "JSLabel.h"
#include <stdint.h>
#include <string.h>

namespace JSC {

    
	class URLEntry {
	
	private:
		const char* url;                        // taken from scripts url UString
        JSLabel value;                         // generated based on map index
		
	public:
		URLEntry(const char*, uint64_t value);  // takes url string and generated binary
		const char* getURL() const;             // returns key of self
        JSLabel getValue();                    // returns value of self
	};
	
}

#endif // URLEntry_h
