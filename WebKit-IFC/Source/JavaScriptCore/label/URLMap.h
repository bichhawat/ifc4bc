/*
 *  URLMap.h
 *  JavaScriptCore
 *
 *  Created by Alan Cleary on 7/7/11.
 *  Copyright 2011 Alan Cleary and Seth Just. All rights reserved.
 *
 */

#ifndef URLMap_h
#define URLMap_h

#include "URLEntry.h"
#include "JSLabel.h"

#include <string.h>
#include <stdio.h>

#include "JSExportMacros.h"

namespace JSC {
	
	const int OUT_OF_BOUNDS = 100; // return instead of null
	const int MAP_SIZE = 64; // map size
	
	class URLMap {
		
	private:
		URLEntry **map; // the map!
		int idx; // current postition in map
		static URLMap* s_map; // member pointer to intself
        char** policyArray; 
        int policyCount = 0;
		
		void append(const char*, bool isPolicy); // appends url onto map
		int search(const char*); // searches for url in the map and returns its index
		const char* filter(const char*); // filter urls
		inline bool capacity() { return (idx+1 < MAP_SIZE); }; // checks if the map is full
		
		JSLabel lastLabel;
		int lastIdx;
		void setLast(int);
		
	public: // puts/gets will be fed with program->sourceURL().utf8().data() from the interpretor (subject to change for functions and evals)
		        
		// ctor, copy-ctor, and assignment opperators
		URLMap(); // map constructor
		URLMap(URLMap const&);
		URLMap& operator = (URLMap const&);
		JS_EXPORT_PRIVATE static URLMap& urlmap(); // validate member pointer
		
		JS_EXPORT_PRIVATE JSLabel getLabel(const char*); // takes script url as string and finds value
		JS_EXPORT_PRIVATE void put(const char*, bool isPolicy); // puts script url string in map and generates a value
        JS_EXPORT_PRIVATE void readPolicy();
		JSLabel head(); // returns JSLabel at head of map
		char * sHead(); // return head as char* array
		JS_EXPORT_PRIVATE JSLabel lastAsLabel();
		JS_EXPORT_PRIVATE uint64_t lastAsVal();
		~URLMap(); // destructor
	};
	
}

#endif //URLMap
