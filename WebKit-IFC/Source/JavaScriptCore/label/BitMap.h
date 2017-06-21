//
//  BitMap.h
//  JavaScriptCore
//
//  Created by Abhishek Bichhawat on 1/29/16.
//
//

#ifndef __JavaScriptCore__BitMap__
#define __JavaScriptCore__BitMap__

#include "BitEntry.h"

#include <string.h>
#include <stdio.h>

#include "JSExportMacros.h"

namespace JSC {
	
	const int OUT_OF_BOUND = 100; // return instead of null
    const int M_SIZE = 64;
    
	class BitMap {
		
	private:
		BitEntry **map; // the map!
		int idx; // current postition in map
		static BitMap* s_map; // member pointer to intself
            
		int append(const char*, uint64_t, uint64_t, uint64_t);
		int search(const char*);
		inline bool capacity() { return (idx+1 < M_SIZE); }; // checks if the map is full
		
		int lastIdx;
		void setLast(int);

        BitMap(); // map constructor

	public: 
        
		// ctor, copy-ctor, and assignment opperators
		BitMap(BitMap const&);
		BitMap& operator = (BitMap const&);
		JS_EXPORT_PRIVATE static BitMap& Bitmap();
		JS_EXPORT_PRIVATE int getIndex(const char* n);
		JS_EXPORT_PRIVATE uint64_t getBits(const char*);
		JS_EXPORT_PRIVATE uint64_t getBits(int);
        JS_EXPORT_PRIVATE uint64_t getVarLabel(int);
        JS_EXPORT_PRIVATE uint64_t getRelLabel(int);
		JS_EXPORT_PRIVATE void setBits(int, uint64_t);
		JS_EXPORT_PRIVATE int put(const char* n, uint64_t b, uint64_t, uint64_t);

		~BitMap(); // destructor
	};
	
}

#endif /* defined(__JavaScriptCore__BitMap__) */
