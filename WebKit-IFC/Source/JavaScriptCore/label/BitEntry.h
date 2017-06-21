//
//  BitEntry.h
//  JavaScriptCore
//
//  Created by Abhishek Bichhawat on 1/29/16.
//
//

#ifndef __JavaScriptCore__BitEntry__
#define __JavaScriptCore__BitEntry__

#include <stdint.h>
#include <string.h>

namespace JSC {
    
	class BitEntry {
        
	private:
		const char* name;                 
        uint64_t bits;
        uint64_t actLabel;
        uint64_t decLabel;
		
	public:
		BitEntry(const char*, uint64_t, uint64_t, uint64_t);
		const char* getName() const;
        uint64_t getBit();
        void setBit(uint64_t);
        uint64_t getActLabel();
        uint64_t getDecLabel();
	};
	
}

#endif /* defined(__JavaScriptCore__BitEntry__) */
