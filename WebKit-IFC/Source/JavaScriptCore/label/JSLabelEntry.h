//
//  JSLabelEntry.h
//  JavaScriptCore
//
//  Created by Abhishek Bichhawat on 3/9/15.
//
//

#ifndef JSLabelEntry__h
#define JSLabelEntry__h

namespace JSC {
    
	class JSLabelEntry {
        
	private:
		uint64_t topValue;
		uint64_t bottomValue;
		
	public:
		JSLabelEntry(uint64_t, uint64_t);
		uint64_t getTopValue();
		uint64_t getBottomValue();
	};
	
}

#endif 
