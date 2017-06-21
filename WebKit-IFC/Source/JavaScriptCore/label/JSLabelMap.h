//
//  JSLabelMap.h
//  JavaScriptCore
//
//  Created by Abhishek Bichhawat on 3/9/15.
//
//

#ifndef JSLabelMap_h
#define JSLabelMap_h

#include <stdio.h>

#include "JSLabelEntry.h"
#include "JSExportMacros.h"

namespace JSC {
	
	const int LABEL_MAP_SIZE = 4096; // map size
	class JSLabelMap {
		
	private:
		JSLabelEntry **map;
		int idx;
		static JSLabelMap* s_map;
        inline bool capacity() { return (idx < LABEL_MAP_SIZE); };
		
	public:
		JSLabelMap();
		JSLabelMap(JSLabelMap const&);
		JSLabelMap& operator = (JSLabelMap const&);
		JS_EXPORT_PRIVATE static JSLabelMap& labelMap();
		
		JS_EXPORT_PRIVATE bool isOrdered(uint64_t, uint64_t);
		JS_EXPORT_PRIVATE void append(uint64_t, uint64_t);
		~JSLabelMap();
	};
	
}

#endif
