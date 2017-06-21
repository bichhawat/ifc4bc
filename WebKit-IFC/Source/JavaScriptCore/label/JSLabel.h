/*
 *  JSLabel.h
 *  JavaScriptCore
 *
 *  Created by Alan Cleary on 6/23/11.
 *  Copyright 2011 Alan Cleary and Seth Just. All rights reserved.
 *
 */

#ifndef JSLabel_h
#define JSLabel_h

#include <stdint.h>
#include "JSExportMacros.h"

namespace JSC {
	
	class JSLabel {
		uint64_t label; // label's value
        // uint64_t iLabel;
        
        bool star; // for deferred no-sensitive upgrade check
                    // and property user defined. Will make it union later, if it works
	public:
        typedef struct pair{
            uint64_t clabel;
            // uint64_t ilabel;
            // uint64_t plabel;
        } pair;
        
        // uint64_t pLabel;
        
		JS_EXPORT_PRIVATE JSLabel();                  // constructor
		JS_EXPORT_PRIVATE JSLabel(uint64_t);          // overload
        JS_EXPORT_PRIVATE JSLabel(pair);          // overload
        JS_EXPORT_PRIVATE uint64_t Val() const;       // return label value
        // JS_EXPORT_PRIVATE uint64_t iVal() const;       // return label value
        JS_EXPORT_PRIVATE pair getPair() const;       // return label value
        JS_EXPORT_PRIVATE JSLabel Join(JSLabel);      // join labels
        JS_EXPORT_PRIVATE void vJoin(JSLabel);        // void join
        JS_EXPORT_PRIVATE void setVal(uint64_t);
        // JS_EXPORT_PRIVATE void setiVal(uint64_t);
        // IFC4BC --- for DNSU
        JS_EXPORT_PRIVATE bool Star() const;          // return the star for DNSU
        JS_EXPORT_PRIVATE void setStar(bool);         // set the star for DNSU
        // IFC4BC ------------ */
        JS_EXPORT_PRIVATE bool operator ==(const JSLabel&);
        JS_EXPORT_PRIVATE bool operator !=(const JSLabel&);
        
        JS_EXPORT_PRIVATE bool operator >(const JSLabel&);
        JS_EXPORT_PRIVATE bool operator <(const JSLabel&);
        
        JS_EXPORT_PRIVATE bool operator >=(const JSLabel&);
        JS_EXPORT_PRIVATE bool operator <=(const JSLabel&);
        
        JS_EXPORT_PRIVATE JSLabel& operator |=(const JSLabel&);
        JS_EXPORT_PRIVATE const JSLabel operator |(const JSLabel&) const;
        JS_EXPORT_PRIVATE JSLabel& operator =(const JSLabel&);
        JS_EXPORT_PRIVATE JSLabel& operator =(const pair);
        JS_EXPORT_PRIVATE bool NSU(JSLabel label);
        
        // Static members
        JS_EXPORT_PRIVATE static pair pcGlobalLabel;
        JS_EXPORT_PRIVATE static pair returnLabel;
        JS_EXPORT_PRIVATE static pair eventNodeLabel;
        JS_EXPORT_PRIVATE static pair argLabel[1000];
        JS_EXPORT_PRIVATE static pair eventContextLabel;
        
        JS_EXPORT_PRIVATE static bool ABORT_FLAG;
        JS_EXPORT_PRIVATE static bool BRANCH_FLAG;
    };
    
    
	
}

#endif // JSLabel_h
