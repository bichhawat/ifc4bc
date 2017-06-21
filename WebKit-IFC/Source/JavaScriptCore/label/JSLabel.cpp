/*
 *  JSLabel.cpp
 *  JavaScriptCore
 *
 *  Created by Alan Cleary on 6/23/11.
 *  Copyright 2011 Alan Cleary and Seth Just. All rights reserved.
 *
 */

#include "config.h"
#include "JSLabel.h"

namespace JSC {
	
    // JSLabel constructor
	JSLabel::JSLabel() {
		label = 0;
        // iLabel = 0xffffffffffffffff;
        
        // pLabel = 0;
        // IFC4BC  --- for DNSU
        star = false;
        //printf("::JSLabel()\n");
        
		// Alan commented this out
        //*label = URLMap::urlmap().lastAsVal();
	}
	
	// JSLabel constructor overload; Takes value
	JSLabel::JSLabel(uint64_t l) {
		//printf("::JSLabel(%" PRIx64 ")\n", l);
		label = l;
        // iLabel = i;
        
        // pLabel = p;
        // IFC4BC --- star is set only in setStar()
        star = false;
	}
    
    // JSLabel constructor overload; Takes value
	JSLabel::JSLabel(pair l) {
		//printf("::JSLabel(%" PRIx64 ")\n", l);
		label = l.clabel;
        // iLabel = l.ilabel;
        // pLabel = l.plabel;
        // IFC4BC --- star is set only in setStar()
        star = false;
	}

   
    JSLabel::pair JSLabel::pcGlobalLabel;
    
    JSLabel::pair JSLabel::returnLabel;
    
    JSLabel::pair JSLabel::eventNodeLabel;
    
    JSLabel::pair JSLabel::eventContextLabel;
    
    JSLabel::pair JSLabel::argLabel[];
//    
//    JSLabel::argLabel[] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//                                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//                                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//                                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//                                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//                                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//                                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//                                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//                                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//                                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, \
//        0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    
    bool JSLabel::ABORT_FLAG = false;
    bool JSLabel::BRANCH_FLAG = false;

	// Get labels value
	uint64_t JSLabel::Val() const {
		return label;
	}
    
    /*
    uint64_t JSLabel::iVal() const {
		return iLabel;
	}
    */
    
    JSLabel::pair JSLabel::getPair() const {
		pair temp;
        temp.clabel = label;
        // temp.ilabel = iLabel;
        // temp.plabel = pLabel;
        return temp;
	}
	
	// return new label with OR'd vals, does not effect current label
    // What is the point of the function? Seems like we should have a 
    // static function that takes to labels and returns the join, or just
    // overload the | operator - probably should TODO:
	JSLabel JSLabel::Join(JSLabel l) {
        // IFC4BC - For DNSU --
        JSLabel ret;
        /*
        if (JSLabelMap::labelMap().isOrdered(l.Val(), this->Val()))
        {
            ret = l; // Allowed check as label is higher in the lattice than current pc
        }
        else if (JSLabelMap::labelMap().isOrdered(this->Val(), l.Val()))
        {
            ret = *this; // Allowed check as label is higher in the lattice than current pc
        }
        else */
        {
            // ret = JSLabel(l.Val() | this->Val(), l.pLabel & this->pLabel);
            ret = JSLabel(l.Val() | this->Val());
        }
        // ret.pLabel = l.pLabel | this->pLabel;
        ret.setStar(l.Star() || this->Star());
        return ret;
		// return JSLabel(l.Val() | this->Val());
	}
    
	void JSLabel::setVal(uint64_t l) {
        label = l;
    }
    /*
    void JSLabel::setiVal(uint64_t l) {
        iLabel = l;
    }
    */
    bool JSLabel::operator==(const JSLabel& rhs) {
        if((label ^ rhs.label) == 0 && (star == rhs.star))
            // && /*(iLabel ^ rhs.iLabel) == 0 &&*/ (pLabel ^ rhs.pLabel) == 0)
            return true;
        return false;
    }
    
    bool JSLabel::operator!=(const JSLabel& rhs) {
        return !(*this == rhs);
    }
    
    bool JSLabel::operator >(const JSLabel& rhs) {
        if(*this == rhs) return false;
        // if (star)   return true;
        // if (rhs.star) return false;
        if((label | rhs.label) == label /* && (pLabel | rhs.pLabel) == pLabel */) return true;
        return false;
    }
    
    bool JSLabel::operator <(const JSLabel& rhs) {
        if(*this == rhs) return false;
        // if (rhs.star)   return true;
        // if (star)   return false;
        if((label | rhs.label) == rhs.label /* && (pLabel | rhs.pLabel) == rhs.pLabel */) return true;
        return false;
    }
    
    // Use this check
    // i.e. if vo >= pc execute
    bool JSLabel::operator >=(const JSLabel& rhs) { // execute
        if(*this == rhs) return true;
        // if (star)   return true;
        // if (rhs.star) return false;
        if((label | rhs.label) == label /*&& (pLabel | rhs.pLabel) == pLabel */) return true;
        return false;
    }
           
    bool JSLabel::operator <=(const JSLabel& rhs) {
        if(*this == rhs) return true;
        // if (rhs.star)   return true;
        // if (star)   return false;
        if((label | rhs.label) == rhs.label /*&& (pLabel | rhs.pLabel) == rhs.pLabel*/) return true;
        return false;
    }
    
    
    JSLabel& JSLabel::operator |=(const JSLabel& rhs) {
        this->label |= rhs.label;
        // this->pLabel|= rhs.pLabel;
        this->star  |= rhs.star;
        return *this;
    }
    
    const JSLabel JSLabel::operator |(const JSLabel& other) const{
        JSLabel result = *this;
        result |= other;
        return result;
    }
    
    JSLabel& JSLabel::operator =(const JSLabel& rhs) {
        if(this != &rhs) {
            this->label = rhs.label;
            // this->iLabel = rhs.iLabel;
            // this->pLabel = rhs.pLabel;
            this->star = rhs.star;
        }
        return * this;
    }
    
    JSLabel& JSLabel::operator =(const pair rhs) {
        this->label = rhs.clabel;
        // this->iLabel = rhs.ilabel;
        // this->pLabel = rhs.plabel;
        this->star = false;
        return *this;
    }
    
    bool JSLabel :: NSU(JSLabel l) {
        // this is the context and l is the label of the value being changed.
        // returns true for valid upgrades
        // false for sensitive upgrades
        if (BRANCH_FLAG == false)
            return true;
        if (this->Val() == 1) { // PC is policy
            return true;
        }
        else if (l.Val() == 1) { // Modifying policy value even though PC is not policy
            return false;
        }
        /*
        if (JSLabelMap::labelMap().isOrdered(l.Val(), this->Val()))
        {
            return true; // Allowed check as label is higher in the lattice than current pc
        }*/
        // if (*this == l) return true;
        // if (l.star)   return true;
        // if (star)   return false;
        // IFC4BC - For global objects like window, we allow if it has a label 0.
        // if (l.Val() == 0 || label == 0) return true;
        if ((l.label | this->label) == l.label /*&& (pLabel | l.pLabel) == l.pLabel*/)
            return true;
        else
            return false;
        // return (l >= label) ? true : false;
        // TODO - add code for star
        // return (l.Val() == 0 || l >= label) ? true : false;
    }
    // if vo < pc terminate - > don't dynamically upgrade
    
    // IFC4BC - for DNSU
    // Return the star value for DNSU
    bool JSLabel :: Star() const {
        return star;
    }
    
    // Set the star value
    void JSLabel :: setStar (bool s){
        star = s;
    }
    // IFC4BC --------------------------------
}
