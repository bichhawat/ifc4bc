/*
 *  StaticAnalyzer.h
 *  JavaScriptCore
 *
 *  Created by Seth Just on 7/15/11.
 *  Copyright 2011 Utah State University. All rights reserved.
 * 
 * Contributors:
 *    Seth Just       - Initial implementation
 *    Brandon Shirley - timing functionality
 *    Brandon Shilrey - complete rewrite - 10/22/2011
 *  Implementation adapted from "A Fast Algorithm for Finding Dominators in a Flowgraph"
 *  by Thomas Lengauer and Robert Endre Tarjan
 *  - slight modification to produce immediate post-dominator
 */

#ifndef StaticAnalyzer_h
#define StaticAnalyzer_h

#include "config.h"
#include "FlowGraph.h"
#include <time.h>

namespace JSC {
#define STAT_TIME 0
#define ADEBUG 0    // Abhi
#define DIDOM 0
    
    class CodeBlock;
    
    class StaticAnalyzer {
        int* idom;
        int eval(int);
        void link(int, int);
        void compress(int);
        FlowGraph graph;
        
        bool* containsLoop;

        
#if STAT_TIME
        static double   rtime;
#endif  
    public:
        StaticAnalyzer();
        void    genContextTable(CodeBlock*, Interpreter*, bool =false);
        int     IDom(int node) {return idom[node];} //{ printf("node: %d idom[node]: %d\n", node, idom[node]); return idom[node]; }
        int     count;
        bool    loop (int node) {return graph.loop[node];} // whether loop or not
        bool    cLoop (int node) {return containsLoop[node];} // whether the branch contains loop or not
#if STAT_TIME
        static void printTime();
#endif
    };
    
}

#endif // StaticAnalyzer_h
