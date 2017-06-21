/*
 *  FlowGraph.h
 *  JavaScriptCore
 *
 *  Created by Seth Just on 7/15/11.
 *  Copyright 2011 Utah State University. All rights reserved.
 *
 *  Brandon Shilrey - complete rewrite - 10/22/2011
 *
 *  Implementation adapted from "A Fast Algorithm for Finding Dominators in a Flowgraph"
 *  Thomas Lengauer and Robert Endre Tarjan
 *  - slight modification to produce immediate post-dominator
 */

#ifndef FlowGraph_h
#define FlowGraph_h


#include "config.h"
//Vineet
#include <wtf/Vector.h>


namespace JSC {
    // To make includes all work properly -- we get errors if we straight-up #include CodeBlock.h
    class CodeBlock;
    class Interpreter;
    
    class AListNode {
    public:
        AListNode();
        WTF::Vector<int> successor;
        WTF::Vector<int> predecessor;
        WTF::Vector<int> bucket;
        
        void dump();
    };
    
    class FlowGraph {
        int n;
        int count;
        CodeBlock* codeBlock;
        void add_edge( int from, int to);
        void dfs(int);
        
        
    public:
        
        AListNode* edges;
        
        int* semi;
        int* label;
        int* size;
        
        int* vertex;
        int* parent;
        int* ancestor;
        int* child;
        
        bool impException; // Abhi -- Include impexception or not
        
        // Return n-1 becuase of extra increment in last call to dfs(v)
        int getN() { return n-1; }        
        void dfs();
        FlowGraph();
        void createGraph(CodeBlock* cb, Interpreter*, bool);
        CodeBlock* code_block() { return codeBlock; }
        int Count() { return count; } // IFC4BC - removed -1 as added another exception node
        
        bool* loop; // indicating whether loop or not
        bool checkLoop (CodeBlock* cb, Interpreter*, int, int); // whether the branch contains loop or not
        
        void dump_tree();
        void dump_vertex();
        void dump_semi();
    };
    
}

#endif // FlowGraph_h











