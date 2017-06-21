/*
 *  StaticAnalyzer.cpp
 *  JavaScriptCore
 *
 *  Created by Seth Just on 7/15/11.
 *  Copyright 2011 Utah State University. All rights reserved.
 * 
 *  Rewritten by Brandon Shirley on 10/22/2011
 *  Implementation adapted from "A Fast Algorithm for Finding Dominators in a Flowgraph"
 *  by Thomas Lengauer and Robert Endre Tarjan
 *  - slight modification to produce immediate post-dominator
 *
 */

#include "StaticAnalyzer.h"
#include "CodeBlock.h"
#include "Instruction.h"


namespace JSC {
    
#if STAT_TIME	
    double  StaticAnalyzer::rtime = 0;
#endif  
    
    // Constructor
    StaticAnalyzer::StaticAnalyzer() {
        graph = FlowGraph();
    }
    
    
    int StaticAnalyzer::eval(int v) {
        if(graph.ancestor[v] == 0) return graph.label[v];
        else {
            compress(v);
            if(graph.semi[graph.label[graph.ancestor[v]]] >= graph.semi[graph.label[v]])
                return graph.label[v];
            else return graph.label[graph.ancestor[v]];
        }
    }
    
    void StaticAnalyzer::link(int v, int w) {
        int s = w;
        while (graph.semi[graph.label[w]] <  graph.semi[graph.label[graph.child[s]]]) {
            if(graph.size[s] + graph.size[graph.child[graph.child[s]]] >= 2 * graph.size[graph.child[s]]) {
                graph.ancestor[graph.child[s]] = s;
                graph.child[s] = graph.child[graph.child[s]];
            } else {
                graph.size[graph.child[s]] = graph.size[s];
                s = graph.ancestor[s] = graph.child[s];
            }
        }
        graph.label[s] = graph.label[w];
        graph.size[v] = graph.size[v] + graph.size[w];
        if (graph.size[v] < 2 * graph.size[w]) {
            int temp = s;
            s = graph.child[v];
            graph.child[v] = temp;
        }
        while (s != 0) {
            graph.ancestor[s] = v;
            s = graph.child[s];
        }
    }
    
    void StaticAnalyzer::compress(int v) {
        if(graph.ancestor[graph.ancestor[v]] != 0) {
            compress(graph.ancestor[v]);
            if(graph.semi[graph.label[graph.ancestor[v]]] < graph.semi[graph.label[v]]) {
                graph.label[v] = graph.label[graph.ancestor[v]];
            }
            graph.ancestor[v] = graph.ancestor[graph.ancestor[v]];
        }
    }
    
    
    void StaticAnalyzer::genContextTable(CodeBlock* codeBlock, Interpreter* interpreter, bool existsHandler) {
        
#if STAT_TIME
        clock_t start;
        clock_t end;
        start = clock();
#endif
        
        // Abhi -- to run with impException
        graph.impException = true;
    
        // Generate the control flow graph (CFG)
        graph.createGraph(codeBlock, interpreter, existsHandler);
        
        count = graph.Count();
        idom = new int[count];
        
        memset(idom, 0, sizeof(int) * count);
        
        
        // Perform DFS
        graph.dfs();
        
#if ADEBUG 
        // Dump reverse CFG, including DFS information
        graph.dump_tree();
        
        // Dump vertex numbering from DFS (vertex[] maps number->node)
//        graph.dump_vertex();  // Abhi -- Not needed for now
#endif
        
        graph.size[0] = graph.label[0] = graph.semi[0] = 0;
        
        for(int i = graph.getN(); i >= 2; i--) {
            int w = graph.vertex[i];
            for (size_t v = 0; v < graph.edges[w].predecessor.size(); v++) {
                int u = eval(graph.edges[w].predecessor.at(v));
                if(graph.semi[u] < graph.semi[w]) {
                    graph.semi[w] = graph.semi[u];
                }
            }
//            for (int v : graph.edges[w].predecessor) {
//                int u = eval(v);
//                if(graph.semi[u] < graph.semi[w]) {
//                    graph.semi[w] = graph.semi[u];
//                }
//            }
            // add w to bucket(vertex(semi(w)))
            graph.edges[graph.vertex[graph.semi[w]]].bucket.append(w);
            
            link(graph.parent[w],w);
            int u;
            for (size_t i = 0; i < graph.edges[graph.parent[w]].bucket.size(); i++) {
                int v = graph.edges[graph.parent[w]].bucket.at(i);
                u = eval(v); 
                if(graph.semi[u] < graph.semi[v]) idom[v] = u;
                else idom[v] = graph.parent[w];
            }
//            for (int v : graph.edges[graph.parent[w]].bucket) {
//                u = eval(v); 
//                if(graph.semi[u] < graph.semi[v]) idom[v] = u;
//                else idom[v] = graph.parent[w];
//            }
            graph.edges[graph.parent[w]].bucket.clear();           
        }
        
        for (int i = 2; i <= graph.getN(); i++) {
            int w = graph.vertex[i];
            if(idom[w] != graph.vertex[graph.semi[w]]){
                idom[w] = idom[idom[w]];
            }
        }
        
        // Artifically set to 0 node 1
        //idom[count-1] = 0;    //original
        idom[0] = 1;            // artificially set, should always be "true"
    
        // set the loop information 
        containsLoop = new bool[count];
        memset(containsLoop, false, sizeof(bool) * count);

        for (int i = 1; i < count; i++) {
            if (idom[i] != 0) {
                containsLoop[i] = graph.checkLoop (codeBlock, interpreter, i, idom[i]);
            }
        }
        
#if ADEBUG
        // Dump semi post-dominators
        graph.dump_semi();
#endif        
#if ADEBUG || DIDOM        
        printf("idom has\n");
        for (int i=0; i<count; i++) {
            if (idom[i]) printf("%d\t%d\n", i, idom[i]);
        }
        printf("\n");
#endif
        
#if STAT_TIME
        end = clock();
        clock_t diff = end - start;
        rtime += diff / (double)CLOCKS_PER_SEC;
#endif
    }
    
#if STAT_TIME
    void StaticAnalyzer::printTime() {
        //TODO: hack, write conversion to minutes and seconds?
        fprintf(stderr, "static\t0m%fs", rtime);
    }
#endif
}
