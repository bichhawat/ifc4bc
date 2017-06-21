/*
 *  FlowGraph.cpp
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
 *
 */

#include "FlowGraph.h"
#include "CodeBlock.h"

namespace JSC
{
    
    // Start AlistNode class functions
    AListNode::AListNode() {
    }
    // End AlistNode class functions
    
    FlowGraph::FlowGraph() {
        
    }
    
    
    void FlowGraph::createGraph(CodeBlock* cb, Interpreter* interpreter, bool existsHandler) {
        
        
        // Initialize instance variables
        codeBlock = cb;
        
        // Initialize locals
        Instruction* begin = codeBlock->instructions().begin();
        Instruction* vPC = begin;
        
        // Exception Handling details
        const size_t numHandlers = codeBlock->numberOfExceptionHandlers();
        HandlerInfo* hInfo;
        int retNode = 0;
        
        // Get number of instructions
        count = (int) (codeBlock->instructions().end() - codeBlock->instructions().begin()) + 1;
        
        if (interpreter->isOpcode((codeBlock->instructions().end() - 2)->u.opcode) &&
            (interpreter->getOpcodeID((codeBlock->instructions().end() - 2)->u.opcode) == op_ret)) {
            retNode = count - 3;
        }
        else if (interpreter->isOpcode((codeBlock->instructions().end() - 3)->u.opcode) &&
            (interpreter->getOpcodeID((codeBlock->instructions().end() - 3)->u.opcode) == op_ret_object_or_this)) {
            retNode = count - 4;
        }
        
        edges = new AListNode[count];
        for(int i = 0; i < count; i++) {
            edges[i] = AListNode();
        }
        
        // Set the loop information
        loop = new bool[count];
        memset(loop, false, sizeof(bool) * count);
        
        // Iterate over OPCODES to build control flow graph (CFG)
        while (vPC < codeBlock->instructions().end()) {
            // Pull out opcode
            int opcode = interpreter->getOpcodeID(vPC->u.opcode);
            
            // TODO: Could int vs long size become issue
            int pos = (long) (vPC-begin);
            // Get length of particular opcode, use to inrement to next instruction
            int length = opcodeLengths[opcode];

            bool found = false;     // Check if handler found
            bool expExc = false;
            // Abhi -- For edges for "implicit" exceptions
            switch (opcode) {
                    
                    // direct throws
                case op_throw:
                case op_throw_reference_error:
                    
                    expExc = true;
                    // CHECK_FOR_EXCEPTION / TIMEOUT might not be required for edges
                    // Throw exception via CHECK_FOR_TIMEOUT
                    
                case op_loop:
                case op_loop_if_true:
                case op_loop_if_false:
                
                // Throw exception via CHECK_FOR_EXCEPTION
                case op_jless:
                case op_jlesseq:
                case op_jgreater:
                case op_jgreatereq:
                case op_jnless:
                case op_jnlesseq:
                case op_jngreater:
                case op_jngreatereq:
                case op_strcat:
                case op_push_scope:
                case op_next_pname:
                case op_eq:
                case op_neq:
                case op_stricteq:
                case op_nstricteq:
                case op_less:
                case op_lesseq:
                case op_greater:
                case op_greatereq:
                case op_pre_inc:
                case op_post_inc:
                case op_pre_dec:
                case op_post_dec:
                case op_to_jsnumber:
                case op_negate:
                case op_add:
                case op_mul:
                case op_div:
                case op_mod:
                case op_sub:
                case op_lshift:
                case op_rshift:
                case op_urshift:
                case op_bitand:
                case op_bitxor:
                case op_bitor:
                case op_not:
                case op_instanceof:
                case op_resolve_base:
                case op_get_by_id:
                case op_get_by_id_getter_proto:
                case op_get_by_id_custom_proto:
                case op_get_by_id_getter_self:
                case op_get_by_id_custom_self:
                case op_get_by_id_generic:
                case op_get_by_id_getter_chain:
                case op_get_by_id_custom_chain:
                case op_put_by_id:
                case op_put_by_id_generic:
                case op_get_by_pname:
                case op_get_arguments_length:
                case op_get_by_val:
                case op_put_by_val:
                
                 // CHECK_FOR_TIMEOUT/EXCEPTION
                case op_loop_if_less:
                case op_loop_if_lesseq:
                case op_loop_if_greater:
                case op_loop_if_greatereq:
                
                    // Direct throw
                case op_new_regexp:
                case op_check_has_instance:
                case op_resolve:
                case op_resolve_skip:
                case op_resolve_global:
                case op_resolve_global_dynamic:
                case op_ensure_property_exists:
                case op_resolve_with_base:
                case op_resolve_with_this:
                case op_del_by_val:
                case op_call_eval:
                    
                    // Throw and CHECK_FOR_EXCEPTION
                    // Currently, the called function returns and retains the label in both cases - exception/no-exception
                    // On normal return, we pop at op_call; else we pop at the idom (exception handler)
                case op_call:
                case op_call_varargs:
                case op_del_by_id:
                case op_construct:
                case op_in:
                {
                    if (expExc || impException){
                        if (numHandlers > 0) {
                            int num = 0;
                            while ((unsigned)num < numHandlers) {
                                hInfo = &codeBlock->exceptionHandler(num++);
                                if ((hInfo->start <= (unsigned)pos) && (hInfo->end > (unsigned)pos)) {
                                    add_edge(pos, hInfo->target);  // target contains where it should be handled
                                    found = true;
                                    break;
                                }
                            }
                        }
                        // If no handler is found, add an edge to the exception node. Making count as exception node
                        // ----- Hope this does not break anything ----- 
                        // ret might occur in between causing confusion as synthetic exit node might be the IPD,
                        // even though there is no handler or the handler is present in the same function itself.
                        if (!found && existsHandler)
                            add_edge(pos, count - 1);
                    }
                }
                default:
                    break;
            }
            
            // Add edges for implicit exceptions across functions
            // The edges would go to the synthetic exit node of the function.
            // Abhi ---------------------------------------------------------------------
            
            switch (opcode) {
                    //----------- CONDITIONAL JUMPS (I.E. BRANCHES) -----------//
                    
                    // Conditional w/ single offset in vPC[2]
                case op_loop_if_true:
                case op_loop_if_false:
                case op_jtrue:
                case op_jfalse:
                case op_jempty: // Abhi -- opcode for finally block
                case op_jeq_null:
                case op_jneq_null:
                    add_edge(pos, pos + vPC[2].u.operand);
                    add_edge(pos, pos + length);
                    break;
  
                    // Conditional w/ single offset in vPC[3]
                case op_jneq_ptr:
                case op_loop_if_less:
                case op_loop_if_lesseq:
                case op_loop_if_greater:
                case op_loop_if_greatereq:
                case op_jnless:
                case op_jless:
                case op_jnlesseq:
                case op_jlesseq:
                case op_jgreater:
                case op_jgreatereq:
                case op_jngreater:
                case op_jngreatereq:
                    add_edge(pos, pos + vPC[3].u.operand);
                    add_edge(pos, pos + length);
                    break;
                    
                    // Property name getter may branch; stores offset in vPC[5]
                case op_get_pnames:
                    add_edge(pos, pos + vPC[5].u.operand);
                    add_edge(pos, pos + length);
                    break;
                    
                    // Property name interator stores offset in vPC[6]
                case op_next_pname:
                    add_edge(pos, pos + vPC[6].u.operand);
                    add_edge(pos, pos + length);
                    break;
                    
// Macro to loop over a SimpleJumpTable, as in CodeBlock::dump()
#define ADD_SWITCH_EDGES() \
Vector<int32_t>::const_iterator end = table.branchOffsets.end(); \
for (Vector<int32_t>::const_iterator iter = table.branchOffsets.begin(); iter != end; ++iter) { \
if (!*iter) \
continue; \
add_edge(pos, pos + *iter); \
}
                    
                    // Switches have jump table index in vPC[1] and default target in vPC[2]
                case op_switch_imm: {
                    SimpleJumpTable table = codeBlock->immediateSwitchJumpTable(vPC[1].u.operand);
                    ADD_SWITCH_EDGES();
                    add_edge(pos, pos + vPC[2].u.operand);
                    break;
                }
                    
                case op_switch_char: {
                    SimpleJumpTable table = codeBlock->characterSwitchJumpTable(vPC[1].u.operand);
                    ADD_SWITCH_EDGES();
                    add_edge(pos, pos + vPC[2].u.operand);
                    break;
                }
                    
                    // String Switches use a different type for storing the table, so our macro doesn't work
                case op_switch_string: {
                    StringJumpTable table = codeBlock->stringSwitchJumpTable(vPC[1].u.operand);
                    StringJumpTable::StringOffsetTable::const_iterator end = table.offsetTable.end();
                    for ( StringJumpTable::StringOffsetTable::const_iterator iter = table.offsetTable.begin(); iter != end; ++iter) {
                        add_edge(pos, pos + iter->second.branchOffset);
                    }
                    add_edge(pos, pos + vPC[2].u.operand);
                    break;
                }
                    
                    //----------- UNCONDITIONAL JUMPS -----------//
                    
                    // Unconditional w/ offset in vPC[1]
                case op_jmp:
                case op_loop:
                    add_edge(pos, pos + vPC[1].u.operand);
                    break;
                    
                    // Unconditional w/ offset in vPC[2]
                case op_jmp_scopes:
                    //Vineet - Commenting the op_jsr case, as it is not a valid opcode in this Javascriptcore
                    //case op_jsr:
                    add_edge(pos, pos + vPC[2].u.operand);
                    break;
                    
                    //----------- OTHER OPCODES -----------//
                    // Abhi -- Handled above
                    /* Abhi - EXCEPTION HANDLING
                    
                case op_throw_reference_error:   // Statements which throw reference error -- Explicit error
                case op_throw:
                {
                    bool found = false;     // Check if handler found
                    int num = 0;
                    while ((unsigned)num < numHandlers) {
                        hInfo = &codeBlock->exceptionHandler(num++);
                        if ((hInfo->start <= (unsigned)pos) && (hInfo->end > (unsigned)pos)) {
                            add_edge(pos, hInfo->target);  // target contains where it should be handled
                            found = true;
                            break;
                        }
                    }
                    // No handler found. Jump to end of the program!
                    if (!found)     add_edge(pos, count - 3); // Assuming, end is 2 bytes long.
                    break;
                }
                    //Abhi -- End of Exception Handling case */
                    
                    // End of method
                case op_end:
                case op_ret:
                    if (pos == count - 3)
                        add_edge(pos, count - 1); // edge to last node - SEN
                    else
                        add_edge(pos, retNode); // edge to itself or last ret node

                    break;
                    
                case op_ret_object_or_this:
                    if (pos == count - 4)
                        add_edge(pos, count - 1); // edge to last node - SEN
                    else
                        add_edge(pos, retNode); // edge to last constructor_ret node
                    break;
                    
                    // Non-jumping/branching opcodes
                default:
                    add_edge(pos, pos+length);
                    break;
            }
            // Loop indication
            switch (opcode) {
                case op_loop:
                    if (pos > pos + vPC[1].u.operand)
                        loop[pos + vPC[1].u.operand] = true;
                    else
                        loop[pos] = true;
                    break;
                case op_loop_if_true:
                case op_loop_if_false:
                    if (pos > pos + vPC[2].u.operand)
                        loop[pos + vPC[2].u.operand] = true;
                    else
                        loop[pos] = true;
                    break;
                case op_loop_if_less:
                case op_loop_if_lesseq:
                case op_loop_if_greater:
                case op_loop_if_greatereq:
                    if (pos > pos + vPC[3].u.operand)
                        loop[pos + vPC[3].u.operand] = true;
                    else
                        loop[pos] = true;
                    break;
                    
                default:
                    break;
            }
            
            vPC += length; // advance the length of the given opcode
        }
        
        // Initialize arrays
        
        semi = new int[count];
        memset(semi, 0, sizeof(int) * count);
        
        label = new int[count];
        memset(label, 0, sizeof(int) * count);
        
        vertex = new int[count];
        memset(vertex, 0, sizeof(int) * count);
        
        parent = new int[count];
        memset(parent, 0, sizeof(int) * count);
        
        ancestor = new int[count];
        memset(ancestor, 0, sizeof(int) * count);
        
        child = new int[count];
        memset(child, 0, sizeof(int) * count);
        
        size = new int[count];
        memset(size, 0, sizeof(int) * count);
        
    }
    
    void FlowGraph::add_edge(int from, int to) {
        // Swaped to make post-dominator
        //edges[from].successor.append(to);
        
        edges[to].successor.append(from);
    }
    
    void FlowGraph::dfs() {
        n = 1;
        // Going in reverse to make post-dominator
        dfs(count - 1);
    }
    
    
    void FlowGraph::dfs(int v) {
        vertex[n] = label[v] = v;
        semi[v] = n++;
        ancestor[v] = child[v] = 0;
        size[v] = 1;
        for (size_t i = 0; i < edges[v].successor.size(); i++) {
            int w = edges[v].successor.at(i);
            if(semi[w] == 0) {
                parent[w] = v;
                dfs(w);
            }
            edges[w].predecessor.append(v);
        }
        
        //        for (int w : edges[v].successor) {
        //            if(semi[w] == 0) {
        //                parent[w] = v;
        //                dfs(w);
        //            }
        //            edges[w].predecessor.append(v);
        //        }
    }
    
    
    //    void FlowGraph::dump_tree() {
    //        printf("\nCFG has\n");
    //        for(int i = 0; i < count; i++ ) {
    //            printf("%d:\t", i);
    //            for(int w : edges[i].successor) {
    //                printf("%d ", w);
    //            }
    //            printf("\n");
    //        }
    //
    //        printf("\n");
    //    }
    
    
    void FlowGraph::dump_tree() {
        printf("\nCFG has\n");
        
        for(int i = 0; i < count; i++ ) {
            // Abhi - Changing to depict the CFG edges -- Included it inside the for loop
            //            printf("%d:\t", i);
            for(size_t w = 0; w < edges[i].successor.size(); w++) {
                printf("%d:\t%d \n", i, edges[i].successor.at(w));
            }
            //            printf("\n"); //Abhi - Inside for loop
        }
        
        printf("\n");
    }
    
    
    void FlowGraph::dump_vertex() {
        printf("vertex has\n");
        for (int i=1; i< n ; i++) {
            printf("%d:\t%d\n", i, vertex[i]);
        }  
    }
    
    
    void FlowGraph::dump_semi() {
        printf("semi has\n");
        for (int i=0; i<count; i++) {
            if (semi[i]) printf("%d\t%d\n", i, semi[i]);
        }
    }
    
    bool FlowGraph::checkLoop(CodeBlock* codeBlock, Interpreter* interpreter, int pos, int idom)
    {
        // Set contains loop
        Instruction* begin = codeBlock->instructions().begin();
        Instruction* vPC;
        Instruction* end;
        if (pos <= idom) {
            vPC = begin + pos;
            end = begin + idom;
        }
        else {
            vPC = begin + idom;
            end = begin + pos;
        }
        // Get number of instructions
        count = (int) (codeBlock->instructions().end() - codeBlock->instructions().begin()) + 1;
        
        int opcode = interpreter->getOpcodeID(vPC->u.opcode);
        int length = opcodeLengths[opcode];
        switch (opcode) {
            case op_jmp:
            case op_jtrue:
            case op_jfalse:
            case op_jempty:
            case op_jeq_null:
            case op_jneq_null:
            case op_jneq_ptr:
            case op_jnless:
            case op_jless:
            case op_jnlesseq:
            case op_jlesseq:
            case op_jgreater:
            case op_jgreatereq:
            case op_jngreater:
            case op_jngreatereq:
                while (vPC < end) {
                    int opcode = interpreter->getOpcodeID(vPC->u.opcode);
                    int pos = (long) (vPC-begin);
                    int length = opcodeLengths[opcode];
                    
                    switch (opcode) {
                        case op_loop:
                        case op_loop_if_true:
                        case op_loop_if_false:
                        case op_loop_if_less:
                        case op_loop_if_lesseq:
                        case op_loop_if_greater:
                        case op_loop_if_greatereq:
                            return true;
                        default:
                            break;
                    }
                    vPC += length;
                }
                break;
            default:
                break;
        }
        return false;
    }

}

