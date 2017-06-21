/*
 * Copyright (C) 1999 Lars Knoll (knoll@kde.org)
 *           (C) 1999 Antti Koivisto (koivisto@kde.org)
 *           (C) 2001 Dirk Mueller (mueller@kde.org)
 * Copyright (C) 2004, 2006, 2007, 2008, 2010 Apple Inc. All rights reserved.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Library General Public License for more details.
 *
 * You should have received a copy of the GNU Library General Public License
 * along with this library; see the file COPYING.LIB.  If not, write to
 * the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
 * Boston, MA 02110-1301, USA.
 */

#include "config.h"
#include "DynamicNodeList.h"

#include "Document.h"
#include "Element.h"

namespace WebCore {

DynamicSubtreeNodeList::~DynamicSubtreeNodeList()
{
}

unsigned DynamicSubtreeNodeList::length() const
{
    JSC::JSLabel listLabel = JSC::JSLabel();
    if (isLengthCacheValid()) {
        nodeListLabel = getListLengthLabel();
        listLabel = nodeListLabel;
//        if (!JSC::JSLabel(JSC::JSLabel::pcGlobalLabel).NSU(listLabel)) {
//            JSC::JSLabel::ABORT_FLAG = true;
//            printf("Accessing child nodes list length in a different pc\n");
//            // return -1;
//        }
        return cachedLength();
    }

    unsigned length = 0;
    Node* rootNode = this->rootNode();
    
    for (Node* n = rootNode->firstChild(); n; n = n->traverseNextNode(rootNode))
    {
        length += n->isElementNode() && nodeMatches(static_cast<Element*>(n));
        // IFC4BC - Join the next pointer label
        listLabel = listLabel.Join(n->getNodeLabel().Join(n->getNextSiblingLabel()).Join(n->getFCLabel()));
    }
    // IFC4BC - Reading lists should not terminate the execution. return the label
//    if (!JSC::JSLabel(JSC::JSLabel::pcGlobalLabel).NSU(listLabel)) {
//        JSC::JSLabel::ABORT_FLAG = true;
//        printf("Accessing child nodes list length in a different pc\n");
//        // return -1;
//    }
    nodeListLabel = listLabel;
    
    setLengthCache(length, listLabel);

    return length;
}

Node* DynamicSubtreeNodeList::itemForwardsFromCurrent(Node* start, unsigned offset, int remainingOffset) const
{
    JSC::JSLabel listLabel = JSC::JSLabel();
    ASSERT(remainingOffset >= 0);
    Node* rootNode = this->rootNode();
    for (Node* n = start; n; n = n->traverseNextNode(rootNode)) {
        // IFC4BC - join the next pointer label
        listLabel = listLabel.Join(n->getNodeLabel().Join(n->getNextSiblingLabel()).Join(n->getFCLabel()));
        if (n->isElementNode() && nodeMatches(static_cast<Element*>(n))) {
            if (!remainingOffset) {
                setItemCache(n, offset, listLabel);
                // IFC4BC - get the complete label for a cached item
                if (start == cachedItem())
                    nodeListLabel = nodeListLabel.Join(listLabel);
                else
                    nodeListLabel = listLabel;
                return n;
            }
            --remainingOffset;
        }
    }

    return 0; // no matching node in this subtree
}

Node* DynamicSubtreeNodeList::itemBackwardsFromCurrent(Node* start, unsigned offset, int remainingOffset) const
{
    JSC::JSLabel listLabel = JSC::JSLabel();
    ASSERT(remainingOffset < 0);
    Node* rootNode = this->rootNode();
    for (Node* n = start; n; n = n->traversePreviousNode(rootNode)) {
        // IFC4BC - join the pointer label
        listLabel = listLabel.Join(n->getNodeLabel().Join(n->getPrevSiblingLabel()).Join(n->getLCLabel()));
        if (n->isElementNode() && nodeMatches(static_cast<Element*>(n))) {
            if (!remainingOffset) {
                setItemCache(n, offset, listLabel);
                // IFC4BC - get the complete label for item relative to cached item
                if (start == cachedItem())
                    nodeListLabel = nodeListLabel.Join(listLabel);
                else
                    nodeListLabel = listLabel;
                return n;
            }
            ++remainingOffset;
        }
    }

    return 0; // no matching node in this subtree
}

Node* DynamicSubtreeNodeList::item(unsigned offset) const
{
    int remainingOffset = offset;
    Node* start = rootNode()->firstChild();
    if (isItemCacheValid()) {
        if (offset == cachedItemOffset())
        {
            // IFC4BC - get the cached item label
            nodeListLabel = getItemLabel();
//            if (!JSC::JSLabel(JSC::JSLabel::pcGlobalLabel).NSU(nodeListLabel)) {
//                JSC::JSLabel::ABORT_FLAG = true;
//                printf("Accessing child nodes list item in a different pc\n");
//                // return 0;
//            }
            return cachedItem();
        }
        if (offset > cachedItemOffset() || cachedItemOffset() - offset < offset) {
            start = cachedItem();
            // IFC4BC - set the label for cached item
            nodeListLabel = getItemLabel();
            remainingOffset -= cachedItemOffset();
        }
    }
    Node* returnNode;
    
    if (remainingOffset < 0)
        returnNode = itemBackwardsFromCurrent(start, offset, remainingOffset);
    else
        returnNode = itemForwardsFromCurrent(start, offset, remainingOffset);
    
//    if (!JSC::JSLabel(JSC::JSLabel::pcGlobalLabel).NSU(nodeListLabel)) {
//        JSC::JSLabel::ABORT_FLAG = true;
//        printf("Accessing child nodes list item in a different pc\n");
//        // return 0;
//    }
    
    return returnNode;
}

Node* DynamicNodeList::itemWithName(const AtomicString& elementId) const
{
    Node* rootNode = this->rootNode();

    if (rootNode->inDocument()) {
        Element* element = rootNode->treeScope()->getElementById(elementId);
        if (element && nodeMatches(element) && element->isDescendantOf(rootNode))
            return element;
        if (!element)
            return 0;
        // In the case of multiple nodes with the same name, just fall through.
    }

    unsigned length = this->length();
    for (unsigned i = 0; i < length; i++) {
        Node* node = item(i);
        // FIXME: This should probably be using getIdAttribute instead of idForStyleResolution.
        if (node->hasID() && static_cast<Element*>(node)->idForStyleResolution() == elementId)
            return node;
    }

    return 0;
}

} // namespace WebCore
