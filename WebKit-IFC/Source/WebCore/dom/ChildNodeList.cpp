/**
 * Copyright (C) 1999 Lars Knoll (knoll@kde.org)
 *           (C) 1999 Antti Koivisto (koivisto@kde.org)
 *           (C) 2001 Dirk Mueller (mueller@kde.org)
 * Copyright (C) 2004, 2007, 2008 Apple Inc. All rights reserved.
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
#include "ChildNodeList.h"

#include "Element.h"

namespace WebCore {

ChildNodeList::ChildNodeList(PassRefPtr<Node> node)
    : DynamicNodeList(node, RootedAtNode, DoNotInvalidateOnAttributeChange)
{
}

ChildNodeList::~ChildNodeList()
{
    ownerNode()->removeCachedChildNodeList();
}

unsigned ChildNodeList::length() const
{
    // IFC4BC - Setting the list label
    Node* root = rootNode();
    JSC::JSLabel listLabel = root->getNodeLabel();
    if (isLengthCacheValid())
    {
        listLabel = getListLengthLabel();
        nodeListLabel = listLabel;
//        if (!JSC::JSLabel(JSC::JSLabel::pcGlobalLabel).NSU(listLabel)) {
//            JSC::JSLabel::ABORT_FLAG = true;
//            printf("Accessing child nodes list length in a different pc\n");
//            // return -1;
//        }
        return cachedLength();
    }
    
    unsigned len = 0;
    for (Node* n = root->firstChild(); n; n = n->nextSibling()) {
        len++;
        listLabel = listLabel.Join(root->getFCLabel());
        listLabel = listLabel.Join(n->getNodeLabel());
        listLabel = listLabel.Join(n->getNextSiblingLabel());
    }

//    if (!JSC::JSLabel(JSC::JSLabel::pcGlobalLabel).NSU(listLabel)) {
//        JSC::JSLabel::ABORT_FLAG = true;
//        printf("Accessing child nodes list length in a different pc\n");
//        // return -1;
//    }
    nodeListLabel = listLabel;
    
    setLengthCache(len, listLabel);

    return len;
}

Node* ChildNodeList::item(unsigned index) const
{
    unsigned int pos = 0;
    Node* root = rootNode();
    Node* n = root->firstChild();
    // IFC4BC - Setting the list label
    JSC::JSLabel listLabel = root->getNodeLabel().Join(n->getNodeLabel().Join(root->getFCLabel()));
    
    if (isItemCacheValid()) {
        listLabel = getItemLabel();
        if (index == cachedItemOffset())
        {
            // Do not need NSU checks here
//            if (!JSC::JSLabel(JSC::JSLabel::pcGlobalLabel).NSU(listLabel)) {
//                JSC::JSLabel::ABORT_FLAG = true;
//                printf("Accessing child node item in a different pc\n");
//                // return 0;
//            }
            return cachedItem();
        }

        int diff = index - cachedItemOffset();
        unsigned dist = abs(diff);
        if (dist < index) {
            n = cachedItem();
            pos = cachedItemOffset();
        }
    }

    if (isLengthCacheValid()) {
        if (index >= cachedLength())
            return 0;

        int diff = index - pos;
        unsigned dist = abs(diff);
        if (dist > cachedLength() - 1 - index) {
            n = root->lastChild();
            listLabel = listLabel.Join(root->getLCLabel());
            listLabel = listLabel.Join(n->getNodeLabel());
            pos = cachedLength() - 1;
        }
    }

    if (pos <= index) {
        while (n && pos < index) {
            listLabel = listLabel.Join(n->getNextSiblingLabel());
            n = n->nextSibling();
            listLabel = listLabel.Join(n->getNodeLabel());
            ++pos;
        }
    } else {
        while (n && pos > index) {
            listLabel = listLabel.Join(n->getPrevSiblingLabel());
            n = n->previousSibling();
            listLabel = listLabel.Join(n->getNodeLabel());
            --pos;
        }
    }

    if (n) {
        setItemCache(n, pos, listLabel);
        // We can return the label and copy it to the register
        // Do not need NSU check here
//        if (!JSC::JSLabel(JSC::JSLabel::pcGlobalLabel).NSU(listLabel)) {
//            JSC::JSLabel::ABORT_FLAG = true;
//            printf("Accessing node in a different pc\n");
//            // return 0;
//        }
        return n;
    }

    return 0;
}

bool ChildNodeList::nodeMatches(Element* testNode) const
{
    // Note: Due to the overrides of the length and item functions above,
    // this function will be called only by DynamicNodeList::itemWithName,
    // for an element that was located with getElementById.
    return testNode->parentNode() == rootNode();
}

} // namespace WebCore
