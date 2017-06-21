/*
 * Copyright (C) 1999 Lars Knoll (knoll@kde.org)
 *           (C) 1999 Antti Koivisto (koivisto@kde.org)
 *           (C) 2001 Dirk Mueller (mueller@kde.org)
 * Copyright (C) 2003, 2004, 2005, 2006, 2007, 2008 Apple Inc. All rights reserved.
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
#include "HTMLScriptElement.h"

#include "Attribute.h"
#include "Document.h"
#include "Event.h"
#include "EventNames.h"
#include "HTMLNames.h"
#include "ScriptEventListener.h"
#include "Text.h"

namespace WebCore {

using namespace HTMLNames;

inline HTMLScriptElement::HTMLScriptElement(const QualifiedName& tagName, Document* document, bool wasInsertedByParser, bool alreadyStarted)
    : HTMLElement(tagName, document)
    , ScriptElement(this, wasInsertedByParser, alreadyStarted)
{
    ASSERT(hasTagName(scriptTag));
}

PassRefPtr<HTMLScriptElement> HTMLScriptElement::create(const QualifiedName& tagName, Document* document, bool wasInsertedByParser, bool alreadyStarted)
{
    return adoptRef(new HTMLScriptElement(tagName, document, wasInsertedByParser, alreadyStarted));
}

bool HTMLScriptElement::isURLAttribute(const Attribute& attribute) const
{
    return attribute.name() == srcAttr || HTMLElement::isURLAttribute(attribute);
}

void HTMLScriptElement::childrenChanged(bool changedByParser, Node* beforeChange, Node* afterChange, int childCountDelta)
{
    HTMLElement::childrenChanged(changedByParser, beforeChange, afterChange, childCountDelta);
    ScriptElement::childrenChanged();
}

void HTMLScriptElement::parseAttribute(const Attribute& attribute)
{
    if (attribute.name() == srcAttr)
    {
        // IFC4BC - Checking for policy and adding it to the map
        KURL scriptSrc = document()->completeURL(attribute.value().string());
        bool isPolicy = false;
    
        if (strstr(scriptSrc.string().utf8().data(), ".policy"))
        {
            char* scriptDom = new char[strlen(scriptSrc.string().utf8().data())];
            if (strncmp(scriptSrc.string().utf8().data(), "http:", 5) == 0)
            {
                sscanf(scriptSrc.string().utf8().data(), "http://%[^/]", scriptDom);
            }
            else if (strncmp(scriptSrc.string().utf8().data(), "https", 5) == 0)
            {
                sscanf(scriptSrc.string().utf8().data(), "https://%[^/]", scriptDom);
            }
            else if (strncmp(scriptSrc.string().utf8().data(), "file:", 5) == 0)
            {
                sscanf(scriptSrc.string().utf8().data(), "file:///%[^/]", scriptDom);
            }
            else
            {
                strcpy(scriptDom, scriptSrc.string().utf8().data());
            }
            
            char* domain = new char[strlen(document()->documentURI().utf8().data())];
            if (strncmp(document()->documentURI().utf8().data(), "http:", 5) == 0)
            {
                sscanf(document()->documentURI().utf8().data(), "http://%[^/]", domain);
            }
            else if (strncmp(document()->documentURI().utf8().data(), "https", 5) == 0)
            {
                sscanf(document()->documentURI().utf8().data(), "https://%[^/]", domain);
            }
            else if (strncmp(document()->documentURI().utf8().data(), "file:", 5) == 0)
            {
                sscanf(document()->documentURI().utf8().data(), "file:///%[^/]", domain);
            }
            else
            {
                strcpy(domain, document()->documentURI().utf8().data());
            }
            
            // printf ("The source domain is %s\n", scriptDom);
            // printf ("The script domain is %s\n", domain);
            if (strcmp(domain, scriptDom) == 0) {
                isPolicy = true;
            }
        }
        JSC::URLMap::urlmap().put(scriptSrc.string().utf8().data(), isPolicy);
        // ----------------------- 
        handleSourceAttribute(attribute.value());
    }
    else if (attribute.name() == asyncAttr)
        handleAsyncAttribute();
    else if (attribute.name() == onloadAttr)
        setAttributeEventListener(eventNames().loadEvent, createAttributeEventListener(this, attribute));
    else if (attribute.name() == onbeforeloadAttr)
        setAttributeEventListener(eventNames().beforeloadEvent, createAttributeEventListener(this, attribute));
    // IFC4BC - Setting the context for the script
    else if (strcmp(attribute.localName().string().utf8().data(), "setContext")==0)
    {
        JSC::URLMap::urlmap().put(attribute.value().string().utf8().data(), 0);
        JSC::JSLabel::pcGlobalLabel = JSC::URLMap::urlmap().getLabel(attribute.value().string().utf8().data()).getPair();
    }
    else
        HTMLElement::parseAttribute(attribute);
}

Node::InsertionNotificationRequest HTMLScriptElement::insertedInto(ContainerNode* insertionPoint)
{
    HTMLElement::insertedInto(insertionPoint);
    ScriptElement::insertedInto(insertionPoint);
    return InsertionDone;
}

void HTMLScriptElement::setText(const String &value)
{
    RefPtr<Node> protectFromMutationEvents(this);

    ExceptionCode ec = 0;
    int numChildren = childNodeCount();

    if (numChildren == 1 && firstChild()->isTextNode()) {
        toText(firstChild())->setData(value, ec);
        return;
    }

    if (numChildren > 0)
        removeChildren();

    appendChild(document()->createTextNode(value.impl()), ec);
}

void HTMLScriptElement::setAsync(bool async)
{
    setBooleanAttribute(asyncAttr, async);
    handleAsyncAttribute();
}

bool HTMLScriptElement::async() const
{
    return fastHasAttribute(asyncAttr) || forceAsync();
}

KURL HTMLScriptElement::src() const
{
    return document()->completeURL(sourceAttributeValue());
}

void HTMLScriptElement::addSubresourceAttributeURLs(ListHashSet<KURL>& urls) const
{
    HTMLElement::addSubresourceAttributeURLs(urls);

    addSubresourceURL(urls, src());
}

String HTMLScriptElement::sourceAttributeValue() const
{
    return getAttribute(srcAttr).string();
}

String HTMLScriptElement::charsetAttributeValue() const
{
    return getAttribute(charsetAttr).string();
}

String HTMLScriptElement::typeAttributeValue() const
{
    return getAttribute(typeAttr).string();
}

String HTMLScriptElement::languageAttributeValue() const
{
    return getAttribute(languageAttr).string();
}

String HTMLScriptElement::forAttributeValue() const
{
    return getAttribute(forAttr).string();
}

String HTMLScriptElement::eventAttributeValue() const
{
    return getAttribute(eventAttr).string();
}

bool HTMLScriptElement::asyncAttributeValue() const
{
    return fastHasAttribute(asyncAttr);
}

bool HTMLScriptElement::deferAttributeValue() const
{
    return fastHasAttribute(deferAttr);
}

bool HTMLScriptElement::hasSourceAttribute() const
{
    return fastHasAttribute(srcAttr);
}

void HTMLScriptElement::dispatchLoadEvent()
{
    ASSERT(!haveFiredLoadEvent());
    setHaveFiredLoadEvent(true);

    dispatchEvent(Event::create(eventNames().loadEvent, false, false));
}

PassRefPtr<Element> HTMLScriptElement::cloneElementWithoutAttributesAndChildren()
{
    return adoptRef(new HTMLScriptElement(tagQName(), document(), false, alreadyStarted()));
}

}
