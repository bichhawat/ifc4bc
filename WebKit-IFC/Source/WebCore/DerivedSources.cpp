/*
 * Copyright (C) 2008 Apple Inc. All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY APPLE INC. ``AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL APPLE INC. OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY
 * OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. 
 */

// This all-in-one cpp file cuts down on template bloat to allow us to build our Windows release build.

#include "HTMLElementFactory.cpp"
#include "HTMLEntityTable.cpp"
#include "JSAbstractWorker.cpp"
#include "JSArrayBuffer.cpp"
#include "JSArrayBufferView.cpp"
#include "JSAttr.cpp"
#include "JSBarInfo.cpp"
#include "JSBeforeLoadEvent.cpp"
#include "JSBlob.cpp"
#include "JSCanvasGradient.cpp"
#include "JSCanvasPattern.cpp"
#include "JSCanvasRenderingContext.cpp"
#include "JSCanvasRenderingContext2D.cpp"
#if ENABLE(WEBGL)    
#include "JSWebGLRenderingContext.cpp"
#endif
#include "JSCDATASection.cpp"
#include "JSCharacterData.cpp"
#include "JSClientRect.cpp"
#include "JSClientRectList.cpp"
#include "JSClipboard.cpp"
#include "JSCloseEvent.cpp"
#include "JSComment.cpp"
#include "JSCompositionEvent.cpp"
#include "JSConsole.cpp"
#include "JSCoordinates.cpp"
#include "JSCounter.cpp"
#include "JSCrypto.cpp"
#include "JSCSSCharsetRule.cpp"
#include "JSCSSFontFaceRule.cpp"
#include "JSCSSImportRule.cpp"
#include "JSCSSMediaRule.cpp"
#include "JSCSSPageRule.cpp"
#include "JSCSSPrimitiveValue.cpp"
#include "JSCSSRule.cpp"
#include "JSCSSRuleList.cpp"
#include "JSCSSStyleDeclaration.cpp"
#include "JSCSSStyleRule.cpp"
#include "JSCSSStyleSheet.cpp"
#include "JSCSSValue.cpp"
#include "JSCSSValueList.cpp"
#include "JSCustomEvent.cpp"
#include "JSDatabase.cpp"
#include "JSDatabaseCallback.cpp"
#include "JSDatabaseSync.cpp"
#include "JSDataTransferItem.cpp"
#include "JSDataTransferItemList.cpp"
#include "JSDataView.cpp"
#include "JSDedicatedWorkerContext.cpp"
#include "JSDeviceOrientationEvent.cpp"
#include "JSDirectoryEntry.cpp"
#include "JSDirectoryEntrySync.cpp"
#include "JSDirectoryReader.cpp"
#include "JSDirectoryReaderSync.cpp"
#include "JSDocument.cpp"
#include "JSDocumentFragment.cpp"
#include "JSDocumentType.cpp"
#include "JSDOMApplicationCache.cpp"
#include "JSDOMCoreException.cpp"
#include "JSDOMError.cpp"
#include "JSDOMFileSystem.cpp"
#include "JSDOMFileSystemSync.cpp"
#include "JSDOMFormData.cpp"
#include "JSDOMImplementation.cpp"
#include "JSDOMMimeType.cpp"
#include "JSDOMMimeTypeArray.cpp"
#include "JSDOMParser.cpp"
#include "JSDOMPlugin.cpp"
#include "JSDOMPluginArray.cpp"
#include "JSDOMSelection.cpp"
#include "JSDOMSettableTokenList.cpp"
#include "JSDOMStringList.cpp"
#include "JSDOMStringMap.cpp"
#include "JSDOMTokenList.cpp"
#include "JSDOMURL.cpp"
#include "JSDOMWindow.cpp"
#include "JSElement.cpp"
#include "JSEntity.cpp"
#include "JSEntityReference.cpp"
#include "JSEntriesCallback.cpp"
#include "JSEntry.cpp"
#include "JSEntryArray.cpp"
#include "JSEntryArraySync.cpp"
#include "JSEntrySync.cpp"
#include "JSEntryCallback.cpp"
#include "JSErrorCallback.cpp"
#include "JSErrorEvent.cpp"
#include "JSEvent.cpp"
#include "JSEventException.cpp"
#include "JSEventSource.cpp"
#include "JSFile.cpp"
#include "JSFileCallback.cpp"
#include "JSFileEntry.cpp"
#include "JSFileEntrySync.cpp"
#include "JSFileError.cpp"
#include "JSFileException.cpp"
#include "JSFileList.cpp"
#include "JSFileReader.cpp"
#include "JSFileReaderSync.cpp"
#include "JSFileSystemCallback.cpp"
#include "JSFileWriter.cpp"
#include "JSFileWriterCallback.cpp"
#include "JSFileWriterSync.cpp"
#include "JSFloat32Array.cpp"
#include "JSFloat64Array.cpp"
#include "JSGeolocation.cpp"
#include "JSGeoposition.cpp"
#include "JSHashChangeEvent.cpp"
#include "JSHistory.cpp"
#include "JSHTMLAllCollection.cpp"
#include "JSHTMLPropertiesCollection.cpp"
#include "JSHTMLAnchorElement.cpp"
#include "JSHTMLAppletElement.cpp"
#include "JSHTMLAreaElement.cpp"
#include "JSHTMLAudioElement.cpp"
#include "JSHTMLBaseElement.cpp"
#include "JSHTMLBaseFontElement.cpp"
#include "JSHTMLBodyElement.cpp"
#include "JSHTMLBRElement.cpp"
#include "JSHTMLButtonElement.cpp"
#include "JSHTMLCanvasElement.cpp"
#include "JSHTMLCollection.cpp"
#include "JSHTMLContentElement.cpp"
#include "JSHTMLDataListElement.cpp"
#include "JSHTMLDetailsElement.cpp"
#include "JSHTMLDirectoryElement.cpp"
#include "JSHTMLDivElement.cpp"
#include "JSHTMLDListElement.cpp"
#include "JSHTMLDocument.cpp"
#include "JSHTMLElement.cpp"
#include "JSHTMLElementWrapperFactory.cpp"
#include "JSHTMLEmbedElement.cpp"
#include "JSHTMLFieldSetElement.cpp"
#include "JSHTMLFontElement.cpp"
#include "JSHTMLFormElement.cpp"
#include "JSHTMLFrameElement.cpp"
#include "JSHTMLFrameSetElement.cpp"
#include "JSHTMLHeadElement.cpp"
#include "JSHTMLHeadingElement.cpp"
#include "JSHTMLHRElement.cpp"
#include "JSHTMLHtmlElement.cpp"
#include "JSHTMLIFrameElement.cpp"
#include "JSHTMLImageElement.cpp"
#include "JSHTMLInputElement.cpp"
#include "JSHTMLKeygenElement.cpp"
#include "JSHTMLLabelElement.cpp"
#include "JSHTMLLegendElement.cpp"
#include "JSHTMLLIElement.cpp"
#include "JSHTMLLinkElement.cpp"
#include "JSHTMLMapElement.cpp"
#include "JSHTMLMarqueeElement.cpp"
#include "JSHTMLMediaElement.cpp"
#include "JSHTMLMenuElement.cpp"
#include "JSHTMLMetaElement.cpp"
#include "JSHTMLMeterElement.cpp"
#include "JSHTMLModElement.cpp"
#include "JSHTMLObjectElement.cpp"
#include "JSHTMLOListElement.cpp"
#include "JSHTMLOptGroupElement.cpp"
#include "JSHTMLOptionElement.cpp"
#include "JSHTMLOptionsCollection.cpp"
#include "JSHTMLOutputElement.cpp"
#include "JSHTMLParagraphElement.cpp"
#include "JSHTMLParamElement.cpp"
#include "JSHTMLPreElement.cpp"
#include "JSHTMLProgressElement.cpp"
#include "JSHTMLQuoteElement.cpp"
#include "JSHTMLScriptElement.cpp"
#include "JSHTMLSelectElement.cpp"
#if ENABLE(SHADOW_DOM)
#include "JSHTMLShadowElement.cpp"
#endif
#include "JSHTMLSourceElement.cpp"
#include "JSHTMLSpanElement.cpp"
#include "JSHTMLStyleElement.cpp"
#include "JSHTMLTableCaptionElement.cpp"
#include "JSHTMLTableCellElement.cpp"
#include "JSHTMLTableColElement.cpp"
#include "JSHTMLTableElement.cpp"
#include "JSHTMLTableRowElement.cpp"
#include "JSHTMLTableSectionElement.cpp"
#include "JSHTMLTextAreaElement.cpp"
#include "JSHTMLTitleElement.cpp"
#include "JSHTMLUnknownElement.cpp"
#include "JSHTMLUListElement.cpp"
#include "JSHTMLVideoElement.cpp"
#include "JSIDBAny.cpp"
#include "JSIDBCursor.cpp"
#include "JSIDBDatabase.cpp"
#include "JSIDBDatabaseException.cpp"
#include "JSIDBFactory.cpp"
#include "JSIDBIndex.cpp"
#include "JSIDBKey.cpp"
#include "JSIDBKeyRange.cpp"
#include "JSIDBObjectStore.cpp"
#include "JSIDBRequest.cpp"
#include "JSIDBTransaction.cpp"
#include "JSImageData.cpp"
#include "JSInjectedScriptHost.cpp"
#include "JSInspectorFrontendHost.cpp"
#include "JSInt16Array.cpp"
#include "JSInt32Array.cpp"
#include "JSInt8Array.cpp"
#include "JSJavaScriptCallFrame.cpp"
#include "JSKeyboardEvent.cpp"
#include "JSLocation.cpp"
#include "JSMediaController.cpp"
#include "JSMediaError.cpp"
#include "JSMediaList.cpp"
#include "JSMediaQueryList.cpp"
#include "JSMemoryInfo.cpp"
#include "JSMessageChannel.cpp"
#include "JSMessageEvent.cpp"
#include "JSMessagePort.cpp"
#include "JSMetadata.cpp"
#include "JSMetadataCallback.cpp"
#include "JSMouseEvent.cpp"
#include "JSMutationCallback.cpp"
#include "JSMutationEvent.cpp"
#include "JSMutationObserver.cpp"
#include "JSMutationRecord.cpp"
#include "JSNamedNodeMap.cpp"
#include "JSNavigator.cpp"
#include "JSNode.cpp"
#include "JSNodeFilter.cpp"
#include "JSNodeIterator.cpp"
#include "JSNodeList.cpp"
#include "JSNotation.cpp"
#include "JSNotificationCenter.cpp"
#include "JSNotification.cpp"
#include "JSOverflowEvent.cpp"
#include "JSPageTransitionEvent.cpp"
#include "JSPerformance.cpp"
#include "JSPerformanceNavigation.cpp"
#include "JSPerformanceTiming.cpp"
#include "JSPopStateEvent.cpp"
#include "JSPositionCallback.cpp"
#include "JSPositionError.cpp"
#include "JSPositionErrorCallback.cpp"
#include "JSProcessingInstruction.cpp"
#include "JSProgressEvent.cpp"
#include "JSRadioNodeList.cpp"
#include "JSRange.cpp"
#include "JSRangeException.cpp"
#include "JSRect.cpp"
#include "JSRequestAnimationFrameCallback.cpp"
#include "JSRGBColor.cpp"
#include "JSScreen.cpp"
#include "JSScriptProfile.cpp"
#include "JSScriptProfileNode.cpp"
#include "JSShadowRoot.cpp"
#include "JSSharedWorker.cpp"
#include "JSSharedWorkerContext.cpp"
#include "JSSQLError.cpp"
#include "JSSQLException.cpp"
#include "JSSQLResultSet.cpp"
#include "JSSQLResultSetRowList.cpp"
#include "JSSQLStatementCallback.cpp"
#include "JSSQLStatementErrorCallback.cpp"
#include "JSSQLTransaction.cpp"
#include "JSSQLTransactionCallback.cpp"
#include "JSSQLTransactionErrorCallback.cpp"
#include "JSSQLTransactionSync.cpp"
#include "JSSQLTransactionSyncCallback.cpp"
#include "JSStorage.cpp"
#include "JSStorageEvent.cpp"
#include "JSStorageInfo.cpp"
#include "JSStorageInfoErrorCallback.cpp"
#include "JSStorageInfoQuotaCallback.cpp"
#include "JSStorageInfoUsageCallback.cpp"
#include "JSStringCallback.cpp"
#include "JSStyleMedia.cpp"
#include "JSStyleSheet.cpp"
#include "JSStyleSheetList.cpp"
#include "JSSVGAElement.cpp"
#include "JSSVGAltGlyphDefElement.cpp"
#include "JSSVGAltGlyphElement.cpp"
#include "JSSVGAltGlyphItemElement.cpp"
#include "JSSVGAngle.cpp"
#include "JSSVGAnimateColorElement.cpp"
#include "JSSVGAnimatedAngle.cpp"
#include "JSSVGAnimatedBoolean.cpp"
#include "JSSVGAnimatedEnumeration.cpp"
#include "JSSVGAnimatedInteger.cpp"
#include "JSSVGAnimatedLength.cpp"
#include "JSSVGAnimatedLengthList.cpp"
#include "JSSVGAnimatedNumber.cpp"
#include "JSSVGAnimatedNumberList.cpp"
#include "JSSVGAnimatedPreserveAspectRatio.cpp"
#include "JSSVGAnimatedRect.cpp"
#include "JSSVGAnimatedString.cpp"
#include "JSSVGAnimatedTransformList.cpp"
#include "JSSVGAnimateElement.cpp"
#include "JSSVGAnimateMotionElement.cpp"
#include "JSSVGAnimateTransformElement.cpp"
#include "JSSVGAnimationElement.cpp"
#include "JSSVGCircleElement.cpp"
#include "JSSVGClipPathElement.cpp"
#include "JSSVGColor.cpp"
#include "JSSVGComponentTransferFunctionElement.cpp"
#include "JSSVGCursorElement.cpp"
#include "JSSVGDefsElement.cpp"
#include "JSSVGDescElement.cpp"
#include "JSSVGDocument.cpp"
#include "JSSVGElement.cpp"
#include "JSSVGElementInstance.cpp"
#include "JSSVGElementInstanceList.cpp"
#include "JSSVGEllipseElement.cpp"
#include "JSSVGException.cpp"
#include "JSSVGFEBlendElement.cpp"
#include "JSSVGFEColorMatrixElement.cpp"
#include "JSSVGFEComponentTransferElement.cpp"
#include "JSSVGFECompositeElement.cpp"
#include "JSSVGFEConvolveMatrixElement.cpp"
#include "JSSVGFEDiffuseLightingElement.cpp"
#include "JSSVGFEDisplacementMapElement.cpp"
#include "JSSVGFEDistantLightElement.cpp"
#include "JSSVGFEDropShadowElement.cpp"
#include "JSSVGFEFloodElement.cpp"
#include "JSSVGFEFuncAElement.cpp"
#include "JSSVGFEFuncBElement.cpp"
#include "JSSVGFEFuncGElement.cpp"
#include "JSSVGFEFuncRElement.cpp"
#include "JSSVGFEGaussianBlurElement.cpp"
#include "JSSVGFEImageElement.cpp"
#include "JSSVGFEMergeElement.cpp"
#include "JSSVGFEMergeNodeElement.cpp"
#include "JSSVGFEMorphologyElement.cpp"
#include "JSSVGFEOffsetElement.cpp"
#include "JSSVGFEPointLightElement.cpp"
#include "JSSVGFESpecularLightingElement.cpp"
#include "JSSVGFESpotLightElement.cpp"
#include "JSSVGFETileElement.cpp"
#include "JSSVGFETurbulenceElement.cpp"
#include "JSSVGFilterElement.cpp"
#include "JSSVGFontElement.cpp"
#include "JSSVGFontFaceElement.cpp"
#include "JSSVGFontFaceFormatElement.cpp"
#include "JSSVGFontFaceNameElement.cpp"
#include "JSSVGFontFaceSrcElement.cpp"
#include "JSSVGFontFaceUriElement.cpp"
#include "JSSVGForeignObjectElement.cpp"
#include "JSSVGGElement.cpp"
#include "JSSVGGlyphElement.cpp"
#include "JSSVGGlyphRefElement.cpp"
#include "JSSVGGradientElement.cpp"
#include "JSSVGHKernElement.cpp"
#include "JSSVGImageElement.cpp"
#include "JSSVGLength.cpp"
#include "JSSVGLengthList.cpp"
#include "JSSVGLinearGradientElement.cpp"
#include "JSSVGLineElement.cpp"
#include "JSSVGMPathElement.cpp"
#include "JSSVGMarkerElement.cpp"
#include "JSSVGMaskElement.cpp"
#include "JSSVGMatrix.cpp"
#include "JSSVGMetadataElement.cpp"
#include "JSSVGMissingGlyphElement.cpp"
#include "JSSVGNumber.cpp"
#include "JSSVGNumberList.cpp"
#include "JSSVGPaint.cpp"
#include "JSSVGPathElement.cpp"
#include "JSSVGPathSeg.cpp"
#include "JSSVGPathSegArcAbs.cpp"
#include "JSSVGPathSegArcRel.cpp"
#include "JSSVGPathSegClosePath.cpp"
#include "JSSVGPathSegCurvetoCubicAbs.cpp"
#include "JSSVGPathSegCurvetoCubicRel.cpp"
#include "JSSVGPathSegCurvetoCubicSmoothAbs.cpp"
#include "JSSVGPathSegCurvetoCubicSmoothRel.cpp"
#include "JSSVGPathSegCurvetoQuadraticAbs.cpp"
#include "JSSVGPathSegCurvetoQuadraticRel.cpp"
#include "JSSVGPathSegCurvetoQuadraticSmoothAbs.cpp"
#include "JSSVGPathSegCurvetoQuadraticSmoothRel.cpp"
#include "JSSVGPathSegLinetoAbs.cpp"
#include "JSSVGPathSegLinetoHorizontalAbs.cpp"
#include "JSSVGPathSegLinetoHorizontalRel.cpp"
#include "JSSVGPathSegLinetoRel.cpp"
#include "JSSVGPathSegLinetoVerticalAbs.cpp"
#include "JSSVGPathSegLinetoVerticalRel.cpp"
#include "JSSVGPathSegList.cpp"
#include "JSSVGPathSegMovetoAbs.cpp"
#include "JSSVGPathSegMovetoRel.cpp"
#include "JSSVGPatternElement.cpp"
#include "JSSVGPoint.cpp"
#include "JSSVGPointList.cpp"
#include "JSSVGPolygonElement.cpp"
#include "JSSVGPolylineElement.cpp"
#include "JSSVGPreserveAspectRatio.cpp"
#include "JSSVGRadialGradientElement.cpp"
#include "JSSVGRect.cpp"
#include "JSSVGRectElement.cpp"
#include "JSSVGRenderingIntent.cpp"
#include "JSSVGScriptElement.cpp"
#include "JSSVGSetElement.cpp"
#include "JSSVGStopElement.cpp"
#include "JSSVGStringList.cpp"
#include "JSSVGStyleElement.cpp"
#include "JSSVGSVGElement.cpp"
#include "JSSVGSwitchElement.cpp"
#include "JSSVGSymbolElement.cpp"
#include "JSSVGTextContentElement.cpp"
#include "JSSVGTextElement.cpp"
#include "JSSVGTextPathElement.cpp"
#include "JSSVGTextPositioningElement.cpp"
#include "JSSVGTitleElement.cpp"
#include "JSSVGTransform.cpp"
#include "JSSVGTransformList.cpp"
#include "JSSVGTRefElement.cpp"
#include "JSSVGTSpanElement.cpp"
#include "JSSVGUnitTypes.cpp"
#include "JSSVGUseElement.cpp"
#include "JSSVGVKernElement.cpp"
#include "JSSVGViewElement.cpp"
#include "JSSVGViewSpec.cpp"
#include "JSSVGZoomAndPan.cpp"
#include "JSSVGZoomEvent.cpp"
#include "JSText.cpp"
#include "JSTextEvent.cpp"
#include "JSTextMetrics.cpp"
#if ENABLE(VIDEO_TRACK)
#include "JSTextTrack.cpp"
#include "JSTextTrackCue.cpp"
#include "JSTextTrackCueList.cpp"
#include "JSTextTrackList.cpp"
#include "JSTrackEvent.cpp"
#endif
#include "JSTimeRanges.cpp"
#include "JSTouch.cpp"
#include "JSTouchEvent.cpp"
#include "JSTouchList.cpp"
#include "JSTreeWalker.cpp"
#include "JSUint16Array.cpp"
#include "JSUint32Array.cpp"
#include "JSUint8Array.cpp"
#include "JSUint8ClampedArray.cpp"
#include "JSUIEvent.cpp"
#if ENABLE(UNDO_MANAGER)
#include "JSUndoManager.cpp"
#endif
#include "JSValidityState.cpp"
#include "JSWebKitAnimation.cpp"
#include "JSWebKitAnimationEvent.cpp"
#include "JSWebKitAnimationList.cpp"
#include "JSWebKitBlobBuilder.cpp"
#if ENABLE(CSS_FILTERS)
#include "JSWebKitCSSFilterValue.cpp"
#endif
#include "JSWebKitCSSKeyframeRule.cpp"
#include "JSWebKitCSSKeyframesRule.cpp"
#include "JSWebKitCSSTransformValue.cpp"
#include "JSWebKitCSSMatrix.cpp"
#include "JSWebKitCSSRegionRule.cpp"
#include "JSWebKitNamedFlow.cpp"
#include "JSWebKitPoint.cpp"
#include "JSWebKitTransitionEvent.cpp"
#include "JSWebSocket.cpp"
#include "JSWheelEvent.cpp"
#include "JSWorker.cpp"
#include "JSWorkerContext.cpp"
#include "JSWorkerLocation.cpp"
#include "JSWorkerNavigator.cpp"
#include "JSXMLHttpRequest.cpp"
#include "JSXMLHttpRequestException.cpp"
#include "JSXMLHttpRequestProgressEvent.cpp"
#include "JSXMLHttpRequestUpload.cpp"
#include "JSXMLSerializer.cpp"
#include "JSXPathEvaluator.cpp"
#include "JSXPathException.cpp"
#include "JSXPathExpression.cpp"
#include "JSXPathNSResolver.cpp"
#include "JSXPathResult.cpp"
#include "JSXSLTProcessor.cpp"
#include "UserAgentStyleSheetsData.cpp"

// On MSVC, including StaticConstructors.h causes all global objects not to be
// automatically initialized by the C runtime. This is useful in some specific
// cases (e.g., the *Names.cpp files), but can be dangerous in others. We don't
// want StaticConstructors.h to "pollute" all the source files we #include here
// accidentally, so we'll throw an error whenever any file includes it.
#ifdef StaticConstructors_h
#error Do not include any file in DerivedSources.cpp that includes StaticConstructors.h
#endif
