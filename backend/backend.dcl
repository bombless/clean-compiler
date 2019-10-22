definition module backend;

:: CPtr (:== Int);
:: *UWorld :== Int;
:: *BackEnd (:== CPtr);
:: BESymbolP (:== CPtr);
:: BETypeNodeP (:== CPtr);
:: BETypeArgP (:== CPtr);
:: BETypeAltP (:== CPtr);
:: BENodeP (:== CPtr);
:: BEArgP (:== CPtr);
:: BERuleAltP (:== CPtr);
:: BEImpRuleP (:== CPtr);
:: BEConstructorListP (:== CPtr);
:: BEFieldListP (:== CPtr);
:: BENodeIdP (:== CPtr);
:: BENodeDefP (:== CPtr);
:: BEStrictNodeIdP (:== CPtr);
:: BECodeParameterP (:== CPtr);
:: BECodeBlockP (:== CPtr);
:: BEStringListP (:== CPtr);
:: BENodeIdListP (:== CPtr);
:: BENodeIdRefCountListP (:== CPtr);
:: BEAnnotation :== Int;
:: BEAttribution :== Int;
:: BESymbKind :== Int;
:: BEArrayFunKind :== Int;
:: BESelectorKind :== Int;
:: BESpecialIdentIndex :== Int;
BEGetVersion :: (!Int,!Int,!Int);
// void BEGetVersion (int* current,int* oldestDefinition,int* oldestImplementation);
BEInit :: !Int !UWorld -> (!BackEnd,!UWorld);
// BackEnd BEInit (int argc);
BECloseFiles :: !BackEnd -> BackEnd;
// void BECloseFiles ();
BEFree :: !BackEnd !UWorld -> UWorld;
// void BEFree (BackEnd backEnd);
BEArg :: !String !BackEnd -> BackEnd;
// void BEArg (CleanString arg);
BEDeclareModules :: !Int !BackEnd -> BackEnd;
// void BEDeclareModules (int nModules);
BEBindSpecialModule :: !BESpecialIdentIndex !Int !BackEnd -> BackEnd;
// void BEBindSpecialModule (BESpecialIdentIndex index,int moduleIndex);
BEBindSpecialFunction :: !BESpecialIdentIndex !Int !Int !BackEnd -> BackEnd;
// void BEBindSpecialFunction (BESpecialIdentIndex index,int functionIndex,int moduleIndex);
BEBindSpecialType :: !Int !Int !Int !BackEnd -> BackEnd;
// void BEBindSpecialType (int special_type_n,int type_index,int module_index);
BESpecialArrayFunctionSymbol :: !BEArrayFunKind !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BESpecialArrayFunctionSymbol (BEArrayFunKind arrayFunKind,int functionIndex,int moduleIndex);
BEDictionarySelectFunSymbol :: !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEDictionarySelectFunSymbol ();
BEDictionaryUpdateFunSymbol :: !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEDictionaryUpdateFunSymbol ();
BEFunctionSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEFunctionSymbol (int functionIndex,int moduleIndex);
BEConstructorSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEConstructorSymbol (int constructorIndex,int moduleIndex);
BEFieldSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEFieldSymbol (int fieldIndex,int moduleIndex);
BETypeSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BETypeSymbol (int typeIndex,int moduleIndex);
BETypeSymbolNoMark :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BETypeSymbolNoMark (int typeIndex,int moduleIndex);
BEExternalTypeSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEExternalTypeSymbol (int typeIndex,int moduleIndex);
BEDontCareDefinitionSymbol :: !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEDontCareDefinitionSymbol ();
BEBoolSymbol :: !Bool !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEBoolSymbol (int value);
BELiteralSymbol :: !BESymbKind !String !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BELiteralSymbol (BESymbKind kind,CleanString value);
BEPredefineListConstructorSymbol :: !Int !Int !BESymbKind !Int !Int !BackEnd -> BackEnd;
// void BEPredefineListConstructorSymbol (int constructorIndex,int moduleIndex,BESymbKind symbolKind,int head_strictness,int tail_strictness);
BEPredefineListTypeSymbol :: !Int !Int !BESymbKind !Int !Int !BackEnd -> BackEnd;
// void BEPredefineListTypeSymbol (int typeIndex,int moduleIndex,BESymbKind symbolKind,int head_strictness,int tail_strictness);
BEAdjustStrictListConsInstance :: !Int !Int !BackEnd -> BackEnd;
// void BEAdjustStrictListConsInstance (int functionIndex,int moduleIndex);
BEAdjustUnboxedListDeconsInstance :: !Int !Int !BackEnd -> BackEnd;
// void BEAdjustUnboxedListDeconsInstance (int functionIndex,int moduleIndex);
BEAdjustOverloadedNilFunction :: !Int !Int !BackEnd -> BackEnd;
// void BEAdjustOverloadedNilFunction (int functionIndex,int moduleIndex);
BEOverloadedConsSymbol :: !Int !Int !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEOverloadedConsSymbol (int constructorIndex,int moduleIndex,int deconsIndex,int deconsModuleIndex);
BEOverloadedPushNode :: !Int !BESymbolP !BEArgP !BENodeIdListP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEOverloadedPushNode (int arity,BESymbolP symbol,BEArgP arguments,BENodeIdListP nodeIds,BENodeP decons_node);
BEPredefineConstructorSymbol :: !Int !Int !Int !BESymbKind !BackEnd -> BackEnd;
// void BEPredefineConstructorSymbol (int arity,int constructorIndex,int moduleIndex,BESymbKind symbolKind);
BEPredefineTypeSymbol :: !Int !Int !Int !BESymbKind !BackEnd -> BackEnd;
// void BEPredefineTypeSymbol (int arity,int typeIndex,int moduleIndex,BESymbKind symbolKind);
BEBasicSymbol :: !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEBasicSymbol (BESymbKind kind);
BEVar0TypeNode :: !BEAnnotation !BEAttribution !BackEnd -> (!BETypeNodeP,!BackEnd);
// BETypeNodeP BEVar0TypeNode (BEAnnotation annotation,BEAttribution attribution);
BEVarNTypeNode :: !BEAnnotation !BEAttribution !Int !BackEnd -> (!BETypeNodeP,!BackEnd);
// BETypeNodeP BEVarNTypeNode (BEAnnotation annotation,BEAttribution attribution,int argument_n);
BESymbolTypeNode :: !BEAnnotation !BEAttribution !BESymbolP !BETypeArgP !BackEnd -> (!BETypeNodeP,!BackEnd);
// BETypeNodeP BESymbolTypeNode (BEAnnotation annotation,BEAttribution attribution,BESymbolP symbol,BETypeArgP args);
BENoTypeArgs :: !BackEnd -> (!BETypeArgP,!BackEnd);
// BETypeArgP BENoTypeArgs ();
BETypeArgs :: !BETypeNodeP !BETypeArgP !BackEnd -> (!BETypeArgP,!BackEnd);
// BETypeArgP BETypeArgs (BETypeNodeP node,BETypeArgP nextArgs);
BETypeAlt :: !BESymbolP !BETypeArgP !BETypeNodeP !BackEnd -> (!BETypeAltP,!BackEnd);
// BETypeAltP BETypeAlt (BESymbolP lhs_symbol,BETypeArgP lhs_arguments,BETypeNodeP rhs);
BENormalNode :: !BESymbolP !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BENormalNode (BESymbolP symbol,BEArgP args);
BEMatchNode :: !Int !BESymbolP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEMatchNode (int arity,BESymbolP symbol,BENodeP node);
BETupleSelectNode :: !Int !Int !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BETupleSelectNode (int arity,int index,BENodeP node);
BEIfNode :: !BENodeP !BENodeP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEIfNode (BENodeP cond,BENodeP then,BENodeP elsje);
BEGuardNode :: !BENodeP !BENodeDefP !BEStrictNodeIdP !BENodeP !BENodeDefP !BEStrictNodeIdP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEGuardNode (BENodeP cond,BENodeDefP thenNodeDefs,BEStrictNodeIdP thenStricts,BENodeP then,BENodeDefP elseNodeDefs,BEStrictNodeIdP elseStricts,BENodeP elsje);
BESetNodeDefRefCounts :: !BENodeP !BackEnd -> BackEnd;
// void BESetNodeDefRefCounts (BENodeP lhs);
BEAddNodeIdsRefCounts :: !Int !BESymbolP !BENodeIdListP !BackEnd -> BackEnd;
// void BEAddNodeIdsRefCounts (int sequenceNumber,BESymbolP symbol,BENodeIdListP nodeIds);
BESwitchNode :: !BENodeIdP !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BESwitchNode (BENodeIdP nodeId,BEArgP caseNode);
BECaseNode :: !Int !BESymbolP !BENodeDefP !BEStrictNodeIdP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BECaseNode (int symbolArity,BESymbolP symbol,BENodeDefP nodeDefs,BEStrictNodeIdP strictNodeIds,BENodeP node);
BEOverloadedCaseNode :: !BENodeP !BENodeP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEOverloadedCaseNode (BENodeP case_node,BENodeP equal_node,BENodeP from_integer_node);
BEEnterLocalScope :: !BackEnd -> BackEnd;
// void BEEnterLocalScope ();
BELeaveLocalScope :: !BENodeP !BackEnd -> BackEnd;
// void BELeaveLocalScope (BENodeP node);
BEPushNode :: !Int !BESymbolP !BEArgP !BENodeIdListP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEPushNode (int arity,BESymbolP symbol,BEArgP arguments,BENodeIdListP nodeIds);
BEDefaultNode :: !BENodeDefP !BEStrictNodeIdP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEDefaultNode (BENodeDefP nodeDefs,BEStrictNodeIdP strictNodeIds,BENodeP node);
BESelectorNode :: !BESelectorKind !BESymbolP !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BESelectorNode (BESelectorKind selectorKind,BESymbolP fieldSymbol,BEArgP args);
BEUpdateNode :: !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEUpdateNode (BEArgP args);
BENodeIdNode :: !BENodeIdP !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BENodeIdNode (BENodeIdP nodeId,BEArgP args);
BENoArgs :: !BackEnd -> (!BEArgP,!BackEnd);
// BEArgP BENoArgs ();
BEArgs :: !BENodeP !BEArgP !BackEnd -> (!BEArgP,!BackEnd);
// BEArgP BEArgs (BENodeP node,BEArgP nextArgs);
BERuleAlt :: !Int !BENodeDefP !BENodeP !BENodeDefP !BEStrictNodeIdP !BENodeP !BackEnd -> (!BERuleAltP,!BackEnd);
// BERuleAltP BERuleAlt (int line,BENodeDefP lhsDefs,BENodeP lhs,BENodeDefP rhsDefs,BEStrictNodeIdP lhsStrictNodeIds,BENodeP rhs);
BEDeclareNodeId :: !Int !Int !String !BackEnd -> BackEnd;
// void BEDeclareNodeId (int sequenceNumber,int lhsOrRhs,CleanString name);
BENodeId :: !Int !BackEnd -> (!BENodeIdP,!BackEnd);
// BENodeIdP BENodeId (int sequenceNumber);
BEWildCardNodeId :: !BackEnd -> (!BENodeIdP,!BackEnd);
// BENodeIdP BEWildCardNodeId ();
BENodeDefList :: !Int !BENodeP !BENodeDefP !BackEnd -> (!BENodeDefP,!BackEnd);
// BENodeDefP BENodeDefList (int sequenceNumber,BENodeP node,BENodeDefP nodeDefs);
BENoNodeDefs :: !BackEnd -> (!BENodeDefP,!BackEnd);
// BENodeDefP BENoNodeDefs ();
BEStrictNodeIdList :: !BENodeIdP !BEStrictNodeIdP !BackEnd -> (!BEStrictNodeIdP,!BackEnd);
// BEStrictNodeIdP BEStrictNodeIdList (BENodeIdP nodeId,BEStrictNodeIdP strictNodeIds);
BENoStrictNodeIds :: !BackEnd -> (!BEStrictNodeIdP,!BackEnd);
// BEStrictNodeIdP BENoStrictNodeIds ();
BERule :: !Int !Int !BETypeAltP !BERuleAltP !BackEnd -> (!BEImpRuleP,!BackEnd);
// BEImpRuleP BERule (int functionIndex,int isCaf,BETypeAltP type,BERuleAltP alts);
BEDeclareRuleType :: !Int !Int !String !BackEnd -> BackEnd;
// void BEDeclareRuleType (int functionIndex,int moduleIndex,CleanString name);
BEDefineRuleType :: !Int !Int !BETypeAltP !BackEnd -> BackEnd;
// void BEDefineRuleType (int functionIndex,int moduleIndex,BETypeAltP typeAlt);
BEDefineRuleTypeWithCode :: !Int !Int !BETypeAltP !BECodeBlockP !BackEnd -> BackEnd;
// void BEDefineRuleTypeWithCode (int functionIndex,int moduleIndex,BETypeAltP typeAlt,BECodeBlockP codeBlock);
BEAdjustArrayFunction :: !BEArrayFunKind !Int !Int !BackEnd -> BackEnd;
// void BEAdjustArrayFunction (BEArrayFunKind arrayFunKind,int functionIndex,int moduleIndex);
BENoRules :: !BackEnd -> (!BEImpRuleP,!BackEnd);
// BEImpRuleP BENoRules ();
BERules :: !BEImpRuleP !BEImpRuleP !BackEnd -> (!BEImpRuleP,!BackEnd);
// BEImpRuleP BERules (BEImpRuleP rule,BEImpRuleP rules);
BEDefineAlgebraicType :: !BESymbolP !BEAttribution !BEConstructorListP !BackEnd -> BackEnd;
// void BEDefineAlgebraicType (BESymbolP symbol,BEAttribution attribution,BEConstructorListP constructors);
BEDefineExtensibleAlgebraicType :: !BESymbolP !BEAttribution !BEConstructorListP !BackEnd -> BackEnd;
// void BEDefineExtensibleAlgebraicType (BESymbolP symbol,BEAttribution attribution,BEConstructorListP constructors);
BEDefineRecordType :: !BESymbolP !BEAttribution !Int !Int !BETypeArgP !Int !BEFieldListP !BackEnd -> BackEnd;
// void BEDefineRecordType (BESymbolP symbol,BEAttribution attribution,int moduleIndex,int constructorIndex,BETypeArgP constructorArgs,int is_boxed_record,BEFieldListP fields);
BEAbstractType :: !BESymbolP !BackEnd -> BackEnd;
// void BEAbstractType (BESymbolP symbol);
BEConstructorList :: !BESymbolP !BETypeArgP !BEConstructorListP !BackEnd -> (!BEConstructorListP,!BackEnd);
// BEConstructorListP BEConstructorList (BESymbolP symbol_p,BETypeArgP type_args,BEConstructorListP constructors);
BENoConstructors :: !BackEnd -> (!BEConstructorListP,!BackEnd);
// BEConstructorListP BENoConstructors ();
BEFieldList :: !Int !Int !String !BETypeNodeP !BEFieldListP !BackEnd -> (!BEFieldListP,!BackEnd);
// BEFieldListP BEField (int fieldIndex,int moduleIndex,CleanString name,BETypeNodeP type,BEFieldListP fields);
BESetMemberTypeOfField :: !Int !Int !BETypeAltP !BackEnd -> BackEnd;
// void BESetMemberTypeOfField (int fieldIndex,int moduleIndex,BETypeAltP typeAlt);
BESetDictionaryFieldOfMember :: !Int !Int !Int !BackEnd -> (!Int,!BackEnd);
// int BESetDictionaryFieldOfMember (int function_index, int field_index, int field_module_index);
BESetInstanceFunctionOfFunction :: !Int !Int !BackEnd -> BackEnd;
// void BESetInstanceFunctionOfFunction (int function_index, int instance_function_index);
BENoFields :: !BackEnd -> (!BEFieldListP,!BackEnd);
// BEFieldListP BENoFields ();
BEDeclareConstructor :: !Int !Int !String !BackEnd -> BackEnd;
// void BEDeclareConstructor (int constructorIndex,int moduleIndex,CleanString name);
BEDeclareType :: !Int !Int !String !BackEnd -> BackEnd;
// void BEDeclareType (int typeIndex,int moduleIndex,CleanString name);
BEDeclareFunction :: !String !Int !Int !Int !BackEnd -> BackEnd;
// void BEDeclareFunction (CleanString name,int arity,int functionIndex,int ancestor);
BEStartFunction :: !Int !BackEnd -> BackEnd;
// void BEStartFunction (int functionIndex);
BECodeAlt :: !Int !BENodeDefP !BENodeP !BECodeBlockP !BackEnd -> (!BERuleAltP,!BackEnd);
// BERuleAltP BECodeAlt (int line,BENodeDefP lhsDefs,BENodeP lhs,BECodeBlockP codeBlock);
BEStringList :: !String !BEStringListP !BackEnd -> (!BEStringListP,!BackEnd);
// BEStringListP BEStringList (CleanString cleanString,BEStringListP strings);
BENoStrings :: !BackEnd -> (!BEStringListP,!BackEnd);
// BEStringListP BENoStrings ();
BECodeParameterList :: !String !BENodeIdP !BECodeParameterP !BackEnd -> (!BECodeParameterP,!BackEnd);
// BECodeParameterP BECodeParameterList (CleanString location,BENodeIdP nodeId,BECodeParameterP parameters);
BENoCodeParameters :: !BackEnd -> (!BECodeParameterP,!BackEnd);
// BECodeParameterP BENoCodeParameters ();
BENodeIdList :: !BENodeIdP !BENodeIdListP !BackEnd -> (!BENodeIdListP,!BackEnd);
// BENodeIdListP BENodeIdList (BENodeIdP nodeId,BENodeIdListP nids);
BENoNodeIds :: !BackEnd -> (!BENodeIdListP,!BackEnd);
// BENodeIdListP BENoNodeIds ();
BEAbcCodeBlock :: !Bool !BEStringListP !BackEnd -> (!BECodeBlockP,!BackEnd);
// BECodeBlockP BEAbcCodeBlock (int inlineFlag,BEStringListP instructions);
BEAnyCodeBlock :: !BECodeParameterP !BECodeParameterP !BEStringListP !BackEnd -> (!BECodeBlockP,!BackEnd);
// BECodeBlockP BEAnyCodeBlock (BECodeParameterP inParams,BECodeParameterP outParams,BEStringListP instructions);
BEDeclareIclModule :: !String !String !Int !Int !Int !Int !BackEnd -> BackEnd;
// void BEDeclareIclModule (CleanString name,CleanString modificationTime,int nFunctions,int nTypes,int nConstructors,int nFields);
BEDeclareDclModule :: !Int !String !String !Bool !Int !Int !Int !Int !BackEnd -> BackEnd;
// void BEDeclareDclModule (int moduleIndex,CleanString name,CleanString modificationTime,int systemModule,int nFunctions,int nTypes,int nConstructors,int nFields);
BEDeclarePredefinedModule :: !Int !Int !BackEnd -> BackEnd;
// void BEDeclarePredefinedModule (int nTypes,int nConstructors);
BEDefineRules :: !BEImpRuleP !BackEnd -> BackEnd;
// void BEDefineRules (BEImpRuleP rules);
BEGenerateCode :: !String !BackEnd -> (!Bool,!BackEnd);
// int BEGenerateCode (CleanString outputFile);
BEGetError :: {#Char};
// CleanString BEGetError ();
BEExportType :: !Bool !Int !BackEnd -> BackEnd;
// void BEExportType (int isDictionary,int typeIndex);
BEExportConstructor :: !Int !BackEnd -> BackEnd;
// void BEExportConstructor (int constructorIndex);
BEExportField :: !Bool !Int !BackEnd -> BackEnd;
// void BEExportField (int isDictionaryField,int fieldIndex);
BEExportFunction :: !Int !BackEnd -> BackEnd;
// void BEExportFunction (int functionIndex);
BEDefineImportedObjsAndLibs :: !BEStringListP !BEStringListP !BackEnd -> BackEnd;
// void BEDefineImportedObjsAndLibs (BEStringListP objs,BEStringListP libs);
BEInsertForeignExport :: !BESymbolP !Int !BackEnd -> BackEnd;
// void BEInsertForeignExport (BESymbolP symbol_p,int stdcall);
BESetMainDclModuleN :: !Int !BackEnd -> BackEnd;
// void BESetMainDclModuleN (int main_dcl_module_n_parameter);
BEStrictPositions :: !Int !BackEnd -> (!Int,!Int,!BackEnd);
// void BEStrictPositions (int functionIndex,int* bits,int** positions);
BEGetIntFromArray :: !Int !Int -> Int;
// int BEGetIntFromArray (int index,int* ints);
BEDeclareDynamicTypeSymbol :: !Int !Int !BackEnd -> BackEnd;
// void BEDeclareDynamicTypeSymbol (int typeIndex,int moduleIndex);
BEDynamicTempTypeSymbol :: !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEDynamicTempTypeSymbol ();
kBEVersionCurrent:==0x02116000;
kBEVersionOldestDefinition:==0x02100401;
kBEVersionOldestImplementation:==0x02100401;
kBEDebug:==1;
kPredefinedModuleIndex:==1;
BENoAnnot:==0;
BEStrictAnnot:==1;
BENoUniAttr:==0;
BENotUniqueAttr:==1;
BEUniqueAttr:==2;
BEExistsAttr:==3;
BEUniqueVariable:==4;
BEFirstUniVarNumber:==5;
BEIntType:==0;
BEBoolType:==1;
BECharType:==2;
BERealType:==3;
BEFileType:==4;
BEStringType:==5;
BEWorldType:==6;
BEProcIdType:==7;
BERedIdType:==8;
BERationalDenot:==9;
BEIntDenot:==10;
BEBoolDenot:==11;
BECharDenot:==12;
BERealDenot:==13;
BEIntegerDenot:==14;
BEStringDenot:==15;
BEFunType:==16;
BEArrayType:==17;
BEStrictArrayType:==18;
BEUnboxedArrayType:==19;
BEPackedArrayType:==20;
BEListType:==21;
BETupleType:==22;
BEEmptyType:==23;
BEDynamicType:==24;
BENrOfPredefTypes:==25;
BETupleSymb:==26;
BEConsSymb:==27;
BENilSymb:==28;
BEApplySymb:==29;
BEIfSymb:==30;
BEFailSymb:==31;
BEAllSymb:==32;
BESelectSymb:==33;
BENrOfPredefFunsOrConses:==34;
BEDefinition:==35;
BENewSymbol:==36;
BEInstanceSymb:==37;
BEEmptySymbol:==38;
BEFieldSymbolList:==39;
BEErroneousSymb:==40;
BECreateArrayFun:==0;
BEArraySelectFun:==1;
BEUnqArraySelectFun:==2;
BEArrayUpdateFun:==3;
BEArrayReplaceFun:==4;
BEArraySizeFun:==5;
BEUnqArraySizeFun:==6;
BE_CreateArrayFun:==7;
BE_UnqArraySelectFun:==8;
BE_UnqArraySelectNextFun:==9;
BE_UnqArraySelectLastFun:==10;
BE_ArrayUpdateFun:==11;
BENoArrayFun:==12;
BESelectorDummy:==0;
BESelector:==1;
BESelector_U:==2;
BESelector_F:==3;
BESelector_L:==4;
BESelector_N:==5;
BESpecialIdentStdMisc:==0;
BESpecialIdentAbort:==1;
BESpecialIdentUndef:==2;
BESpecialIdentStdBool:==3;
BESpecialIdentAnd:==4;
BESpecialIdentOr:==5;
BESpecialIdentPrelude:==6;
BESpecialIdentSeq:==7;
BESpecialIdentCount:==8;
BELhsNodeId:==0;
BERhsNodeId:==1;
BEIsNotACaf:==0;
BEIsACaf:==1;
