definition module backend;

from StdString import String;

:: *UWorld :== Int;
:: *BackEnd; // :== Int;
:: BESymbolP; // :== Int;
:: BETypeNodeP; // :== Int;
:: BETypeArgP; // :== Int;
:: BETypeAltP; // :== Int;
:: BENodeP; // :== Int;
:: BEArgP; // :== Int;
:: BERuleAltP; // :== Int;
:: BEImpRuleP; // :== Int;
:: BETypeP; // :== Int;
:: BEFlatTypeP; // :== Int;
:: BETypeVarP; // :== Int;
:: BETypeVarListP; // :== Int;
:: BEConstructorListP; // :== Int;
:: BEFieldListP; // :== Int;
:: BENodeIdP; // :== Int;
:: BENodeDefP; // :== Int;
:: BEStrictNodeIdP; // :== Int;
:: BECodeParameterP; // :== Int;
:: BECodeBlockP; // :== Int;
:: BEStringListP; // :== Int;
:: BEAnnotation :== Int;
:: BEAttribution :== Int;
:: BESymbKind :== Int;
:: BEArrayFunKind :== Int;
:: BESelectorKind :== Int;
:: BEUpdateKind :== Int;
BEGetVersion :: (!Int,!Int,!Int);
// void BEGetVersion(int* current,int* oldestDefinition,int* oldestImplementation);
BEInit :: !Int !UWorld -> (!BackEnd,!UWorld);
// BackEnd BEInit(int argc);
BEFree :: !BackEnd !UWorld -> UWorld;
// void BEFree(BackEnd backEnd);
BEArg :: !String !BackEnd -> BackEnd;
// void BEArg(CleanString arg);
BEDeclareModules :: !Int !BackEnd -> BackEnd;
// void BEDeclareModules(int nModules);
BEDeclarePredefinedSymbols :: !Int !Int !BackEnd -> BackEnd;
// void BEDeclarePredefinedSymbols(int nConstructors,int nTypes);
BESpecialArrayFunctionSymbol :: !BEArrayFunKind !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BESpecialArrayFunctionSymbol(BEArrayFunKind arrayFunKind,int functionIndex,int moduleIndex);
BEDictionarySelectFunSymbol :: !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEDictionarySelectFunSymbol();
BEDictionaryUpdateFunSymbol :: !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEDictionaryUpdateFunSymbol();
BEFunctionSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEFunctionSymbol(int functionIndex,int moduleIndex);
BEConstructorSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEConstructorSymbol(int constructorIndex,int moduleIndex);
BEFieldSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEFieldSymbol(int fieldIndex,int moduleIndex);
BETypeSymbol :: !Int !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BETypeSymbol(int typeIndex,int moduleIndex);
BEDontCareDefinitionSymbol :: !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEDontCareDefinitionSymbol();
BEBoolSymbol :: !Bool !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEBoolSymbol(int value);
BELiteralSymbol :: !BESymbKind !String !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BELiteralSymbol(BESymbKind kind,CleanString value);
BEPredefineConstructorSymbol :: !Int !Int !Int !BESymbKind !BackEnd -> BackEnd;
// void BEPredefineConstructorSymbol(int arity,int constructorIndex,int moduleIndex,BESymbKind symbolKind);
BEPredefineTypeSymbol :: !Int !Int !Int !BESymbKind !BackEnd -> BackEnd;
// void BEPredefineTypeSymbol(int arity,int typeIndex,int moduleIndex,BESymbKind symbolKind);
BEBasicSymbol :: !Int !BackEnd -> (!BESymbolP,!BackEnd);
// BESymbolP BEBasicSymbol(BESymbKind kind);
BEVarTypeNode :: !String !BackEnd -> (!BETypeNodeP,!BackEnd);
// BETypeNodeP BEVarTypeNode(CleanString name);
BETypeVars :: !BETypeVarP !BETypeVarListP !BackEnd -> (!BETypeVarListP,!BackEnd);
// BETypeVarListP BETypeVars(BETypeVarP typeVar,BETypeVarListP typeVarList);
BENoTypeVars :: !BackEnd -> (!BETypeVarListP,!BackEnd);
// BETypeVarListP BENoTypeVars();
BENormalTypeNode :: !BESymbolP !BETypeArgP !BackEnd -> (!BETypeNodeP,!BackEnd);
// BETypeNodeP BENormalTypeNode(BESymbolP symbol,BETypeArgP args);
BEAnnotateTypeNode :: !BEAnnotation !BETypeNodeP !BackEnd -> (!BETypeNodeP,!BackEnd);
// BETypeNodeP BEAnnotateTypeNode(BEAnnotation annotation,BETypeNodeP typeNode);
BEAttributeTypeNode :: !BEAttribution !BETypeNodeP !BackEnd -> (!BETypeNodeP,!BackEnd);
// BETypeNodeP BEAttributeTypeNode(BEAttribution attribution,BETypeNodeP typeNode);
BENoTypeArgs :: !BackEnd -> (!BETypeArgP,!BackEnd);
// BETypeArgP BENoTypeArgs();
BETypeArgs :: !BETypeNodeP !BETypeArgP !BackEnd -> (!BETypeArgP,!BackEnd);
// BETypeArgP BETypeArgs(BETypeNodeP node,BETypeArgP nextArgs);
BETypeAlt :: !BETypeNodeP !BETypeNodeP !BackEnd -> (!BETypeAltP,!BackEnd);
// BETypeAltP BETypeAlt(BETypeNodeP lhs,BETypeNodeP rhs);
BENormalNode :: !BESymbolP !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BENormalNode(BESymbolP symbol,BEArgP args);
BEMatchNode :: !Int !BESymbolP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEMatchNode(int arity,BESymbolP symbol,BENodeP node);
BETupleSelectNode :: !Int !Int !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BETupleSelectNode(int arity,int index,BENodeP node);
BEIfNode :: !BENodeP !BENodeP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEIfNode(BENodeP cond,BENodeP then,BENodeP elsje);
BEGuardNode :: !BENodeP !BENodeDefP !BEStrictNodeIdP !BENodeP !BENodeDefP !BEStrictNodeIdP !BENodeP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEGuardNode(BENodeP cond,BENodeDefP thenNodeDefs,BEStrictNodeIdP thenStricts,BENodeP then,BENodeDefP elseNodeDefs,BEStrictNodeIdP elseStricts,BENodeP elsje);
BESelectorNode :: !BESelectorKind !BESymbolP !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BESelectorNode(BESelectorKind selectorKind,BESymbolP fieldSymbol,BEArgP args);
BEUpdateNode :: !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BEUpdateNode(BEArgP args);
BENodeIdNode :: !BENodeIdP !BEArgP !BackEnd -> (!BENodeP,!BackEnd);
// BENodeP BENodeIdNode(BENodeIdP nodeId,BEArgP args);
BENoArgs :: !BackEnd -> (!BEArgP,!BackEnd);
// BEArgP BENoArgs();
BEArgs :: !BENodeP !BEArgP !BackEnd -> (!BEArgP,!BackEnd);
// BEArgP BEArgs(BENodeP node,BEArgP nextArgs);
BERuleAlt :: !Int !BENodeDefP !BENodeP !BENodeDefP !BEStrictNodeIdP !BENodeP !BackEnd -> (!BERuleAltP,!BackEnd);
// BERuleAltP BERuleAlt(int line,BENodeDefP lhsDefs,BENodeP lhs,BENodeDefP rhsDefs,BEStrictNodeIdP lhsStrictNodeIds,BENodeP rhs);
BERuleAlts :: !BERuleAltP !BERuleAltP !BackEnd -> (!BERuleAltP,!BackEnd);
// BERuleAltP BERuleAlts(BERuleAltP alt,BERuleAltP alts);
BENoRuleAlts :: !BackEnd -> (!BERuleAltP,!BackEnd);
// BERuleAltP BENoRuleAlts();
BEDeclareNodeId :: !Int !Int !String !BackEnd -> BackEnd;
// void BEDeclareNodeId(int sequenceNumber,int lhsOrRhs,CleanString name);
BENodeId :: !Int !BackEnd -> (!BENodeIdP,!BackEnd);
// BENodeIdP BENodeId(int sequenceNumber);
BEWildCardNodeId :: !BackEnd -> (!BENodeIdP,!BackEnd);
// BENodeIdP BEWildCardNodeId();
BENodeDef :: !Int !BENodeP !BackEnd -> (!BENodeDefP,!BackEnd);
// BENodeDefP BENodeDef(int sequenceNumber,BENodeP node);
BENoNodeDefs :: !BackEnd -> (!BENodeDefP,!BackEnd);
// BENodeDefP BENoNodeDefs();
BENodeDefs :: !BENodeDefP !BENodeDefP !BackEnd -> (!BENodeDefP,!BackEnd);
// BENodeDefP BENodeDefs(BENodeDefP nodeDef,BENodeDefP nodeDefs);
BEStrictNodeId :: !BENodeIdP !BackEnd -> (!BEStrictNodeIdP,!BackEnd);
// BEStrictNodeIdP BEStrictNodeId(BENodeIdP nodeId);
BENoStrictNodeIds :: !BackEnd -> (!BEStrictNodeIdP,!BackEnd);
// BEStrictNodeIdP BENoStrictNodeIds();
BEStrictNodeIds :: !BEStrictNodeIdP !BEStrictNodeIdP !BackEnd -> (!BEStrictNodeIdP,!BackEnd);
// BEStrictNodeIdP BEStrictNodeIds(BEStrictNodeIdP strictNodeId,BEStrictNodeIdP strictNodeIds);
BERule :: !Int !Int !BETypeAltP !BERuleAltP !BackEnd -> (!BEImpRuleP,!BackEnd);
// BEImpRuleP BERule(int functionIndex,int isCaf,BETypeAltP type,BERuleAltP alts);
BEDeclareRuleType :: !Int !Int !String !BackEnd -> BackEnd;
// void BEDeclareRuleType(int functionIndex,int moduleIndex,CleanString name);
BEDefineRuleType :: !Int !Int !BETypeAltP !BackEnd -> BackEnd;
// void BEDefineRuleType(int functionIndex,int moduleIndex,BETypeAltP typeAlt);
BEAdjustArrayFunction :: !BEArrayFunKind !Int !Int !BackEnd -> BackEnd;
// void BEAdjustArrayFunction(BEArrayFunKind arrayFunKind,int functionIndex,int moduleIndex);
BENoRules :: !BackEnd -> (!BEImpRuleP,!BackEnd);
// BEImpRuleP BENoRules();
BERules :: !BEImpRuleP !BEImpRuleP !BackEnd -> (!BEImpRuleP,!BackEnd);
// BEImpRuleP BERules(BEImpRuleP rule,BEImpRuleP rules);
BETypes :: !BETypeP !BETypeP !BackEnd -> (!BETypeP,!BackEnd);
// BETypeP BETypes(BETypeP type,BETypeP types);
BENoTypes :: !BackEnd -> (!BETypeP,!BackEnd);
// BETypeP BENoTypes();
BEFlatType :: !BESymbolP !BETypeVarListP !BackEnd -> (!BEFlatTypeP,!BackEnd);
// BEFlatTypeP BEFlatType(BESymbolP symbol,BETypeVarListP arguments);
BEAlgebraicType :: !BEFlatTypeP !BEConstructorListP !BackEnd -> BackEnd;
// void BEAlgebraicType(BEFlatTypeP lhs,BEConstructorListP constructors);
BERecordType :: !Int !BEFlatTypeP !BETypeNodeP !BEFieldListP !BackEnd -> BackEnd;
// void BERecordType(int moduleIndex,BEFlatTypeP lhs,BETypeNodeP constructorType,BEFieldListP fields);
BEAbsType :: !BEFlatTypeP !BackEnd -> BackEnd;
// void BEAbsType(BEFlatTypeP lhs);
BEConstructors :: !BEConstructorListP !BEConstructorListP !BackEnd -> (!BEConstructorListP,!BackEnd);
// BEConstructorListP BEConstructors(BEConstructorListP constructor,BEConstructorListP constructors);
BENoConstructors :: !BackEnd -> (!BEConstructorListP,!BackEnd);
// BEConstructorListP BENoConstructors();
BEConstructor :: !BETypeNodeP !BackEnd -> (!BEConstructorListP,!BackEnd);
// BEConstructorListP BEConstructor(BETypeNodeP type);
BEDeclareField :: !Int !Int !String !BackEnd -> BackEnd;
// void BEDeclareField(int fieldIndex,int moduleIndex,CleanString name);
BEField :: !Int !Int !BETypeNodeP !BackEnd -> (!BEFieldListP,!BackEnd);
// BEFieldListP BEField(int fieldIndex,int moduleIndex,BETypeNodeP type);
BEFields :: !BEFieldListP !BEFieldListP !BackEnd -> (!BEFieldListP,!BackEnd);
// BEFieldListP BEFields(BEFieldListP field,BEFieldListP fields);
BENoFields :: !BackEnd -> (!BEFieldListP,!BackEnd);
// BEFieldListP BENoFields();
BEDeclareConstructor :: !Int !Int !String !BackEnd -> BackEnd;
// void BEDeclareConstructor(int constructorIndex,int moduleIndex,CleanString name);
BETypeVar :: !String !BackEnd -> (!BETypeVarP,!BackEnd);
// BETypeVarP BETypeVar(CleanString name);
BEDeclareType :: !Int !Int !String !BackEnd -> BackEnd;
// void BEDeclareType(int typeIndex,int moduleIndex,CleanString name);
BEDeclareFunction :: !String !Int !Int !Int !BackEnd -> BackEnd;
// void BEDeclareFunction(CleanString name,int arity,int functionIndex,int ancestor);
BECodeAlt :: !Int !BENodeDefP !BENodeP !BECodeBlockP !BackEnd -> (!BERuleAltP,!BackEnd);
// BERuleAltP BECodeAlt(int line,BENodeDefP lhsDefs,BENodeP lhs,BECodeBlockP codeBlock);
BEString :: !String !BackEnd -> (!BEStringListP,!BackEnd);
// BEStringListP BEString(CleanString cleanString);
BEStrings :: !BEStringListP !BEStringListP !BackEnd -> (!BEStringListP,!BackEnd);
// BEStringListP BEStrings(BEStringListP string,BEStringListP strings);
BENoStrings :: !BackEnd -> (!BEStringListP,!BackEnd);
// BEStringListP BENoStrings();
BECodeParameter :: !String !BENodeIdP !BackEnd -> (!BECodeParameterP,!BackEnd);
// BECodeParameterP BECodeParameter(CleanString location,BENodeIdP nodeId);
BECodeParameters :: !BECodeParameterP !BECodeParameterP !BackEnd -> (!BECodeParameterP,!BackEnd);
// BECodeParameterP BECodeParameters(BECodeParameterP parameter,BECodeParameterP parameters);
BENoCodeParameters :: !BackEnd -> (!BECodeParameterP,!BackEnd);
// BECodeParameterP BENoCodeParameters();
BEAbcCodeBlock :: !Bool !BEStringListP !BackEnd -> (!BECodeBlockP,!BackEnd);
// BECodeBlockP BEAbcCodeBlock(int inline,BEStringListP instructions);
BEAnyCodeBlock :: !BECodeParameterP !BECodeParameterP !BEStringListP !BackEnd -> (!BECodeBlockP,!BackEnd);
// BECodeBlockP BEAnyCodeBlock(BECodeParameterP inParams,BECodeParameterP outParams,BEStringListP instructions);
BEDeclareIclModule :: !String !Int !Int !Int !Int !BackEnd -> BackEnd;
// void BEDeclareIclModule(CleanString name,int nFunctions,int nTypes,int nConstructors,int nFields);
BEDeclareDclModule :: !Int !String !Bool !Int !Int !Int !Int !BackEnd -> BackEnd;
// void BEDeclareDclModule(int moduleIndex,CleanString name,int systemModule,int nFunctions,int nTypes,int nConstructors,int nFields);
BEDeclarePredefinedModule :: !Int !Int !BackEnd -> BackEnd;
// void BEDeclarePredefinedModule(int nTypes,int nConstructors);
BEDefineRules :: !BEImpRuleP !BackEnd -> BackEnd;
// void BEDefineRules(BEImpRuleP rules);
BEGenerateCode :: !String !BackEnd -> (!Bool,!BackEnd);
// int BEGenerateCode(CleanString outputFile);
BEExportType :: !Int !Int !BackEnd -> BackEnd;
// void BEExportType(int dclTypeIndex,int iclTypeIndex);
BESwapTypes :: !Int !Int !BackEnd -> BackEnd;
// void BESwapTypes(int frm,int to);
BEExportConstructor :: !Int !Int !BackEnd -> BackEnd;
// void BEExportConstructor(int dclConstructorIndex,int iclConstructorIndex);
BEExportField :: !Int !Int !BackEnd -> BackEnd;
// void BEExportField(int dclTypeIndex,int iclTypeIndex);
BEExportFunction :: !Int !Int !BackEnd -> BackEnd;
// void BEExportFunction(int dclFunctionIndex,int iclFunctionIndex);
BEDefineImportedObjsAndLibs :: !BEStringListP !BEStringListP !BackEnd -> BackEnd;
// void BEDefineImportedObjsAndLibs(BEStringListP objs,BEStringListP libs);
kBEVersionCurrent:==0x02000203;
kBEVersionOldestDefinition:==0x02000203;
kBEVersionOldestImplementation:==0x02000203;
kBEDebug:==1;
kIclModuleIndex:==0;
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
BENrOfBasicTypes:==9;
BEIntDenot:==10;
BEBoolDenot:==11;
BECharDenot:==12;
BERealDenot:==13;
BENrOfBasicDenots:==14;
BEStringDenot:==15;
BEFunType:==16;
BEArrayType:==17;
BEStrictArrayType:==18;
BEUnboxedArrayType:==19;
BEListType:==20;
BETupleType:==21;
BEEmptyType:==22;
BEDynamicType:==23;
BENrOfPredefTypes:==24;
BETupleSymb:==25;
BEConsSymb:==26;
BENilSymb:==27;
BEApplySymb:==28;
BEIfSymb:==29;
BEFailSymb:==30;
BEAllSymb:==31;
BESelectSymb:==32;
BENrOfPredefFunsOrConses:==33;
BEDefinition:==34;
BENewSymbol:==35;
BEInstanceSymb:==36;
BEEmptySymbol:==37;
BEFieldSymbolList:==38;
BEErroneousSymb:==39;
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
BEUpdateDummy:==0;
BEUpdate:==1;
BEUpdate_U:==2;
BELhsNodeId:==0;
BERhsNodeId:==1;
BEIsNotACaf:==0;
BEIsACaf:==1;
