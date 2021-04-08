implementation module backendconvert

import StdEnv, compare_types
from StdFunc import return
import frontend
import backend
import backendsupport, backendpreprocess

// trace macro
(-*->) infixl
(-*->) value trace
	:==	value //---> trace
/*
sfoldr op r l
	:== foldr l
	where
		foldr [] = r
		foldr [a:x] = \s -> op a (foldr x) s
*/
sfoldr op r l s
	:== foldr l s
	where
		foldr [] = r
		foldr [a:x] = op a (foldr x)

::	FunctionPattern	= FP_Algebraic !(Global DefinedSymbol) ![FunctionPattern]
					| FP_Variable !FreeVar

:: BEMonad a :== *BackEndState -> *(a,*BackEndState)
:: BackEnder :== *BackEndState -> *BackEndState

//
:: *BackEndState = {bes_backEnd :: !BackEnd, bes_varHeap :: !*VarHeap, bes_attrHeap :: !*AttrVarHeap, bes_attr_number :: !Int}

appBackEnd f beState
	:== {beState & bes_backEnd = bes_backEnd}
	where
		bes_backEnd = f beState.bes_backEnd

accBackEnd f beState
	:== accBackEnd
	where
		accBackEnd
			# (result, bes_backEnd) =	f beState.bes_backEnd
			#! beState2 = {beState & bes_backEnd = bes_backEnd}
			= (result,beState2)

accVarHeap f beState
	:== (result, {beState & bes_varHeap = varHeap})
	where
		(result, varHeap) =	f beState.bes_varHeap

accAttrHeap f beState
	:== (result, {beState & bes_attrHeap = attrHeap})
	where
		(result, attrHeap) =	f beState.bes_attrHeap


read_from_var_heap :: VarInfoPtr BackEndState -> (VarInfo, BackEndState)
read_from_var_heap ptr beState
	= (result, {beState & bes_varHeap = varHeap})
where
		(result, varHeap) =	readPtr ptr beState.bes_varHeap

write_to_var_heap ptr v beState
	= {beState & bes_varHeap = writePtr ptr v beState.bes_varHeap}

read_from_attr_heap ptr beState
	= (result, {beState & bes_attrHeap = attrHeap})
where
		(result, attrHeap) =	readPtr ptr beState.bes_attrHeap

write_to_attr_heap ptr v beState
	= {beState & bes_attrHeap = writePtr ptr v beState.bes_attrHeap}
/*
read_from_var_heap ptr heap be
	= (sreadPtr ptr heap,be)

::	*BackEndState :== BackEnd

appBackEnd f beState :== f beState
accBackEnd f beState :== f beState
accVarHeap f beState :== f beState
*/

beApFunction0 f
	:== appBackEnd f
beApFunction1 f m1
	:== m1 ==> \a1
	->	appBackEnd (f a1)
beApFunction2 f m1 m2
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	appBackEnd (f a1 a2)

beFunction0 f
	:== accBackEnd f
beFunction1 f m1
	:== m1 ==> \a1
	->	accBackEnd (f a1)
beFunction2 f m1 m2
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	accBackEnd (f a1 a2)
beFunction3 f m1 m2 m3
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	m3 ==> \a3
	->	accBackEnd (f a1 a2 a3)
beFunction4 f m1 m2 m3 m4
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	m3 ==> \a3
	->	m4 ==> \a4
	->	accBackEnd (f a1 a2 a3 a4)
beFunction5 f m1 m2 m3 m4 m5
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	m3 ==> \a3
	->	m4 ==> \a4
	->	m5 ==> \a5
	->	accBackEnd (f a1 a2 a3 a4 a5)
beFunction6 f m1 m2 m3 m4 m5 m6
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	m3 ==> \a3
	->	m4 ==> \a4
	->	m5 ==> \a5
	->	m6 ==> \a6
	->	accBackEnd (f a1 a2 a3 a4 a5 a6)
beFunction7 f m1 m2 m3 m4 m5 m6 m7
	:== m1 ==> \a1
	->	m2 ==> \a2
	->	m3 ==> \a3
	->	m4 ==> \a4
	->	m5 ==> \a5
	->	m6 ==> \a6
	->	m7 ==> \a7
	->	accBackEnd (f a1 a2 a3 a4 a5 a6 a7)

changeArrayFunctionIndex selectIndex
	:== selectIndex

beBoolSymbol value
	:==	beFunction0 (BEBoolSymbol value)
beLiteralSymbol type value
	:==	beFunction0 (BELiteralSymbol type value)
beFunctionSymbol functionIndex moduleIndex
	:==	beFunction0 (BEFunctionSymbol functionIndex moduleIndex)
beSpecialArrayFunctionSymbol arrayFunKind functionIndex moduleIndex
	:==	beFunction0 (BESpecialArrayFunctionSymbol arrayFunKind (changeArrayFunctionIndex functionIndex) moduleIndex)
beDictionarySelectFunSymbol
	:==	beFunction0 BEDictionarySelectFunSymbol
beDictionaryUpdateFunSymbol
	:==	beFunction0 BEDictionaryUpdateFunSymbol
beConstructorSymbol moduleIndex constructorIndex
	:==	beFunction0 (BEConstructorSymbol constructorIndex moduleIndex)

beOverloadedConsSymbol moduleIndex constructorIndex deconsModuleIndex deconsIndex
	:==	beFunction0 (BEOverloadedConsSymbol constructorIndex moduleIndex deconsIndex deconsModuleIndex)

beFieldSymbol fieldIndex moduleIndex
	:==	beFunction0 (BEFieldSymbol fieldIndex moduleIndex)
beTypeSymbol typeIndex moduleIndex
	:==	beFunction0 (BETypeSymbol typeIndex moduleIndex)
beTypeSymbolNoMark typeIndex moduleIndex
	:==	beFunction0 (BETypeSymbolNoMark typeIndex moduleIndex)
beExternalTypeSymbol typeIndex moduleIndex
	:==	beFunction0 (BEExternalTypeSymbol typeIndex moduleIndex)
beBasicSymbol symbolIndex
	:==	beFunction0 (BEBasicSymbol symbolIndex)
beBasicTypeSymbol symbolIndex
	:==	beFunction0 (BEBasicTypeSymbol symbolIndex)
beDontCareDefinitionSymbol
	:==	beFunction0 BEDontCareDefinitionSymbol
beDontCareTypeDefinitionSymbol
	:==	beFunction0 BEDontCareTypeDefinitionSymbol
beNoArgs
	:==	beFunction0 BENoArgs
beArgs
	:==	beFunction2 BEArgs
beNoTypeArgs
	:==	beFunction0 BENoTypeArgs
beTypeArgs
	:==	beFunction2 BETypeArgs
beNormalNode
	:==	beFunction2 BENormalNode
beIfNode
	:==	beFunction3 BEIfNode
beGuardNode
	:==	beFunction7 BEGuardNode
beSelectorNode selectorKind
	:==	beFunction2 (BESelectorNode selectorKind)
beUpdateNode
	:==	beFunction1 BEUpdateNode
beRuleAlt lineNumber
	:==	beFunction5 (BERuleAlt lineNumber)
beTypeAlt symbol_p
	:==	beFunction2 (BETypeAlt symbol_p)
beRule index isCaf
	:==	beFunction2 (BERule index isCaf)
beNoNodeDefs
	:==	beFunction0 BENoNodeDefs
beNoStrictNodeIds
	:==	beFunction0 BENoStrictNodeIds
beNodeIdNode
	:==	beFunction2 BENodeIdNode
beNodeId sequenceNumber
	:==	beFunction0 (BENodeId sequenceNumber)
beNoConstructors
	:==	beFunction0 BENoConstructors
beDeclareRuleType functionIndex moduleIndex name
	:==	beApFunction0 (BEDeclareRuleType functionIndex moduleIndex name)
beDefineRuleType functionIndex moduleIndex
	:==	beApFunction1 (BEDefineRuleType functionIndex moduleIndex)
beDefineRuleTypeWithCode functionIndex moduleIndex
	:==	beApFunction2 (BEDefineRuleTypeWithCode functionIndex moduleIndex)
beCodeAlt lineNumber
	:==	beFunction3 (BECodeAlt lineNumber)
beStringList string strings
	:==	beFunction0 (BEStringList string strings)
beNoStrings
	:==	beFunction0 BENoStrings
beNoCodeParameters
	:==	beFunction0 BENoCodeParameters
beAbcCodeBlock inline
	:==	beFunction1 (BEAbcCodeBlock inline)
beAnyCodeBlock
	:==	beFunction3 BEAnyCodeBlock
beDeclareNodeId number lhsOrRhs name
	:==	beApFunction0 (BEDeclareNodeId number lhsOrRhs name)
beAdjustArrayFunction backendId functionIndex moduleIndex
	:==	beApFunction0 (BEAdjustArrayFunction backendId functionIndex moduleIndex)
beExportType isDictionary typeIndex
	:==	beApFunction0 (BEExportType isDictionary typeIndex)
beExportConstructor constructorIndex
	:==	beApFunction0 (BEExportConstructor constructorIndex)
beExportField isDictionaryField fieldIndex
	:==	beApFunction0 (BEExportField isDictionaryField fieldIndex)
beExportFunction functionIndex
	:==	beApFunction0 (BEExportFunction functionIndex)
beTupleSelectNode arity index
	:==	beFunction1 (BETupleSelectNode arity index)
beMatchNode arity
	:==	beFunction2 (BEMatchNode arity)
beDefineImportedObjsAndLibs
	:== beApFunction2 BEDefineImportedObjsAndLibs
beSwitchNode
	:==	beFunction2 BESwitchNode
beDefaultNode
	:==	beFunction3 BEDefaultNode
beNoNodeIds
	:==	beFunction0 BENoNodeIds
beBindSpecialModule specialIdentIndex moduleIndex
	:== beApFunction0 (BEBindSpecialModule specialIdentIndex moduleIndex)
beBindSpecialFunction specialIdentIndex functionIndex moduleIndex
	:== beApFunction0 (BEBindSpecialFunction specialIdentIndex functionIndex moduleIndex)

// temporary hack
beDynamicTempTypeSymbol
	:== beFunction0 BEDynamicTempTypeSymbol

backEndConvertModules :: PredefinedSymbols FrontEndSyntaxTree !Int !*TypeVarHeap !*VarHeap !*AttrVarHeap !*BackEnd
															   -> (!*TypeVarHeap,!*VarHeap,!*AttrVarHeap,!*BackEnd)
backEndConvertModules p s main_dcl_module_n type_var_heap var_heap attr_var_heap be
	# (type_var_heap,{bes_varHeap,bes_attrHeap,bes_backEnd})
		= backEndConvertModulesH p s main_dcl_module_n type_var_heap {bes_varHeap=var_heap,bes_attrHeap=attr_var_heap,bes_backEnd=be, bes_attr_number=0}
	= (type_var_heap,bes_varHeap,bes_attrHeap,bes_backEnd)

backEndConvertModulesH :: PredefinedSymbols FrontEndSyntaxTree !Int !*TypeVarHeap !*BackEndState -> (!*TypeVarHeap,!*BackEndState)
backEndConvertModulesH predefs {fe_icl = 
	fe_icl =: {	icl_name, icl_functions, icl_common,
				icl_function_indices = {ifi_type_function_indices,ifi_global_function_indices},
				icl_imported_objects, icl_foreign_exports, icl_used_module_numbers, icl_modification_time},
	fe_components, fe_dcls,
	fe_iaci = { iaci_array_and_list_instances
				= {ali_array_first_instance_indices,ali_list_first_instance_indices,
					ali_tail_strict_list_first_instance_indices,ali_unboxed_maybe_first_instance_indices},
				iaci_start_index_generic_classes, iaci_not_exported_generic_classes }
	}
	main_dcl_module_n type_var_heap backEnd
	// sanity check ...
//	| cIclModIndex <> kIclModuleIndex || cPredefinedModuleIndex <> kPredefinedModuleIndex
//		=	undef <<- "backendconvert, backEndConvertModules: module index mismatch"
	// ... sanity check
	#! backEnd = appBackEnd (BESetMainDclModuleN main_dcl_module_n) backEnd
	#! backEnd
		=	appBackEnd (BEDeclareModules (size fe_dcls)) backEnd
	#! backEnd
		=	predefineSymbols fe_dcls.[cPredefinedModuleIndex] predefs backEnd

	#  currentDcl
	   	=	fe_dcls.[main_dcl_module_n]
	#! backEnd
		=	declareCurrentDclModule fe_icl fe_dcls.[main_dcl_module_n] main_dcl_module_n backEnd
	#! backEnd
		=	declareOtherDclModules fe_dcls main_dcl_module_n icl_used_module_numbers backEnd

// tempory hack
	#! backEnd
		=	declareDynamicTemp predefs backEnd

	# (old_cons_vi,cons_vi_ptr,var_heap)
		= remove_VI_ExpandedMemberType_of_List_cons fe_dcls main_dcl_module_n icl_used_module_numbers predefs backEnd.bes_varHeap
	  (old_just_vi,just_vi_ptr,var_heap)
		= remove_VI_ExpandedMemberType_of_Maybe_cJust fe_dcls main_dcl_module_n icl_used_module_numbers predefs var_heap
	  backEnd & bes_varHeap = var_heap

	#! (type_var_heap,backEnd)
		=	defineDclModule main_dcl_module_n fe_dcls.[main_dcl_module_n] type_var_heap backEnd
	#! (type_var_heap,backEnd)
		=	defineOtherDclModules fe_dcls main_dcl_module_n icl_used_module_numbers type_var_heap backEnd

	# backEnd & bes_varHeap
		= restore_VI_ExpandedMemberType old_cons_vi cons_vi_ptr
		 (restore_VI_ExpandedMemberType old_just_vi just_vi_ptr backEnd.bes_varHeap)

	#! backEnd
		=	appBackEnd (BEDeclareIclModule icl_name.id_name icl_modification_time (size icl_functions) (size icl_common.com_type_defs) (size icl_common.com_cons_defs) (size icl_common.com_selector_defs)) backEnd
	#! backEnd
		=	declareFunctionSymbols icl_functions functionIndices
				(ifi_type_function_indices ++ ifi_global_function_indices) (backEnd -*-> "declareFunctionSymbols")
	#! (type_var_heap,backEnd)
		=	declare_icl_common_defs main_dcl_module_n iaci_start_index_generic_classes iaci_not_exported_generic_classes icl_common currentDcl.dcl_common currentDcl.dcl_module_kind type_var_heap backEnd
	#! backEnd
		= declareGeneratedUnboxedRecordInstances
			ali_array_first_instance_indices ali_list_first_instance_indices ali_tail_strict_list_first_instance_indices
			ali_unboxed_maybe_first_instance_indices predefs main_dcl_module_n icl_functions fe_dcls backEnd
	#! backEnd
		=	adjustArrayFunctions ali_array_first_instance_indices predefs main_dcl_module_n icl_functions fe_dcls icl_common.com_instance_defs icl_used_module_numbers backEnd
	#! backEnd
		=	adjustStrictListFunctions ali_list_first_instance_indices ali_tail_strict_list_first_instance_indices predefs fe_dcls icl_used_module_numbers main_dcl_module_n backEnd
	#! backEnd
		=	adjustStrictMaybeFunctions ali_unboxed_maybe_first_instance_indices predefs fe_dcls icl_used_module_numbers main_dcl_module_n backEnd
	#! (rules, backEnd)
		=	convertRules [(index, icl_functions.[index]) \\ (_, index) <- functionIndices] main_dcl_module_n predefined_idents.[PD_DummyForStrictAliasFun] (backEnd -*-> "convertRules")
	# backEnd
		= set_dictionary_field_for_instance_member_functions_for_implementation_module icl_common icl_functions main_dcl_module_n fe_dcls backEnd
	# backEnd
		= set_dictionary_field_for_special_instance_member_functions currentDcl icl_common icl_functions main_dcl_module_n fe_dcls backEnd
	#! backEnd
		=	appBackEnd (BEDefineRules rules) (backEnd -*-> "BEDefineRules")
	#! backEnd
		=	beDefineImportedObjsAndLibs
				(convertStrings [imported.io_name \\ imported <- icl_imported_objects | not imported.io_is_library])
				(convertStrings [imported.io_name \\ imported <- icl_imported_objects | imported.io_is_library])
				(backEnd -*-> "beDefineImportedObjsAndLibs")
	#! backEnd = appBackEnd (convertForeignExports icl_foreign_exports main_dcl_module_n) backEnd
	#! backEnd
		=	markExports fe_dcls.[main_dcl_module_n] dcl_common.com_class_defs dcl_common.com_type_defs icl_common.com_class_defs icl_common.com_type_defs (backEnd -*-> "markExports")
			with
				dcl_common
					=	currentDcl.dcl_common
	# backEnd
		=	foldSt beExportFunction exported_local_type_funs backEnd
		with
			exported_local_type_funs
				| False && currentDcl.dcl_module_kind == MK_None
					=	[]
				// otherwise
					=	flatten [[r.ir_from .. r.ir_to-1]
									\\ r <- [ifi_type_function_indices!!1]]
	# backEnd = bindSpecialIdents predefs icl_used_module_numbers backEnd
	#! backEnd = removeExpandedTypesFromDclModules fe_dcls icl_used_module_numbers backEnd
	= (type_var_heap,backEnd)
	where
		functionIndices
			= function_indices 0 fe_components
		
		function_indices i components
			| i<size components
				= function_indices2 components.[i].component_members i components
				= []

		function_indices2 (ComponentMember member members) i components
			#! inc_i = i+1
			= [(inc_i,member) : function_indices2 members i components]
		function_indices2 (GeneratedComponentMember member _ members) i components
			#! inc_i = i+1
			= [(inc_i,member) : function_indices2 members i components]
		function_indices2 NoComponentMembers i components
			= function_indices (i+1) components

fold2StatesWithIndexA function array s1 s2 :== fold2StatesWithIndexA 0 s1 s2
	where
		fold2StatesWithIndexA index s1 s2
			| index == size array
				= (s1,s2)
				# (s1,s2) = fold2StatesWithIndexA (index+1) s1 s2
				= function index array.[index] s1 s2

declareOtherDclModules :: {#DclModule} Int NumberSet -> BackEnder
declareOtherDclModules dcls main_dcl_module_n used_module_numbers
	=	foldStateWithIndexA declareOtherDclModule dcls
where
	declareOtherDclModule :: ModuleIndex DclModule -> BackEnder
	declareOtherDclModule moduleIndex dclModule
		| moduleIndex == main_dcl_module_n
		|| moduleIndex == cPredefinedModuleIndex
		|| not (inNumberSet moduleIndex used_module_numbers)
			=	identity
			=	declareDclModule moduleIndex dclModule

/*
in transformApplication calls to instances List [#(!)] | U(TS)List u_members are converted to List u_members,
however calling an instance entry of _cons_u or _cons_uts instead of a _cons is incorrect, by temporarily removing
the VI_ExpandedMemberType BESetMemberTypeOfField is not called and these entries are not used for List._cons calls
*/
remove_VI_ExpandedMemberType_of_List_cons :: !{#DclModule} !Int !NumberSet !PredefinedSymbols !*VarHeap -> (!VarInfo,!VarInfoPtr,!*VarHeap)
remove_VI_ExpandedMemberType_of_List_cons dcls main_dcl_module_n icl_used_module_numbers predefs var_heap
	# std_strict_list_module_index = predefs.[PD_StdStrictLists].pds_def
	| std_strict_list_module_index==NoIndex || std_strict_list_module_index==main_dcl_module_n
			|| not (inNumberSet std_strict_list_module_index icl_used_module_numbers)
		= (VI_Empty,nilPtr,var_heap)
	# {com_selector_defs,com_type_defs} = dcls.[std_strict_list_module_index].dcl_common
	// _cons is the first selector in _SystemStrictLists
	# {sd_type_ptr,sd_ident,sd_type_index} = com_selector_defs.[0]
	| sd_ident.id_name<>"_cons" || com_type_defs.[sd_type_index].td_ident.id_name<>"List;"
		= abort "error in function remove_VI_ExpandedMemberType_of_List_cons"
	= remove_VI_ExpandedMemberType sd_type_ptr var_heap

remove_VI_ExpandedMemberType_of_Maybe_cJust :: !{#DclModule} !Int !NumberSet !PredefinedSymbols !*VarHeap -> (!VarInfo,!VarInfoPtr,!*VarHeap)
remove_VI_ExpandedMemberType_of_Maybe_cJust dcls main_dcl_module_n icl_used_module_numbers predefs var_heap
	# std_strict_maybe_module_index = predefs.[PD_StdStrictMaybes].pds_def
	| std_strict_maybe_module_index==NoIndex || std_strict_maybe_module_index==main_dcl_module_n
			|| not (inNumberSet std_strict_maybe_module_index icl_used_module_numbers)
		= (VI_Empty,nilPtr,var_heap)
	# {com_selector_defs,com_type_defs} = dcls.[std_strict_maybe_module_index].dcl_common
	// _cons is the first selector in _SystemStrictLists
	# {sd_type_ptr,sd_ident,sd_type_index} = com_selector_defs.[0]
	| sd_ident.id_name<>"_cJust" || com_type_defs.[sd_type_index].td_ident.id_name<>"Maybe;"
		= abort "error in function remove_VI_ExpandedMemberType_of_Maybe_cJust"
	= remove_VI_ExpandedMemberType sd_type_ptr var_heap

remove_VI_ExpandedMemberType :: !VarInfoPtr !*VarHeap -> (!VarInfo,!VarInfoPtr,!*VarHeap)
remove_VI_ExpandedMemberType sd_type_ptr var_heap
	# (old_cons_vi,var_heap) = readPtr sd_type_ptr var_heap
	= case old_cons_vi of
		VI_ExpandedMemberType _ previous_vi
			# var_heap = writePtr sd_type_ptr previous_vi var_heap
			-> (old_cons_vi,sd_type_ptr,var_heap)
		_
			-> (VI_Empty,nilPtr,var_heap)

restore_VI_ExpandedMemberType :: !VarInfo !VarInfoPtr !*VarHeap -> *VarHeap
restore_VI_ExpandedMemberType old_cons_vi cons_vi_ptr var_heap
	| isNilPtr cons_vi_ptr
		= var_heap
		= writePtr cons_vi_ptr old_cons_vi var_heap

defineOtherDclModules :: {#DclModule} Int NumberSet !*TypeVarHeap !*BackEndState -> (!*TypeVarHeap,!*BackEndState)
defineOtherDclModules dcls main_dcl_module_n used_module_numbers type_var_heap beState
	= fold2StatesWithIndexA defineOtherDclModule dcls type_var_heap beState
where
	defineOtherDclModule :: ModuleIndex DclModule !*TypeVarHeap !*BackEndState -> (!*TypeVarHeap,!*BackEndState)
	defineOtherDclModule moduleIndex dclModule type_var_heap beState
		| moduleIndex == main_dcl_module_n
		|| moduleIndex == cPredefinedModuleIndex
		|| not (inNumberSet moduleIndex used_module_numbers)
			= (type_var_heap, beState)
			= defineDclModule moduleIndex dclModule type_var_heap beState

isSystem :: ModuleKind -> Bool
isSystem MK_System
	=	True
isSystem MK_Module
	=	False
isSystem _
	=	abort "backendconvert:isSystem, unknown module kind"

declareCurrentDclModule :: IclModule DclModule Int -> BackEnder
declareCurrentDclModule _ {dcl_module_kind=MK_None} _
	=	identity
declareCurrentDclModule {icl_common} {dcl_name, dcl_modification_time, dcl_functions, dcl_module_kind, dcl_common} main_dcl_module_n
	=	appBackEnd (BEDeclareDclModule main_dcl_module_n dcl_name.id_name dcl_modification_time  (isSystem dcl_module_kind) (size dcl_functions) (size icl_common.com_type_defs) (size dcl_common.com_cons_defs) (size dcl_common.com_selector_defs))

declareDclModule :: ModuleIndex DclModule -> BackEnder
declareDclModule moduleIndex {dcl_name, dcl_modification_time, dcl_common, dcl_functions, dcl_module_kind}
	=	appBackEnd (BEDeclareDclModule moduleIndex dcl_name.id_name dcl_modification_time (isSystem dcl_module_kind) (size dcl_functions) (size dcl_common.com_type_defs) (size dcl_common.com_cons_defs) (size dcl_common.com_selector_defs))

defineDclModule :: ModuleIndex DclModule !*TypeVarHeap !*BackEndState -> (!*TypeVarHeap,!*BackEndState)
defineDclModule moduleIndex {dcl_name, dcl_common, dcl_functions, dcl_type_funs, dcl_instances} type_var_heap beState
	# (type_var_heap,beState) = declare_dcl_common_defs moduleIndex dcl_common type_var_heap beState
	# beState = declareFunTypes moduleIndex dcl_functions [{ir_from = 0, ir_to = dcl_instances.ir_from}, dcl_type_funs] beState
	= (type_var_heap,beState)

removeExpandedTypesFromDclModules :: {#DclModule} NumberSet -> BackEnder
removeExpandedTypesFromDclModules dcls used_module_numbers
	=	foldStateWithIndexA removeExpandedTypesFromDclModule dcls
where
	removeExpandedTypesFromDclModule :: ModuleIndex DclModule -> BackEnder
	removeExpandedTypesFromDclModule moduleIndex dclModule=:{dcl_functions,dcl_common={com_cons_defs,com_selector_defs}}
		| moduleIndex == cPredefinedModuleIndex || not (inNumberSet moduleIndex used_module_numbers)
			= identity
			= foldStateA removeExpandedTypesFromFunType dcl_functions
			o` foldStateA removeExpandedTypesFromConsType com_cons_defs
			o` foldStateA removeExpandedTypesFromSelectorType com_selector_defs
			where
				removeExpandedTypesFromFunType :: FunType -> BackEnder
				removeExpandedTypesFromFunType {ft_type_ptr}
					= \be0 -> let (ft_type,be) = read_from_var_heap ft_type_ptr be0 in
						(case ft_type of
							VI_ExpandedType expandedType
								->	write_to_var_heap ft_type_ptr VI_Empty	
							_
								->	identity) be

				removeExpandedTypesFromSelectorType :: SelectorDef -> BackEnder
				removeExpandedTypesFromSelectorType {sd_type_ptr}
					= \be0
						= if (not (isNilPtr sd_type_ptr))
							(write_to_var_heap sd_type_ptr VI_Empty be0)
							be0

				removeExpandedTypesFromConsType :: ConsDef -> BackEnder
				removeExpandedTypesFromConsType {cons_type_ptr}
					= \be0
						= if (not (isNilPtr cons_type_ptr))
							(write_to_var_heap cons_type_ptr VI_Empty be0)
							be0

:: DeclVarsInput :== Ident

class declareVars a :: a !DeclVarsInput -> BackEnder

instance declareVars [a] | declareVars a where
	declareVars :: [a] !DeclVarsInput -> BackEnder | declareVars a
	declareVars list dvInput
		=	foldState (flip declareVars dvInput) list

instance declareVars (Ptr VarInfo) where
	declareVars varInfoPtr _
		=	declareVariable BELhsNodeId varInfoPtr "_var???"	// +++ name

instance declareVars FreeVar where
	declareVars :: FreeVar !DeclVarsInput -> BackEnder
	declareVars freeVar _
		=	declareVariable BELhsNodeId freeVar.fv_info_ptr freeVar.fv_ident.id_name

instance declareVars LetBind where
	declareVars :: LetBind !DeclVarsInput -> BackEnder
	declareVars {lb_src=App {app_symb, app_args=[Var _:_]}, lb_dst=freeVar} aliasDummyId
		| not (isNilPtr app_symb.symb_ident.id_info) && app_symb.symb_ident==aliasDummyId
			= identity		// we have an alias. Don't declare the same variable twice
		= declareVariable BERhsNodeId freeVar.fv_info_ptr freeVar.fv_ident.id_name
	declareVars {lb_dst=freeVar} _
		= declareVariable BERhsNodeId freeVar.fv_info_ptr freeVar.fv_ident.id_name

declareVariable :: Int (Ptr VarInfo) {#Char} -> BackEnder
declareVariable lhsOrRhs varInfoPtr name
	= \be0 -> let (variable_sequence_number,be) = getVariableSequenceNumber varInfoPtr be0 in
		beDeclareNodeId variable_sequence_number lhsOrRhs name be

instance declareVars (Optional a) | declareVars a where
	declareVars :: (Optional a) !DeclVarsInput -> BackEnder | declareVars a
	declareVars (Yes x) dvInput
		=	declareVars x dvInput
	declareVars No _
		=	identity

instance declareVars FunctionPattern where
	declareVars :: FunctionPattern !DeclVarsInput -> BackEnder
	declareVars (FP_Algebraic _ freeVars) dvInput
		=	declareVars freeVars dvInput
	declareVars (FP_Variable freeVar) dvInput
		=	declareVars freeVar dvInput

instance declareVars Expression where
	declareVars :: Expression !DeclVarsInput -> BackEnder
	declareVars (Let {let_strict_binds, let_lazy_binds, let_expr}) dvInput
		=	declareVars let_strict_binds dvInput
		o`	declareVars let_lazy_binds dvInput
		o`	declareVars let_expr dvInput
	declareVars (Conditional {if_cond, if_then, if_else}) dvInput
		=	declareVars if_cond dvInput
		o`	declareVars if_then dvInput
		o`	declareVars if_else dvInput
	declareVars (Case caseExpr) dvInput
		=	declareVars caseExpr dvInput
	declareVars (AnyCodeExpr _ outParams _) _
		=	foldState declVar outParams 
	  where
		declVar {bind_dst=freeVar} 
			= declareVariable BERhsNodeId freeVar.fv_info_ptr freeVar.fv_ident.id_name
	declareVars _ _
		=	identity

instance declareVars TransformedBody where
	declareVars :: TransformedBody !DeclVarsInput -> BackEnder
	declareVars {tb_args, tb_rhs} dvInput
		=	declareVars tb_args dvInput
		o`	declareVars tb_rhs dvInput

instance declareVars Case where
	declareVars {case_expr, case_guards, case_default} dvInput
		=	declareVars case_guards dvInput
		o`	declareVars case_default dvInput

instance declareVars CasePatterns where
	declareVars (AlgebraicPatterns _ patterns) dvInput
		=	declareVars patterns dvInput
	declareVars (BasicPatterns _ patterns) dvInput
		=	declareVars patterns dvInput
	declareVars (OverloadedPatterns _ decons_expr patterns) dvInput
		=	declareVars patterns dvInput

instance declareVars AlgebraicPattern where
	declareVars {ap_vars, ap_expr} dvInput
		=	declareVars ap_vars dvInput
		o`	declareVars ap_expr dvInput

instance declareVars BasicPattern where
	declareVars {bp_expr} dvInput
		=	declareVars bp_expr dvInput

class declare a :: ModuleIndex a  -> BackEnder

class declareWithIndex a :: Index ModuleIndex a -> BackEnder

instance declare {#a} | declareWithIndex a & Array {#} a where
	declare :: ModuleIndex  {#a} -> BackEnder | declareWithIndex a & Array {#} a 
	declare moduleIndex array
		=	foldStateWithIndexA (\i -> declareWithIndex i moduleIndex) array

declareFunctionSymbols :: {#FunDef} [(Int, Int)] [IndexRange] *BackEndState -> *BackEndState
declareFunctionSymbols functions functionIndices globalFunctions backEnd
	=	foldl declare backEnd [(functionIndex, componentIndex, functions.[functionIndex]) \\ (componentIndex, functionIndex) <- functionIndices]
	where
		declare backEnd (functionIndex, componentIndex, function)
			=	appBackEnd (BEDeclareFunction (functionName function.fun_ident.id_name functionIndex globalFunctions) 
					function.fun_arity functionIndex componentIndex) backEnd
			where
				functionName :: {#Char} Int [IndexRange] -> {#Char}
				functionName name functionIndex icl_global_functions
					| index_in_ranges functionIndex icl_global_functions
						=	name
						=	(name +++ ";" +++ toString functionIndex)
					where
						index_in_ranges index [{ir_from, ir_to}:ranges]
							= (index>=ir_from && index < ir_to) || index_in_ranges index ranges;
						index_in_ranges index []
							= False

// move to backendsupport
foldStateWithIndexRangeA function frm to array
	:== foldStateWithIndexRangeA frm
	where
		foldStateWithIndexRangeA index
			| index == to
				=	identity
			// otherwise
				=	function index array.[index]
				o`	foldStateWithIndexRangeA (index+1)

folds op l r :== folds l r
	where
		folds [] r = r
		folds [a:x]	r = folds x (op a r)

declareGeneratedUnboxedRecordInstances
		ali_array_first_instance_indices ali_list_first_instance_indices ali_tail_strict_list_first_instance_indices
		ali_unboxed_maybe_first_instance_indices predefs main_dcl_module_n icl_functions fe_dcls backEnd
	#! backEnd
		= declareGeneratedUnboxedRecordInstancesOfClass ali_array_first_instance_indices PD_StdArray PD_ArrayClass predefs main_dcl_module_n icl_functions fe_dcls backEnd
	#! backEnd
		= declareGeneratedUnboxedRecordInstancesOfClass ali_list_first_instance_indices PD_StdStrictLists PD_UListClass predefs main_dcl_module_n icl_functions fe_dcls backEnd
	#! backEnd
		= declareGeneratedUnboxedRecordInstancesOfClass ali_tail_strict_list_first_instance_indices PD_StdStrictLists PD_UTSListClass predefs main_dcl_module_n icl_functions fe_dcls backEnd
	#! backEnd
		= declareGeneratedUnboxedRecordInstancesOfClass ali_unboxed_maybe_first_instance_indices PD_StdStrictMaybes PD_UMaybeClass predefs main_dcl_module_n icl_functions fe_dcls backEnd
	= backEnd

declareGeneratedUnboxedRecordInstancesOfClass :: [Int] Int Int PredefinedSymbols Int {#FunDef} {#DclModule} -> BackEnder
declareGeneratedUnboxedRecordInstancesOfClass [] predef_class_module_index predef_class_index predefs main_dcl_module_n functions dcls
	= identity
declareGeneratedUnboxedRecordInstancesOfClass ali_first_instance_indices predef_class_module_index predef_class_index predefs main_dcl_module_n functions dcls
	#! n_class_members=size dcls.[class_module_index].dcl_common.com_class_defs.[class_index].class_members
	= folds (declareInstances 0 n_class_members) ali_first_instance_indices
	where
		class_module_index = predefs.[predef_class_module_index].pds_def
		class_index = predefs.[predef_class_index].pds_def

		declareInstances :: Int Int Index *BackEndState -> *BackEndState
		declareInstances member_n n_class_members first_member_index backend
			| member_n==n_class_members
				= backend
				# function_index=first_member_index+member_n
				# backend = declareInstance function_index functions.[function_index] backend
				= declareInstances (member_n+1) n_class_members first_member_index backend

		declareInstance :: Index FunDef -> BackEnder
		declareInstance index {fun_ident={id_name}, fun_type=Yes type}
			=	beDeclareRuleType index main_dcl_module_n (id_name +++ ";" +++ toString index)
			o`	beDefineRuleType index main_dcl_module_n (convertTypeAlt index main_dcl_module_n type)

declare_icl_common_defs :: ModuleIndex !Int !{#Bool} CommonDefs CommonDefs !ModuleKind !*TypeVarHeap !*BackEndState -> (!*TypeVarHeap,!*BackEndState)
declare_icl_common_defs moduleIndex start_index_generic_classes not_exported_generic_classes
		{com_cons_defs,com_type_defs,com_selector_defs,com_class_defs,com_member_defs} dcl_common_defs dcl_module_kind type_var_heap bes
	# n_dcl_type_defs = size dcl_common_defs.com_type_defs
	  n_dcl_class_defs = size dcl_common_defs.com_class_defs
	  n_type_defs = size com_type_defs
	  n_class_defs = size com_class_defs
	  first_exported_dictionary_i = n_dcl_type_defs-n_dcl_class_defs
	  first_local_dictionary_i = n_type_defs-(n_class_defs-n_dcl_class_defs)
	  bes = declare moduleIndex com_type_defs bes
	  (type_var_heap,bes)
		= defineTypes 0 first_exported_dictionary_i moduleIndex com_cons_defs com_selector_defs com_type_defs type_var_heap bes
	  (type_var_heap,bes)
		= define_dictionary_types first_exported_dictionary_i 0 n_dcl_type_defs moduleIndex
									com_cons_defs com_selector_defs com_type_defs com_class_defs com_member_defs type_var_heap bes
	  (type_var_heap,bes)
		= defineTypes n_dcl_type_defs first_local_dictionary_i moduleIndex com_cons_defs com_selector_defs com_type_defs type_var_heap bes
	| dcl_module_kind=:MK_None
		= define_dictionary_types first_local_dictionary_i n_dcl_class_defs n_type_defs moduleIndex
										com_cons_defs com_selector_defs com_type_defs com_class_defs com_member_defs type_var_heap bes
		# n_generic_classes = size not_exported_generic_classes
		  start_index_generic_class_types = n_type_defs-n_generic_classes
		  (type_var_heap,bes)
			= define_dictionary_types first_local_dictionary_i n_dcl_class_defs start_index_generic_class_types moduleIndex
										com_cons_defs com_selector_defs com_type_defs com_class_defs com_member_defs type_var_heap bes
		= define_generic_dictionary_types 0 start_index_generic_classes start_index_generic_class_types not_exported_generic_classes moduleIndex
										com_cons_defs com_selector_defs com_type_defs com_class_defs com_member_defs type_var_heap bes

declare_dcl_common_defs :: ModuleIndex CommonDefs !*TypeVarHeap !*BackEndState -> (!*TypeVarHeap,!*BackEndState)
declare_dcl_common_defs moduleIndex {com_cons_defs,com_type_defs,com_selector_defs,com_class_defs,com_member_defs} type_var_heap bes
	# n_type_defs = size com_type_defs
	  n_class_defs = size com_class_defs
	  first_dictionary_i = n_type_defs-n_class_defs
	  bes = declare moduleIndex com_type_defs bes
	  (type_var_heap,bes)
		= defineTypes 0 first_dictionary_i moduleIndex com_cons_defs com_selector_defs com_type_defs type_var_heap bes
	= define_dictionary_types first_dictionary_i 0 n_type_defs moduleIndex
								com_cons_defs com_selector_defs com_type_defs com_class_defs com_member_defs type_var_heap bes

instance declareWithIndex (TypeDef a) where
	declareWithIndex :: Index ModuleIndex (TypeDef a) -> BackEnder
	declareWithIndex typeIndex moduleIndex {td_ident}
		=	appBackEnd (BEDeclareType typeIndex moduleIndex td_ident.id_name)

declareFunTypes :: ModuleIndex {#FunType} [IndexRange] -> BackEnder
declareFunTypes moduleIndex funTypes ranges
		=	foldStateWithIndexA (declareFunType moduleIndex ranges) funTypes

declareFunType :: ModuleIndex [IndexRange] Int FunType -> BackEnder
declareFunType moduleIndex ranges functionIndex {ft_ident,ft_type_ptr,ft_specials}
	= \be0 -> let (vi,be) = read_from_var_heap ft_type_ptr be0 in
					(case vi of
						VI_ExpandedType expandedType
							| not ft_specials=:FSP_ABCCode _
								->	beDeclareRuleType functionIndex moduleIndex (functionName ft_ident.id_name functionIndex ranges)
								o`	beDefineRuleType functionIndex moduleIndex (convertTypeAlt functionIndex moduleIndex expandedType)
								->	be_f ft_specials with
									be_f (FSP_ABCCode abc_code) be
										# be = beDeclareRuleType functionIndex moduleIndex (functionName ft_ident.id_name functionIndex ranges) be
										= beDefineRuleTypeWithCode functionIndex moduleIndex
											(convertTypeAlt functionIndex moduleIndex expandedType)
											(beAbcCodeBlock False (convertStrings abc_code)) be
						_
							->	identity) be
		where
			functionName :: {#Char} Int [IndexRange] -> {#Char}
			functionName name functionIndex ranges 
				| index_in_ranges functionIndex ranges
					=	name
					=	name +++ ";" +++ toString functionIndex
				where
					index_in_ranges index [{ir_from, ir_to}:ranges]
						= (index>=ir_from && index < ir_to) || index_in_ranges index ranges;
					index_in_ranges index []
						= False

defineTypes :: !Int !Int ModuleIndex {#ConsDef} {#SelectorDef} {#CheckedTypeDef} !*TypeVarHeap !*BackEndState -> (!*TypeVarHeap,!*BackEndState)
defineTypes type_i type_i_stop moduleIndex constructors selectors types type_var_heap bes
	| type_i<type_i_stop
		# (type_var_heap,bes) = defineType moduleIndex constructors selectors type_i types.[type_i] type_var_heap bes
		= defineTypes (type_i+1) type_i_stop moduleIndex constructors selectors types type_var_heap bes
		= (type_var_heap,bes)

define_dictionary_types :: !Int !Int !Int ModuleIndex {#ConsDef} {#SelectorDef} {#CheckedTypeDef} {#ClassDef} {#MemberDef} !*TypeVarHeap !*BackEndState -> (!*TypeVarHeap,!*BackEndState)
define_dictionary_types type_i class_i type_i_stop moduleIndex constructors selectors types class_defs member_defs type_var_heap bes
	| type_i<type_i_stop
		# (type_var_heap,bes)
			= define_dictionary_type moduleIndex constructors selectors type_i types.[type_i] class_defs.[class_i] member_defs type_var_heap bes
		= define_dictionary_types (type_i+1) (class_i+1) type_i_stop moduleIndex constructors selectors types class_defs member_defs type_var_heap bes
		= (type_var_heap,bes)

define_generic_dictionary_types :: !Int !Int !Int !{#Bool} ModuleIndex {#ConsDef} {#SelectorDef} {#CheckedTypeDef} {#ClassDef} {#MemberDef} !*TypeVarHeap !*BackEndState -> (!*TypeVarHeap,!*BackEndState)
define_generic_dictionary_types generic_class_i start_index_generic_classes start_index_generic_class_types not_exported_generic_classes moduleIndex constructors selectors types class_defs member_defs type_var_heap bes
	| generic_class_i<size not_exported_generic_classes
		# class_i = start_index_generic_classes+generic_class_i
		# type_i = start_index_generic_class_types+generic_class_i
		| not_exported_generic_classes.[generic_class_i]
			# (type_var_heap,bes)
				= define_dictionary_type moduleIndex constructors selectors type_i types.[type_i] class_defs.[class_i] member_defs type_var_heap bes
			= define_generic_dictionary_types (generic_class_i+1) start_index_generic_classes start_index_generic_class_types not_exported_generic_classes moduleIndex constructors selectors types class_defs member_defs type_var_heap bes
			# (type_var_heap,bes)
				= define_exported_generic_dictionary_type moduleIndex constructors selectors type_i types.[type_i] class_defs.[class_i] member_defs type_var_heap bes
			= define_generic_dictionary_types (generic_class_i+1) start_index_generic_classes start_index_generic_class_types not_exported_generic_classes moduleIndex constructors selectors types class_defs member_defs type_var_heap bes
		= (type_var_heap,bes)

convertTypeLhs :: ModuleIndex Index TypeAttribute [ATypeVar] !*TypeVarHeap !*BackEndState
						  -> (!BETypeSymbolP,!BEAttribution, !*TypeVarHeap,!*BackEndState)
convertTypeLhs moduleIndex typeIndex attribute args type_var_heap bes
	= convertTypeDefToFlatType (beTypeSymbol typeIndex moduleIndex) attribute args type_var_heap bes

convertTypeDefToFlatType :: (BEMonad BETypeSymbolP) TypeAttribute [ATypeVar] !*TypeVarHeap !*BackEndState
										   -> (!BETypeSymbolP,!BEAttribution,!*TypeVarHeap,!*BackEndState)
convertTypeDefToFlatType type_symbol_m attribute args type_var_heap bes
	# (a1,bes) = type_symbol_m bes
	  (a2,bes) = convertAttribution attribute bes
	  type_var_heap = numberLhsTypeVars args 0 type_var_heap
	= (a1,a2,type_var_heap,bes)

numberLhsTypeVars :: [ATypeVar] Int !*TypeVarHeap -> *TypeVarHeap
numberLhsTypeVars [{atv_variable={tv_info_ptr}}:x] arg_n type_var_heap
	# type_var_heap = writePtr tv_info_ptr (TVI_TypeVarArgN arg_n) type_var_heap
	= numberLhsTypeVars x (arg_n+1) type_var_heap
numberLhsTypeVars [] arg_n type_var_heap
	= type_var_heap

remove_TVI_TypeVarArgN_in_args :: [ATypeVar] !*TypeVarHeap -> *TypeVarHeap
remove_TVI_TypeVarArgN_in_args [{atv_variable={tv_info_ptr}}:args] type_var_heap
	# type_var_heap = writePtr tv_info_ptr TVI_Empty type_var_heap
	= remove_TVI_TypeVarArgN_in_args args type_var_heap
remove_TVI_TypeVarArgN_in_args [] type_var_heap
	= type_var_heap

defineType :: ModuleIndex {#ConsDef} {#SelectorDef} Index CheckedTypeDef !*TypeVarHeap !*BackEndState -> (!*TypeVarHeap,!*BackEndState)
defineType moduleIndex constructors _ typeIndex {td_ident, td_attribute, td_args, td_rhs=AlgType constructorSymbols} type_var_heap be
	# (symbol_p,type_attribute,type_var_heap,be) = convertTypeLhs moduleIndex typeIndex td_attribute td_args type_var_heap be
	  (constructors,type_var_heap,be)
		= convertConstructors typeIndex td_ident.id_name moduleIndex constructors constructorSymbols type_var_heap be
	  be = appBackEnd (BEDefineAlgebraicType symbol_p type_attribute constructors) be
	  type_var_heap = remove_TVI_TypeVarArgN_in_args td_args type_var_heap
	= (type_var_heap,be)
defineType moduleIndex constructors selectors typeIndex {td_attribute, td_args, td_rhs=RecordType {rt_constructor, rt_fields, rt_is_boxed_record}, td_fun_index} type_var_heap be
	# constructorIndex = rt_constructor.ds_index
	  constructorDef = constructors.[constructorIndex]
	  (symbol_p,type_attribute,type_var_heap,be)
		= if (td_fun_index<>NoIndex)
			(convertTypeLhs moduleIndex typeIndex td_attribute td_args type_var_heap be)
			// define the record without marking, to prevent code generation for many unused generic dictionaries
			(convertTypeDefToFlatType (beTypeSymbolNoMark typeIndex moduleIndex) td_attribute td_args type_var_heap be)
	  (fields,type_var_heap,be)
		= convertSelectors moduleIndex selectors rt_fields constructorDef.cons_type.st_args_strictness type_var_heap be
	  (constructorType,be) = constructorTypeFunction constructorDef be
	  (type_arg_p,type_var_heap,be) = convertTypeDefAnnotatedTypeArgs constructorType.st_args constructorType.st_args_strictness type_var_heap be
	  be = appBackEnd (BEDefineRecordType symbol_p type_attribute moduleIndex constructorIndex type_arg_p (if rt_is_boxed_record 1 0) fields) be
	  type_var_heap = remove_TVI_TypeVarArgN_in_args td_args type_var_heap
	= (type_var_heap,be)
	where
		constructorTypeFunction constructorDef bes
			# (cons_type,bes) = read_from_var_heap constructorDef.cons_type_ptr bes
			= case cons_type of
					VI_ExpandedType expandedType
						->	(expandedType,bes)
					_
						->	(constructorDef.cons_type,bes)
defineType moduleIndex _ _ typeIndex {td_rhs=AbstractType _} type_var_heap be
 	# (symbol,be) = beTypeSymbol typeIndex moduleIndex be
	  be = appBackEnd (BEAbstractType symbol) be
 	= (type_var_heap,be)
defineType moduleIndex _ _ typeIndex {td_rhs=AbstractSynType _ _} type_var_heap be
 	# (symbol,be) = beTypeSymbol typeIndex moduleIndex be
	  be = appBackEnd (BEAbstractType symbol) be
 	= (type_var_heap,be)
defineType moduleIndex constructors _ typeIndex {td_ident, td_attribute, td_args, td_rhs=ExtensibleAlgType constructorSymbols} type_var_heap be
	# (symbol_p,type_attribute,type_var_heap,be) = convertTypeLhs moduleIndex typeIndex td_attribute td_args type_var_heap be
	  (constructors,type_var_heap,be)
		= convertConstructors typeIndex td_ident.id_name moduleIndex constructors constructorSymbols type_var_heap be
	  be = appBackEnd (BEDefineExtensibleAlgebraicType symbol_p type_attribute constructors) be
	  type_var_heap = remove_TVI_TypeVarArgN_in_args td_args type_var_heap
	= (type_var_heap,be)
defineType moduleIndex constructors _ typeIndex {td_ident, td_attribute, td_args, td_rhs=AlgConses constructorSymbols _} type_var_heap be
	# (symbol_p,type_attribute,type_var_heap,be) = convertTypeLhs moduleIndex typeIndex td_attribute td_args type_var_heap be
	  (constructors,type_var_heap,be)
		= convertConstructors typeIndex td_ident.id_name moduleIndex constructors constructorSymbols type_var_heap be
	  be = appBackEnd (BEDefineExtensibleAlgebraicType symbol_p type_attribute constructors) be
	  type_var_heap = remove_TVI_TypeVarArgN_in_args td_args type_var_heap
	= (type_var_heap,be)
defineType moduleIndex _ _ typeIndex {td_rhs=AbstractNewType _ _} type_var_heap be
	# (symbol,be) = beTypeSymbol typeIndex moduleIndex be
	  be = appBackEnd (BEAbstractType symbol) be
	= (type_var_heap,be)
defineType _ _ _ _ _ type_var_heap be
	= (type_var_heap,be)

define_dictionary_type :: ModuleIndex {#ConsDef} {#SelectorDef} Index CheckedTypeDef ClassDef {#MemberDef}
						!*TypeVarHeap !*BackEndState -> (!*TypeVarHeap,!*BackEndState)
define_dictionary_type moduleIndex constructors selectors typeIndex
						{td_attribute,td_args,td_rhs=RecordType {rt_constructor,rt_fields,rt_is_boxed_record},td_fun_index}
						{class_members} member_defs type_var_heap bes
	# constructorIndex = rt_constructor.ds_index
	  constructorDef = constructors.[constructorIndex]
	  (symbol_p,type_attribute,type_var_heap,bes)
		= if (td_fun_index<>NoIndex)
			(convertTypeLhs moduleIndex typeIndex td_attribute td_args type_var_heap bes)
			// define the record without marking, to prevent code generation for many unused generic dictionaries
			(convertTypeDefToFlatType (beTypeSymbolNoMark typeIndex moduleIndex) td_attribute td_args type_var_heap bes)
	  (fields,type_var_heap,bes)
		= convert_dictionary_selectors moduleIndex selectors rt_fields (size class_members) constructorDef.cons_type.st_args_strictness member_defs type_var_heap bes
	  (constructorType,bes) = constructorTypeFunction constructorDef bes
	  (type_arg_p,type_var_heap,bes) = convertTypeDefAnnotatedTypeArgs constructorType.st_args constructorType.st_args_strictness type_var_heap bes
	  bes = appBackEnd (BEDefineRecordType symbol_p type_attribute moduleIndex constructorIndex type_arg_p (if rt_is_boxed_record 1 0) fields) bes
	  type_var_heap = remove_TVI_TypeVarArgN_in_args td_args type_var_heap
	= (type_var_heap,bes)

define_exported_generic_dictionary_type :: ModuleIndex {#ConsDef} {#SelectorDef} Index CheckedTypeDef ClassDef {#MemberDef}
						!*TypeVarHeap !*BackEndState -> (!*TypeVarHeap,!*BackEndState)
define_exported_generic_dictionary_type moduleIndex constructors selectors typeIndex
						{td_attribute,td_args,td_rhs=RecordType {rt_constructor,rt_fields,rt_is_boxed_record},td_fun_index}
						{class_members} member_defs type_var_heap bes
	# constructorIndex = rt_constructor.ds_index
	  constructorDef = constructors.[constructorIndex]
	  (symbol_p,type_attribute,type_var_heap,bes)
		= if (td_fun_index<>NoIndex)
			(convertTypeLhs moduleIndex typeIndex td_attribute td_args type_var_heap bes)
			// define the record without marking, to prevent code generation for many unused generic dictionaries
			(convertTypeDefToFlatType (beTypeSymbolNoMark typeIndex moduleIndex) td_attribute td_args type_var_heap bes)
	  (fields,type_var_heap,bes)
		= convert_exported_generic_dictionary_selectors moduleIndex selectors rt_fields (size class_members) constructorDef.cons_type.st_args_strictness member_defs type_var_heap bes
	  (constructorType,bes) = constructorTypeFunction constructorDef bes
	  (type_arg_p,type_var_heap,bes) = convertTypeDefAnnotatedTypeArgs constructorType.st_args constructorType.st_args_strictness type_var_heap bes
	  bes = appBackEnd (BEDefineRecordType symbol_p type_attribute moduleIndex constructorIndex type_arg_p (if rt_is_boxed_record 1 0) fields) bes
	  type_var_heap = remove_TVI_TypeVarArgN_in_args td_args type_var_heap
	= (type_var_heap,bes)

constructorTypeFunction constructorDef bes
	# (cons_type,bes) = read_from_var_heap constructorDef.cons_type_ptr bes
	= case cons_type of
			VI_ExpandedType expandedType
				->	(expandedType,bes)
			_
				->	(constructorDef.cons_type,bes)

convertConstructors :: Int {#Char} ModuleIndex {#ConsDef} [DefinedSymbol] !*TypeVarHeap !*BackEndState
												  -> (!BEConstructorListP,!*TypeVarHeap,!*BackEndState)
convertConstructors typeIndex typeName moduleIndex cons_defs symbols type_var_heap beState
	= convert_constructors symbols type_var_heap beState
where
	convert_constructors [a:x] type_var_heap beState
		# (constructors,type_var_heap,beState) = convert_constructors x type_var_heap beState
		= convertConstructor typeIndex typeName moduleIndex cons_defs a constructors type_var_heap beState
	convert_constructors [] type_var_heap beState
		# (constructors,beState) = beNoConstructors beState
		= (constructors,type_var_heap,beState)

convertConstructor :: Int {#Char} ModuleIndex {#ConsDef} DefinedSymbol !BEConstructorListP !*TypeVarHeap !*BackEndState
																   -> (!BEConstructorListP,!*TypeVarHeap,!*BackEndState)
convertConstructor typeIndex typeName moduleIndex constructorDefs {ds_index} constructors type_var_heap bes
	# (constructorType,bes) = constructorTypeFunction bes
	  bes = appBackEnd (BEDeclareConstructor ds_index moduleIndex constructorDef.cons_ident.id_name) bes // +++ remove declare
	  (atype_args,type_var_heap,bes) = convertTypeDefAnnotatedTypeArgs constructorType.st_args constructorType.st_args_strictness type_var_heap bes
	  (constructor_symbol,bes) = beConstructorSymbol moduleIndex ds_index bes
	  (constructors,bes) = accBackEnd (BEConstructorList constructor_symbol atype_args constructors) bes
	= (constructors,type_var_heap,bes)
	where
		constructorDef
			=	constructorDefs.[ds_index]
		constructorTypeFunction bes
			# (cons_type,bes) = read_from_var_heap constructorDef.cons_type_ptr bes
			= case cons_type of
				VI_ExpandedType expandedType
					->	(expandedType,bes)
				_
					->	(constructorDef.cons_type,bes)

convertSelectors :: ModuleIndex {#SelectorDef} {#FieldSymbol} StrictnessList !*TypeVarHeap !*BackEndState
														   -> (!BEFieldListP,!*TypeVarHeap,!*BackEndState)
convertSelectors moduleIndex selectors symbols strictness type_var_heap bes
	= convert_selectors 0 type_var_heap bes
where
	convert_selectors index type_var_heap bes
		| index == size symbols
			# (field_list_p,bes) = accBackEnd BENoFields bes
			= (field_list_p,type_var_heap,bes)
			# (field_list_p,type_var_heap,bes) = convert_selectors (index+1) type_var_heap bes
			= convertSelector moduleIndex selectors (arg_is_strict index strictness) symbols.[index] field_list_p type_var_heap bes

convertSelector :: ModuleIndex {#SelectorDef} Bool FieldSymbol !BEFieldListP !*TypeVarHeap !*BackEndState -> (!BEFieldListP,!*TypeVarHeap,!*BackEndState)
convertSelector moduleIndex selectorDefs is_strict {fs_index} field_list_p type_var_heap bes
	# selectorDef = selectorDefs.[fs_index]
	  (field_type,bes) = selectorTypeFunction selectorDef bes
	  (type_node_p,type_var_heap,bes) = convertTypeDefAnnotAndTypeNode (if is_strict AN_Strict AN_None) field_type type_var_heap bes
	  (field_list_p,bes) = accBackEnd (BEFieldList fs_index moduleIndex selectorDef.sd_ident.id_name type_node_p field_list_p) bes
	= (field_list_p,type_var_heap,bes)
	where
		selectorTypeFunction :: !SelectorDef !*BackEndState -> *(!AType,!*BackEndState)
		selectorTypeFunction {sd_type_ptr,sd_type} bes
			# (sd_type_in_ptr,bes) = read_from_var_heap sd_type_ptr bes
			= case sd_type_in_ptr of
				VI_ExpandedType {st_result}
					->	(st_result,bes)
				_
					->	(sd_type.st_result,bes)

convert_dictionary_selectors :: ModuleIndex {#SelectorDef} {#FieldSymbol} !Int StrictnessList {#MemberDef} !*TypeVarHeap !*BackEndState -> (!BEFieldListP,!*TypeVarHeap,!*BackEndState)
convert_dictionary_selectors moduleIndex selectors symbols size_class_members strictness member_defs type_var_heap bes
	= convert_dictionary_selectors 0 type_var_heap bes
where
	convert_dictionary_selectors index type_var_heap bes
		| index == size symbols
			# (field_list_p,bes) = accBackEnd BENoFields bes
			= (field_list_p,type_var_heap,bes)
			# (field_list_p,type_var_heap,bes) = convert_dictionary_selectors (index+1) type_var_heap bes
			| index<size_class_members
				= convertMemberSelector moduleIndex selectors (arg_is_strict index strictness) symbols.[index] field_list_p type_var_heap bes
				= convertSelector moduleIndex selectors (arg_is_strict index strictness) symbols.[index] field_list_p type_var_heap bes

convert_exported_generic_dictionary_selectors :: ModuleIndex {#SelectorDef} {#FieldSymbol} !Int StrictnessList {#MemberDef} !*TypeVarHeap !*BackEndState -> (!BEFieldListP,!*TypeVarHeap,!*BackEndState)
convert_exported_generic_dictionary_selectors moduleIndex selectors symbols size_class_members strictness member_defs type_var_heap bes
	= convert_dictionary_selectors 0 type_var_heap bes
where
	convert_dictionary_selectors index type_var_heap bes
		| index == size symbols
			# (field_list_p,bes) = accBackEnd BENoFields bes
			= (field_list_p,type_var_heap,bes)
			# (field_list_p,type_var_heap,bes) = convert_dictionary_selectors (index+1) type_var_heap bes
			| index<size_class_members
				= convert_exported_generic_member_selector moduleIndex selectors (arg_is_strict index strictness) symbols.[index] field_list_p type_var_heap bes
				= convertSelector moduleIndex selectors (arg_is_strict index strictness) symbols.[index] field_list_p type_var_heap bes

remove_first_arg_type expanded_member_type=:{st_args=[_:args],st_arity,st_args_strictness}
	= {expanded_member_type & st_args = args, st_arity = st_arity-1, st_args_strictness = remove_first_n 1 st_args_strictness}

convertMemberSelector :: ModuleIndex {#SelectorDef} Bool FieldSymbol !BEFieldListP !*TypeVarHeap !*BackEndState -> (!BEFieldListP,!*TypeVarHeap,!*BackEndState)
convertMemberSelector moduleIndex selectorDefs is_strict {fs_index} field_list_p type_var_heap bes
	# selectorDef = selectorDefs.[fs_index]
	  (field_type,optional_type_alt_p,bes) = selectorTypeFunction selectorDef bes
	  (field_type,type_var_heap,bes) = convertTypeDefAnnotAndTypeNode (if is_strict AN_Strict AN_None) field_type type_var_heap bes
	  (field_list_p,bes) = accBackEnd (BEFieldList fs_index moduleIndex selectorDef.sd_ident.id_name field_type field_list_p) bes
	= case optional_type_alt_p of
		No
			-> (field_list_p,type_var_heap,bes)
		Yes type_alt_p
			-> (field_list_p,type_var_heap,appBackEnd (BESetMemberTypeOfField fs_index moduleIndex type_alt_p) bes)
	where
		selectorTypeFunction :: !SelectorDef !*BackEndState -> *(!AType,!Optional BETypeAltP,!*BackEndState)
		selectorTypeFunction {sd_type_ptr,sd_type} bes
			# (sd_type_in_ptr,bes) = read_from_var_heap sd_type_ptr bes
			= case sd_type_in_ptr of
				VI_ExpandedType {st_result}
					->	(st_result,No,bes)
				VI_ExpandedMemberType expanded_member_type (VI_ExpandedType {st_result})
					# (dont_care_symbol_p,bes) = accBackEnd BEDontCareDefinitionSymbol bes
					  expanded_member_type = remove_first_arg_type expanded_member_type
					  (type_alt_p,bes) = convertTypeAltForSymbolP dont_care_symbol_p expanded_member_type bes
					->	(st_result,Yes type_alt_p,bes)
				VI_ExpandedMemberType expanded_member_type VI_Empty
					# (dont_care_symbol_p,bes) = accBackEnd BEDontCareDefinitionSymbol bes
					  expanded_member_type = remove_first_arg_type expanded_member_type
					  (type_alt_p,bes) = convertTypeAltForSymbolP dont_care_symbol_p expanded_member_type bes
					->	(sd_type.st_result,Yes type_alt_p,bes)
				_
					->	(sd_type.st_result,No,bes)

convert_exported_generic_member_selector :: ModuleIndex {#SelectorDef} Bool FieldSymbol !BEFieldListP !*TypeVarHeap !*BackEndState -> (!BEFieldListP,!*TypeVarHeap,!*BackEndState)
convert_exported_generic_member_selector moduleIndex selectorDefs is_strict {fs_index} field_list_p type_var_heap bes
	# selectorDef = selectorDefs.[fs_index]
	  (field_type,optional_type_alt_p,bes) = selectorTypeFunction selectorDef bes
	  (field_type,type_var_heap,bes) = convertTypeDefAnnotAndTypeNode (if is_strict AN_Strict AN_None) field_type type_var_heap bes
	  (field_list_p,bes) = accBackEnd (BEFieldList fs_index moduleIndex selectorDef.sd_ident.id_name field_type field_list_p) bes
	= case optional_type_alt_p of
		No
			-> (field_list_p,type_var_heap,bes)
		Yes type_alt_p
			-> (field_list_p,type_var_heap,appBackEnd (BESetMemberTypeOfField fs_index moduleIndex type_alt_p) bes)
	where
		selectorTypeFunction :: !SelectorDef !*BackEndState -> *(!AType,!Optional BETypeAltP,!*BackEndState)
		selectorTypeFunction {sd_type_ptr,sd_type} bes
			# (sd_type_in_ptr,bes) = read_from_var_heap sd_type_ptr bes
			= case sd_type_in_ptr of
				VI_ExpandedType {st_result}
					->	(st_result,No,bes)
				VI_ExpandedMemberType expanded_member_type (VI_ExpandedType {st_result})
					# (dont_care_symbol_p,bes) = accBackEnd BEDontCareDefinitionSymbol bes
					  expanded_member_type = remove_first_arg_type expanded_member_type
					  (type_alt_p,bes) = convertExportedTypeAltForSymbolP dont_care_symbol_p expanded_member_type bes
					->	(st_result,Yes type_alt_p,bes)
				VI_ExpandedMemberType expanded_member_type VI_Empty
					# (dont_care_symbol_p,bes) = accBackEnd BEDontCareDefinitionSymbol bes
					  expanded_member_type = remove_first_arg_type expanded_member_type
					  (type_alt_p,bes) = convertExportedTypeAltForSymbolP dont_care_symbol_p expanded_member_type bes
					->	(sd_type.st_result,Yes type_alt_p,bes)
				_
					->	(sd_type.st_result,No,bes)

declareDynamicTemp :: PredefinedSymbols -> BackEnder
declareDynamicTemp predefs
	=	appBackEnd (BEDeclareDynamicTypeSymbol predefs.[PD_StdDynamic].pds_def predefs.[PD_Dyn_DynamicTemp].pds_def)

^= v be
	:== (v,be)

@^ f f1 be
	# (v1,be) = f1 be
	:== f v1 be

@^^ f f1 f2 be
	# (v1,be) = f1 be
	  (v2,be) = f2 be
	:== f v1 v2 be

@^^^ f f1 f2 f3 be
	# (v1,be) = f1 be
	  (v2,be) = f2 be
	  (v3,be) = f3 be
	:== f v1 v2 v3 be

@^&^ f f1 v2 f3 be
	# (v1,be) = f1 be
	  (v3,be) = f3 be
	:== f v1 v2 v3 be

predefineSymbols :: DclModule PredefinedSymbols -> BackEnder
predefineSymbols {dcl_common} predefs
	=	appBackEnd (BEDeclarePredefinedModule (size dcl_common.com_type_defs) (size dcl_common.com_cons_defs))
	o`	foldState predefine_list_type list_types
	o`	foldState predefineType types
	o`	foldState predefine_maybe_type maybe_types
	o`	foldState predefine_list_constructor list_constructors
	o`	foldState predefineConstructor constructors
	o`	foldState predefine_maybe_constructor maybe_constructors
	o`	define_unit_type
	where
		list_types :: [(Int,Int,Int)]
		list_types
			=	[	(PD_ListType,0,0),
					(PD_StrictListType,2,0),
					(PD_UnboxedListType,3,0),
					(PD_TailStrictListType,0,1),
					(PD_StrictTailStrictListType,2,1),
					(PD_UnboxedTailStrictListType,3,1)
				]

		predefine_list_type (index,head_strictness,tail_strictness)
			| predefs.[index].pds_def == NoIndex
				=	abort "backendconvert, predefineSymbols predef is not a type"
			=	appBackEnd (BEPredefineListTypeSymbol predefs.[index].pds_def cPredefinedModuleIndex BEListType head_strictness tail_strictness) // id

		types :: [(Int, Int, BESymbKind)]
		types
			=	[	(PD_LazyArrayType, 1, BEArrayType)
				,	(PD_StrictArrayType, 1, BEStrictArrayType)
				,	(PD_UnboxedArrayType, 1, BEUnboxedArrayType)
				,	(PD_PackedArrayType, 1, BEPackedArrayType)
				:	[(index, index-PD_Arity2TupleType+2, BETupleType) \\ index <- [PD_Arity2TupleType..PD_Arity32TupleType]]
				]

		predefineType (index, arity, symbolKind)
			| predefs.[index].pds_def == NoIndex
				=	abort "backendconvert, predefineSymbols predef is not a type"
			=	appBackEnd (BEPredefineTypeSymbol arity predefs.[index].pds_def cPredefinedModuleIndex symbolKind)

		list_constructors :: [(Int,BESymbKind,Int,Int)]
		list_constructors
			=	[	(PD_NilSymbol, BENilSymb,0,0),
					(PD_StrictNilSymbol, BENilSymb,2,0),
					(PD_UnboxedNilSymbol, BENilSymb,4/*3*/,0),
					(PD_TailStrictNilSymbol, BENilSymb,0,1),
					(PD_StrictTailStrictNilSymbol, BENilSymb,2,1),
					(PD_UnboxedTailStrictNilSymbol, BENilSymb,4/*3*/,1),
					(PD_OverloadedNilSymbol, BENilSymb,0,0),
					(PD_ConsSymbol, BEConsSymb,0,0),
					(PD_StrictConsSymbol, BEConsSymb,2,0),
					(PD_UnboxedConsSymbol, BEConsSymb,3,0),
					(PD_TailStrictConsSymbol, BEConsSymb,0,1),
					(PD_StrictTailStrictConsSymbol, BEConsSymb,2,1),
					(PD_UnboxedTailStrictConsSymbol, BEConsSymb,3,1),
					(PD_OverloadedConsSymbol, BEConsSymb,1,0)
				]

		predefine_list_constructor (index,symbolKind,head_strictness,tail_strictness)
			| predefs.[index].pds_def == NoIndex
				=	abort "backendconvert, predefineSymbols predef is not a constructor"
			= appBackEnd (BEPredefineListConstructorSymbol predefs.[index].pds_def cPredefinedModuleIndex symbolKind head_strictness tail_strictness) // id
		
		constructors :: [(Int, Int, BESymbKind)]
		constructors
			=	[(index, index-PD_Arity2TupleSymbol+2, BETupleSymb) \\ index <- [PD_Arity2TupleSymbol..PD_Arity32TupleSymbol]]
 
		predefineConstructor (index, arity, symbolKind)
			| predefs.[index].pds_def == NoIndex
				=	abort "backendconvert, predefineSymbols predef is not a constructor"
			=	appBackEnd (BEPredefineConstructorSymbol arity predefs.[index].pds_def cPredefinedModuleIndex symbolKind)

		maybe_types :: [(Int,Int)]
		maybe_types = [(PD_MaybeType,0), (PD_StrictMaybeType,2), (PD_UnboxedMaybeType,3)]

		predefine_maybe_type (index,head_strictness)
			# pds_def = predefs.[index].pds_def
			| pds_def == NoIndex
				=	abort "backendconvert, predefineSymbols predef is not a type"
			=	appBackEnd (BEPredefineMaybeTypeSymbol pds_def cPredefinedModuleIndex head_strictness)

		maybe_constructors :: [(Int,BESymbKind,Int)]
		maybe_constructors
			=	[	(PD_NothingSymbol, BENothingSymb,0),
					(PD_StrictNothingSymbol, BENothingSymb,2),
					(PD_UnboxedNothingSymbol, BENothingSymb,4/*3*/),
					(PD_OverloadedNothingSymbol, BENothingSymb,0),
					(PD_JustSymbol, BEJustSymb,0),
					(PD_StrictJustSymbol, BEJustSymb,2),
					(PD_UnboxedJustSymbol, BEJustSymb,3),
					(PD_OverloadedJustSymbol, BEJustSymb,1)
				]

		predefine_maybe_constructor (index,symbolKind,head_strictness)
			# pds_def = predefs.[index].pds_def
			| pds_def == NoIndex
				=	abort "backendconvert, predefineSymbols predef is not a constructor"
			= appBackEnd (BEPredefineMaybeConstructorSymbol pds_def cPredefinedModuleIndex symbolKind head_strictness)

		define_unit_type
			# constructor_symbol_be_f = BEConstructorSymbol predefs.[PD_UnitConsSymbol].pds_def cPredefinedModuleIndex
			  constructors_be_f = @^^^ BEConstructorList constructor_symbol_be_f BENoTypeArgs BENoConstructors
			  type_symbol_be_f = BETypeSymbol PD_UnitTypeIndex cPredefinedModuleIndex
			= appBackEnd
				(  BEDeclareConstructor predefs.[PD_UnitConsSymbol].pds_def cPredefinedModuleIndex "_Unit"
				o` BEDeclareType PD_UnitTypeIndex cPredefinedModuleIndex "_Unit"
				o` @^&^ BEDefineAlgebraicType type_symbol_be_f BENoUniAttr constructors_be_f)

bindSpecialIdents :: PredefinedSymbols NumberSet -> BackEnder
bindSpecialIdents predefs usedModules
	=	foldState (bindSpecialModule predefs usedModules) specialModules
	where
		bindSpecialModule :: PredefinedSymbols NumberSet (Int, BESpecialIdentIndex, [(Int, BESpecialIdentIndex)]) -> BackEnder
		bindSpecialModule predefs usedModules (predefIndex, specialIdentIndex, specialFunctions)
			| moduleIndex == NoIndex || not (inNumberSet moduleIndex usedModules)
				=	identity
			// otherwise
				=	beBindSpecialModule specialIdentIndex moduleIndex
				o`	foldState (bindSpecialFunction predefs) specialFunctions
				where
					predef
						=	predefs.[predefIndex]
					moduleIndex
						=	predef.pds_def

		bindSpecialFunction :: PredefinedSymbols (Int, BESpecialIdentIndex) -> BackEnder
		bindSpecialFunction predefs (predefIndex, specialIdentIndex)
			| predef.pds_def == NoIndex
				=	identity
			// otherwise
				=	beBindSpecialFunction specialIdentIndex predef.pds_def predef.pds_module
				where
					predef
						=	predefs.[predefIndex]

		specialModules
			=	[	(PD_StdMisc, BESpecialIdentStdMisc,
						[	(PD_abort,	BESpecialIdentAbort)
						,	(PD_undef,	BESpecialIdentUndef)
						]
					)
				,	(PD_StdBool, BESpecialIdentStdBool,
						[	(PD_AndOp,	BESpecialIdentAnd)
						,	(PD_OrOp,	BESpecialIdentOr)
						]
					)
				]

adjustStrictListFunctions :: [Int] [Int] {#PredefinedSymbol} {#DclModule} NumberSet Int *BackEndState -> *BackEndState;
adjustStrictListFunctions list_first_instance_indices tail_strict_list_first_instance_indices predefs dcls used_module_numbers main_dcl_module_n backEnd
	| std_strict_list_module_index==NoIndex || not (inNumberSet std_strict_list_module_index used_module_numbers)
		|| std_strict_list_module_index==main_dcl_module_n
		= backEnd
		# std_strict_lists_instances=std_strict_lists.dcl_common.com_instance_defs
		# backEnd = adjust_strict_list_instances 0 std_strict_lists_instances backEnd
		# std_strict_lists_nil_functions=std_strict_lists.dcl_functions
		# first_instance_index=std_strict_lists.dcl_instances.ir_from;
		# backEnd=adjust_overloaded_nil_functions 0 first_instance_index std_strict_lists_nil_functions backEnd

		# std_list_common_defs = std_strict_lists.dcl_common
		  indexUListClass = predefs.[PD_UListClass].pds_def
		  dictionaryIndexUListClass = std_list_common_defs.com_class_defs.[indexUListClass].class_dictionary.ds_index
		  (RecordType {rt_fields}) = std_list_common_defs.com_type_defs.[dictionaryIndexUListClass].td_rhs

		  backEnd=appBackEnd (adjustRecordListInstances list_first_instance_indices rt_fields) backEnd

		  indexUTSListClass = predefs.[PD_UTSListClass].pds_def
		  dictionaryIndexUTSListClass = std_list_common_defs.com_class_defs.[indexUTSListClass].class_dictionary.ds_index
		  (RecordType {rt_fields}) = std_list_common_defs.com_type_defs.[dictionaryIndexUTSListClass].td_rhs

		= appBackEnd (adjustRecordListInstances tail_strict_list_first_instance_indices rt_fields) backEnd
where
	std_strict_lists=dcls.[std_strict_list_module_index]
	std_strict_list_module_index=predefs.[PD_StdStrictLists].pds_def

	adjust_strict_list_instances i instances backEnd
		| i<size instances
			# instance_i = instances.[i]
			| isEmpty instance_i.ins_type.it_context // && trace_t ("instance: "+++toString instance_i.ins_ident+++" ") && trace_t (types_to_string instance_i.ins_type.it_types+++" ")
				# backEnd = adjust_strict_list_members 0 instance_i.ins_members backEnd
				= adjust_strict_list_instances (i+1) instances backEnd
				= adjust_strict_list_instances (i+1) instances backEnd
			= backEnd
	where
		adjust_strict_list_members i members backEnd
			| i<size members
				# member=members.[i]
				# member_name=member.cim_ident.id_name
				| size member_name>1 && member_name.[1]=='c' // && trace_tn ("member: "+++member_name)
					# (ft_type,backEnd) = read_from_var_heap std_strict_lists.dcl_functions.[member.cim_index].ft_type_ptr backEnd
					= case ft_type of
						VI_ExpandedType _
							# backEnd=appBackEnd (BEAdjustStrictListConsInstance member.cim_index std_strict_list_module_index) backEnd
							-> adjust_strict_list_members (i+1) members backEnd
						_
							-> adjust_strict_list_members (i+1) members backEnd					
					= adjust_strict_list_members (i+1) members backEnd
				= backEnd

	adjust_overloaded_nil_functions function_index first_instance_index std_strict_lists_nil_functions backEnd
		| function_index<first_instance_index
			# backEnd = appBackEnd (BEAdjustOverloadedNilFunction function_index std_strict_list_module_index) backEnd
			= adjust_overloaded_nil_functions (function_index+1) first_instance_index std_strict_lists_nil_functions backEnd
			= backEnd

	adjustRecordListInstances [] rt_fields backend
		= backend
	adjustRecordListInstances [index:indices] rt_fields backend
		# backend = BEAdjustStrictListConsInstance index main_dcl_module_n backend
		  (r0,backend) = BESetDictionaryFieldOfMember index rt_fields.[0].fs_index std_strict_list_module_index backend
		  backend = BEAdjustUnboxedListDeconsInstance (index+1) main_dcl_module_n backend
		  (r1,backend) = BESetDictionaryFieldOfMember (index+1) rt_fields.[1].fs_index std_strict_list_module_index backend
		= adjustRecordListInstances indices rt_fields backend

adjustStrictMaybeFunctions :: [Int] {#PredefinedSymbol} {#DclModule} NumberSet Int *BackEndState -> *BackEndState;
adjustStrictMaybeFunctions maybe_unboxed_first_instance_indices predefs dcls used_module_numbers main_dcl_module_n backEnd
	| std_strict_maybes_module_index==NoIndex || not (inNumberSet std_strict_maybes_module_index used_module_numbers)
		|| std_strict_maybes_module_index==main_dcl_module_n
		= backEnd
		# std_strict_maybes_instances=std_strict_maybes.dcl_common.com_instance_defs
		# backEnd = adjust_strict_maybe_instances 0 std_strict_maybes_instances backEnd
		# std_strict_maybes_nothing_functions=std_strict_maybes.dcl_functions
		# first_instance_index=std_strict_maybes.dcl_instances.ir_from;
		# backEnd=adjust_overloaded_nothing_functions 0 first_instance_index std_strict_maybes_nothing_functions backEnd

		# std_maybe_common_defs = std_strict_maybes.dcl_common
		  indexUMaybeClass = predefs.[PD_UMaybeClass].pds_def
		  dictionaryIndexUMaybeClass = std_maybe_common_defs.com_class_defs.[indexUMaybeClass].class_dictionary.ds_index
		  (RecordType {rt_fields}) = std_maybe_common_defs.com_type_defs.[dictionaryIndexUMaybeClass].td_rhs

		= appBackEnd (adjustRecordMaybeInstances maybe_unboxed_first_instance_indices rt_fields) backEnd
where
	std_strict_maybes=dcls.[std_strict_maybes_module_index]
	std_strict_maybes_module_index=predefs.[PD_StdStrictMaybes].pds_def

	adjust_strict_maybe_instances i instances backEnd
		| i<size instances
			# instance_i = instances.[i]
			| instance_i.ins_type.it_context=:[]
				# backEnd = adjust_strict_maybe_members 0 instance_i.ins_members backEnd
				= adjust_strict_maybe_instances (i+1) instances backEnd
				= adjust_strict_maybe_instances (i+1) instances backEnd
			= backEnd
	where
		adjust_strict_maybe_members i members backEnd
			| i<size members
				# member=members.[i]
				# member_name=member.cim_ident.id_name
				| size member_name>1 && member_name.[1]=='c'
					# (ft_type,backEnd) = read_from_var_heap std_strict_maybes.dcl_functions.[member.cim_index].ft_type_ptr backEnd
					= case ft_type of
						VI_ExpandedType _
							# backEnd=appBackEnd (BEAdjustStrictJustInstance member.cim_index std_strict_maybes_module_index) backEnd
							-> adjust_strict_maybe_members (i+1) members backEnd
						_
							-> adjust_strict_maybe_members (i+1) members backEnd
					= adjust_strict_maybe_members (i+1) members backEnd
				= backEnd

	adjust_overloaded_nothing_functions function_index first_instance_index std_strict_maybes_nothing_functions backEnd
		| function_index<first_instance_index
			# backEnd = appBackEnd (BEAdjustOverloadedNothingFunction function_index std_strict_maybes_module_index) backEnd
			= adjust_overloaded_nothing_functions (function_index+1) first_instance_index std_strict_maybes_nothing_functions backEnd
			= backEnd

	adjustRecordMaybeInstances [] rt_fields backend
		= backend
	adjustRecordMaybeInstances [index:indices] rt_fields backend
		# backend = BEAdjustStrictJustInstance index main_dcl_module_n backend
		  (r0,backend) = BESetDictionaryFieldOfMember index rt_fields.[0].fs_index std_strict_maybes_module_index backend
		  backend = BEAdjustUnboxedFromJustInstance (index+1) main_dcl_module_n backend
		  (r1,backend) = BESetDictionaryFieldOfMember (index+1) rt_fields.[1].fs_index std_strict_maybes_module_index backend
		= adjustRecordMaybeInstances indices rt_fields backend

:: AdjustStdArrayInfo =
	{	asai_moduleIndex	:: !Int
	,	asai_mapping 		:: !{#BEArrayFunKind}
	,	asai_funs			:: !{#FunType}
	}

adjustArrayFunctions :: [Int] PredefinedSymbols Int {#FunDef} {#DclModule} {#ClassInstance} NumberSet -> BackEnder
adjustArrayFunctions array_first_instance_indices predefs main_dcl_module_n functions dcls icl_instances used_module_numbers
	=	adjustStdArray arrayInfo predefs
				(if (arrayModuleIndex == main_dcl_module_n) icl_instances stdArray.dcl_common.com_instance_defs)
	o`	adjustIclArrayInstances array_first_instance_indices arrayMemberMapping (size arrayClass.class_members) /*functions*/
	where
		arrayModuleIndex
			=	predefs.[PD_StdArray].pds_def
		arrayClassIndex
			=	predefs.[PD_ArrayClass].pds_def
		stdArray
			=	dcls.[arrayModuleIndex]
		arrayClass
			=	stdArray.dcl_common.com_class_defs.[arrayClassIndex]
		arrayMemberMapping
			=	getArrayMemberMapping predefs arrayClass.class_members
		arrayInfo
			=	{	asai_moduleIndex	= arrayModuleIndex
				,	asai_mapping 		= arrayMemberMapping
				,	asai_funs			= stdArray.dcl_functions
				}

		getArrayMemberMapping :: PredefinedSymbols {#DefinedSymbol} -> {#BEArrayFunKind}
		getArrayMemberMapping predefs members
			// sanity check ...
			| size members <> length (memberIndexMapping predefs)
				=	abort "backendconvert, arrayMemberMapping: incorrect number of members"
			// ... sanity check
			=	{	createArray (size members) BENoArrayFun
				&	[i] = backEndFunKind member.ds_index (memberIndexMapping predefs) \\ member <-: members & i <- [0..]
				}				
			where
				memberIndexMapping :: PredefinedSymbols -> [(Index,BEArrayFunKind)]
				memberIndexMapping predefs
					=	[(predefs.[predefIndex].pds_def, backEndArrayFunKind) \\ (predefIndex, backEndArrayFunKind) <- predefMapping]
					where
						predefMapping 
							=	[	(PD_CreateArrayFun,		BECreateArrayFun)
								,	(PD_ArraySelectFun,		BEArraySelectFun)
								,	(PD_UnqArraySelectFun,	BEUnqArraySelectFun)
								,	(PD_ArrayUpdateFun,		BEArrayUpdateFun)
								,	(PD_ArrayReplaceFun,	BEArrayReplaceFun)
								,	(PD_ArraySizeFun,		BEArraySizeFun)
								,	(PD_UnqArraySizeFun,	BEUnqArraySizeFun)
								,	(PD__CreateArrayFun,	BE_CreateArrayFun)
								]

				backEndFunKind :: Index [(Index,BEArrayFunKind)] -> BEArrayFunKind
				backEndFunKind memberIndex predefMapping
					=	hd [back \\ (predefMemberIndex, back) <- predefMapping | predefMemberIndex == memberIndex]

		adjustStdArray :: AdjustStdArrayInfo PredefinedSymbols {#ClassInstance} -> BackEnder
		adjustStdArray arrayInfo predefs instances
			| arrayModuleIndex == NoIndex || not (inNumberSet arrayModuleIndex used_module_numbers)
				=	identity
			// otherwise
				=	foldStateA (adjustStdArrayInstance arrayClassIndex arrayInfo) instances
			where
				adjustStdArrayInstance :: Index AdjustStdArrayInfo ClassInstance -> BackEnder
				adjustStdArrayInstance arrayClassIndex arrayInfo=:{asai_moduleIndex} instance`=:{ins_class_index}
					| ins_class_index.gi_index == arrayClassIndex && ins_class_index.gi_module == asai_moduleIndex
						=	adjustArrayClassInstance arrayInfo instance`
					// otherwise
						=	identity
					where
						adjustArrayClassInstance :: AdjustStdArrayInfo ClassInstance -> BackEnder
						adjustArrayClassInstance arrayInfo {ins_members, ins_ident}
							=	foldStateWithIndexA (adjustMember arrayInfo) ins_members
						where
							adjustMember :: AdjustStdArrayInfo Int ClassInstanceMember -> BackEnder
							adjustMember {asai_moduleIndex, asai_mapping, asai_funs} offset {cim_index}
								| asai_moduleIndex == main_dcl_module_n
									=	beAdjustArrayFunction asai_mapping.[offset] cim_index asai_moduleIndex
								// otherwise
									= \be0 ->	let (ft_type,be) = read_from_var_heap asai_funs.[cim_index].ft_type_ptr be0 in
										(case ft_type of
											VI_ExpandedType _
												->	beAdjustArrayFunction asai_mapping.[offset] cim_index asai_moduleIndex
											_
												->	identity) be

		array_class_dictionary_index = arrayClass.class_dictionary.ds_index
		(RecordType {rt_fields}) = stdArray.dcl_common.com_type_defs.[array_class_dictionary_index].td_rhs

		adjustIclArrayInstances :: [Int] {#BEArrayFunKind} Int -> BackEnder
		adjustIclArrayInstances array_first_instance_indices mapping n_array_members
			= adjustIclArrayInstances array_first_instance_indices
			where
				adjustIclArrayInstances [array_first_instance_index:array_first_instance_indices]
					=	appBackEnd (adjustIclArrayInstanceMembers array_first_instance_index 0)
					o`	adjustIclArrayInstances array_first_instance_indices
				adjustIclArrayInstances []
					= identity

				adjustIclArrayInstanceMembers index member_index backend
					| member_index==n_array_members
						= backend
						# backend = BEAdjustArrayFunction mapping.[member_index] index main_dcl_module_n backend
						# (r0,backend) = BESetDictionaryFieldOfMember index rt_fields.[member_index].fs_index arrayModuleIndex backend
						= adjustIclArrayInstanceMembers (index+1) (member_index+1) backend

convertRules :: [(Int, FunDef)] Int Ident *BackEndState -> (BEImpRuleP, *BackEndState)
convertRules rules main_dcl_module_n aliasDummyId be
	# (null, be)
		=	accBackEnd BENoRules be
	=	convert rules null be
	where
		convert :: [(Int, FunDef)] BEImpRuleP *BackEndState -> (BEImpRuleP, *BackEndState)
		convert [] rulesP be
			=	(rulesP, be)
		convert [h:t] rulesP be
			# (ruleP, be)
				=	convertRule aliasDummyId h main_dcl_module_n be
			# (rulesP, be)
				=	accBackEnd (BERules ruleP rulesP) be
			=	convert t rulesP be

convertRule :: Ident (Int,FunDef) Int -> BEMonad BEImpRuleP
convertRule aliasDummyId (index, {fun_type=Yes type, fun_body=body, fun_pos, fun_kind, fun_info}) main_dcl_module_n
	| fun_info.fi_properties bitand FI_FusedMember<>0
		#! instance_function_index = fun_info.fi_def_level;
		= convert_fused_instance_member_function instance_function_index
		with
		  convert_fused_instance_member_function instance_function_index bes
			# bes & bes_backEnd = BESetInstanceFunctionOfFunction index instance_function_index bes.bes_backEnd
			= beRule index (cafness fun_kind)
					(convertTypeAlt index main_dcl_module_n type)
					(convertFunctionBody index (positionToLineNumber fun_pos) aliasDummyId body main_dcl_module_n)
					bes
		= beRule index (cafness fun_kind)
			(convertTypeAlt index main_dcl_module_n type)
			(convertFunctionBody index (positionToLineNumber fun_pos) aliasDummyId body main_dcl_module_n)
	where
		cafness :: FunKind -> Int
		cafness (FK_Function _)
			=	BEIsNotACaf
		cafness FK_Macro
			=	BEIsNotACaf
		cafness FK_Caf
			=	BEIsACaf
		cafness funKind
			=	BEIsNotACaf // <<- ("backendconvert, cafness: unknown fun kind", funKind)

		positionToLineNumber :: Position -> Int
		positionToLineNumber (FunPos  _ lineNumber _)
			=	lineNumber
		positionToLineNumber (LinePos _ lineNumber)
			=	lineNumber
		positionToLineNumber _
			=	0

beautifyAttributes :: SymbolType -> BEMonad SymbolType
beautifyAttributes st
	=	return st
//	=	accAttrHeap (beautifulizeAttributes st)

convertTypeAlt :: Int ModuleIndex SymbolType -> BEMonad BETypeAltP
convertTypeAlt functionIndex moduleIndex symbolType
	= beFunctionSymbol functionIndex moduleIndex ==> \symbol_p ->
	  convertTypeAltForSymbolP symbol_p symbolType

convertTypeAltForSymbolP :: BESymbolP SymbolType -> BEMonad BETypeAltP
convertTypeAltForSymbolP symbol_p symbolType
	=	beautifyAttributes (symbolType) ==> \symbolType=:{st_result, st_attr_env, st_attr_vars} 
	->	resetAttrNumbers st_attr_vars
	o`	(beTypeAlt symbol_p
			(convertSymbolTypeArgs symbolType)
			(convertAnnotTypeNode st_result))

convertExportedTypeAltForSymbolP :: BESymbolP SymbolType -> BEMonad BETypeAltP
convertExportedTypeAltForSymbolP symbol_p symbolType
	=	beautifyAttributes symbolType ==> \ {st_args,st_args_strictness,st_result, st_attr_env, st_attr_vars} 
	->	resetAttrNumbers st_attr_vars
	o`	(beTypeAlt symbol_p
			(convertAnnotatedExternalTypeArgs st_args st_args_strictness)
			(convertAnnotExternalTypeNode st_result))

resetAttrNumbers :: [AttributeVar] *BackEndState -> *BackEndState
resetAttrNumbers attrVars state=:{bes_attrHeap}
	=	{	state
		&	bes_attr_number = 0
		,	bes_attrHeap = foldSt resetAttrVar attrVars bes_attrHeap
		}
	where
		resetAttrVar :: AttributeVar *AttrVarHeap -> *AttrVarHeap
		resetAttrVar {av_info_ptr} attrHeap
			=	writePtr av_info_ptr AVI_Empty attrHeap

convertSymbolTypeArgs :: SymbolType -> BEMonad BETypeArgP
convertSymbolTypeArgs {st_args,st_args_strictness}
	= convertAnnotatedTypeArgs st_args st_args_strictness

convertBasicTypeKind :: BasicType -> BETypeSymbKind
convertBasicTypeKind BT_Int
	=	BEIntType
convertBasicTypeKind BT_Char
	=	BECharType
convertBasicTypeKind BT_Real
	=	BERealType
convertBasicTypeKind BT_Bool
	=	BEBoolType
convertBasicTypeKind BT_File
	=	BEFileType
convertBasicTypeKind BT_World
	=	BEWorldType
convertBasicTypeKind BT_Dynamic
	=	undef // <<- "convertBasicTypeKind (BT_Dynamic) shouldn't occur"
convertBasicTypeKind (BT_String _)
	=	undef // <<- "convertBasicTypeKind (BT_String _) shouldn't occur"

convertAnnotation :: Annotation -> BEAnnotation
convertAnnotation AN_None
	=	BENoAnnot
convertAnnotation AN_Strict
	=	BEStrictAnnot

nextAttributeNumber :: *BackEndState -> (BEAttribution, *BackEndState)
nextAttributeNumber state=:{bes_attr_number}
	=	(bes_attr_number + BEFirstUniVarNumber, {state & bes_attr_number = bes_attr_number+1})

convertAttributeVar :: AttributeVar *BackEndState -> (BEAttribution, *BackEndState)
convertAttributeVar {av_info_ptr, av_ident} state=:{bes_attr_number}
	# (attrInfo, state)
		=	read_from_attr_heap av_info_ptr state
	=	case attrInfo of
			AVI_SequenceNumber number
				->	(number, state)
			_
				# (attrNumber, state)
					=	nextAttributeNumber state
				->	(attrNumber, write_to_attr_heap av_info_ptr (AVI_SequenceNumber attrNumber) state)

convertAttribution :: TypeAttribute -> BEMonad BEAttribution
convertAttribution TA_Unique
	=	return BEUniqueAttr
convertAttribution TA_None
	=	return BENoUniAttr
convertAttribution TA_Multi
	=	return BENoUniAttr
convertAttribution TA_Anonymous
	=	nextAttributeNumber
convertAttribution (TA_Var attrVar)
	=	convertAttributeVar attrVar
convertAttribution (TA_RootVar attrVar)
	=	convertAttributeVar attrVar
convertAttribution TA_MultiOfPropagatingConsVar
	=	return BENoUniAttr
// FIXME
// this is a work around for caching / attribute heap bug
convertAttribution _
	=	return BENoUniAttr

convertAnnotTypeNode :: AType -> BEMonad BETypeNodeP
convertAnnotTypeNode {at_type, at_attribute}
	= convertAttribution at_attribute ==> \ attribution
	-> convertTypeNode at_type (convertAnnotation AN_None) attribution

convertAnnotExternalTypeNode :: AType -> BEMonad BETypeNodeP
convertAnnotExternalTypeNode {at_type, at_attribute}
	= convertAttribution at_attribute ==> \ attribution
	-> convertExternalTypeNode at_type (convertAnnotation AN_None) attribution

convertAnnotAndTypeNode :: Annotation AType -> BEMonad BETypeNodeP
convertAnnotAndTypeNode at_annotation {at_type, at_attribute}
	= convertAttribution at_attribute ==> \ attribution
	-> convertTypeNode at_type (convertAnnotation at_annotation) attribution

convertAnnotAndExternalTypeNode :: Annotation AType -> BEMonad BETypeNodeP
convertAnnotAndExternalTypeNode at_annotation {at_type, at_attribute}
	= convertAttribution at_attribute ==> \ attribution
	-> convertExternalTypeNode at_type (convertAnnotation at_annotation) attribution

convert_contexts :: [.a] BETypeNodeP BEAnnotation BEAttribution *BackEndState -> *(BETypeNodeP,*BackEndState)
convert_contexts [context:contexts] type_node_p annotation attribution bes
	# (no_type_args,    bes) = accBackEnd BENoTypeArgs bes
	  (type_node_p,     bes) = convert_contexts contexts type_node_p BENoAnnot BENoUniAttr bes
	  (type_args,       bes) = accBackEnd (BETypeArgs type_node_p no_type_args) bes
	  (var_type_node,   bes) = accBackEnd (BEVar0TypeNode BENoAnnot BENoUniAttr) bes
	  (type_args,       bes) = accBackEnd (BETypeArgs var_type_node type_args) bes
	  (fun_type_symbol, bes) = accBackEnd (BEBasicTypeSymbol BEFunType) bes
	= accBackEnd (BESymbolTypeNode annotation attribution fun_type_symbol type_args) bes
convert_contexts [] type_node_p annotation attribution bes
	= (type_node_p,bes)

convertTypeNode :: Type BEAnnotation BEAttribution -> BEMonad BETypeNodeP
convertTypeNode (TB (BT_String type)) annotation attribution
	=	convertTypeNode type annotation attribution
convertTypeNode (TB BT_Dynamic) annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) beDynamicTempTypeSymbol beNoTypeArgs	
convertTypeNode (TB basicType) annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) (beBasicTypeSymbol (convertBasicTypeKind basicType)) beNoTypeArgs	
convertTypeNode (TA typeSymbolIdent typeArgs) annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) (convertTypeSymbolIdent typeSymbolIdent) (convertTypeArgs typeArgs )
convertTypeNode (TAS typeSymbolIdent typeArgs strictness) annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) (convertTypeSymbolIdent typeSymbolIdent) (convertAnnotatedTypeArgs typeArgs strictness)
convertTypeNode (TV _) annotation attribution
	=	beFunction0 (BEVar0TypeNode annotation attribution)
convertTypeNode (TempV _) annotation attribution
	=	beFunction0 (BEVar0TypeNode annotation attribution)
convertTypeNode (TempQV _) annotation attribution
	=	beFunction0 (BEVar0TypeNode annotation attribution)
convertTypeNode (TempQDV _) annotation attribution
	=	beFunction0 (BEVar0TypeNode annotation attribution)
convertTypeNode (a --> b) annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) (beBasicTypeSymbol BEFunType) (convertTypeArgs [a, b])
convertTypeNode (TArrow1 a) annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) (beBasicTypeSymbol BEFunType) (convertTypeArgs [a])
convertTypeNode TArrow annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) (beBasicTypeSymbol BEFunType) beNoTypeArgs
convertTypeNode (a :@: b) annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) (beBasicTypeSymbol BEApplyType) (convertTypeArgs [{at_attribute=TA_Multi, at_type = consVariableToType a} : b])
convertTypeNode TE annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) beDontCareTypeDefinitionSymbol beNoTypeArgs
convertTypeNode TAll annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) beDontCareTypeDefinitionSymbol beNoTypeArgs
convertTypeNode (TFA vars type) annotation attribution
	=	convertTypeNode type annotation attribution
convertTypeNode (TFAC vars type contexts) annotation attribution
	= convertTFAC contexts type annotation attribution
	where
		convertTFAC contexts type annotation attribution bes
			# (type_node_p,bes) = convertTypeNode type BENoAnnot BENoUniAttr bes
			= convert_contexts contexts type_node_p annotation attribution bes
convertTypeNode (TGenericFunctionInDictionary gds type_kind {gi_module,gi_index}) annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) (beTypeSymbol gi_index gi_module) beNoTypeArgs
convertTypeNode typeNode annotation attribution
	=	abort "convertTypeNode"  // <<- ("backendconvert, convertTypeNode: unknown type node", typeNode)

convertExternalTypeNode :: Type BEAnnotation BEAttribution -> BEMonad BETypeNodeP
convertExternalTypeNode (TA typeSymbolIdent typeArgs) annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) (convertExternalTypeSymbolIdent typeSymbolIdent) (convertExternalTypeArgs typeArgs )
convertExternalTypeNode (TAS typeSymbolIdent typeArgs strictness) annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) (convertTypeSymbolIdent typeSymbolIdent) (convertAnnotatedExternalTypeArgs typeArgs strictness)
convertExternalTypeNode (a --> b) annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) (beBasicTypeSymbol BEFunType) (convertExternalTypeArgs [a, b])
convertExternalTypeNode (TArrow1 a) annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) (beBasicTypeSymbol BEFunType) (convertExternalTypeArgs [a])
convertExternalTypeNode (a :@: b) annotation attribution
	=	beFunction2 (BESymbolTypeNode annotation attribution) (beBasicTypeSymbol BEApplyType) (convertExternalTypeArgs [{at_attribute=TA_Multi, at_type = consVariableToType a} : b])
convertExternalTypeNode (TFA vars type) annotation attribution
	=	convertExternalTypeNode type annotation attribution
convertExternalTypeNode (TFAC vars type contexts) annotation attribution
	= convertTFAC contexts type annotation attribution
	where
		convertTFAC contexts type annotation attribution bes
			# (type_node_p,bes) = convertExternalTypeNode type BENoAnnot BENoUniAttr bes
			= convert_contexts contexts type_node_p annotation attribution bes
convertExternalTypeNode typeNode annotation attribution
	=	convertTypeNode typeNode annotation attribution

convertTypeDefAnnotTypeNode :: AType !*TypeVarHeap !*BackEndState -> (!BETypeNodeP,!*TypeVarHeap,!*BackEndState)
convertTypeDefAnnotTypeNode {at_type, at_attribute} type_var_heap bes
	# (attribution,bes) = convertAttribution at_attribute bes
	= convertTypeDefTypeNode at_type (convertAnnotation AN_None) attribution type_var_heap bes

convertTypeDefAnnotAndTypeNode :: Annotation AType !*TypeVarHeap !*BackEndState-> (!BETypeNodeP,!*TypeVarHeap,!*BackEndState)
convertTypeDefAnnotAndTypeNode at_annotation {at_type, at_attribute} type_var_heap bes
	# (attribution,bes) = convertAttribution at_attribute bes
	= convertTypeDefTypeNode at_type (convertAnnotation at_annotation) attribution type_var_heap bes

convertTypeDefTypeNode :: Type BEAnnotation BEAttribution !*TypeVarHeap !*BackEndState -> (!BETypeNodeP,!*TypeVarHeap,!*BackEndState)
convertTypeDefTypeNode (TB (BT_String type)) annotation attribution type_var_heap bes
	= convertTypeDefTypeNode type annotation attribution type_var_heap bes
convertTypeDefTypeNode (TB BT_Dynamic) annotation attribution type_var_heap bes
	# (type_node_p,bes) = beFunction2 (BESymbolTypeNode annotation attribution) beDynamicTempTypeSymbol beNoTypeArgs bes
	= (type_node_p,type_var_heap,bes)
convertTypeDefTypeNode (TB basicType) annotation attribution type_var_heap bes
	# (type_node_p,bes) = beFunction2 (BESymbolTypeNode annotation attribution) (beBasicTypeSymbol (convertBasicTypeKind basicType)) beNoTypeArgs bes
	= (type_node_p,type_var_heap,bes)
convertTypeDefTypeNode (TA typeSymbolIdent typeArgs) annotation attribution type_var_heap bes
	# (symbol_p,bes) = convertTypeSymbolIdent typeSymbolIdent bes
	  (type_arg_p,type_var_heap,bes) = convertTypeDefTypeArgs typeArgs type_var_heap bes
	  (type_node_p,bes) = accBackEnd (BESymbolTypeNode annotation attribution symbol_p type_arg_p) bes
	= (type_node_p,type_var_heap,bes)
convertTypeDefTypeNode (TAS typeSymbolIdent typeArgs strictness) annotation attribution type_var_heap bes
	# (symbol_p,bes) = convertTypeSymbolIdent typeSymbolIdent bes
	  (type_arg_p,type_var_heap,bes) = convertTypeDefAnnotatedTypeArgs typeArgs strictness type_var_heap bes
	  (type_node_p,bes) = accBackEnd (BESymbolTypeNode annotation attribution symbol_p type_arg_p) bes
	= (type_node_p,type_var_heap,bes)
convertTypeDefTypeNode (TV {tv_info_ptr}) annotation attribution type_var_heap bes
	#! argument_n
		= case sreadPtr tv_info_ptr type_var_heap of
				TVI_TypeVarArgN type_var_arg_n
					-> type_var_arg_n
				_
					-> -1
	# (type_node_p,bes) = accBackEnd (BEVarNTypeNode annotation attribution argument_n) bes
	= (type_node_p,type_var_heap,bes)
convertTypeDefTypeNode (TempV _) annotation attribution type_var_heap bes
	# (type_node_p,bes) = accBackEnd (BEVarNTypeNode annotation attribution -1) bes
	= (type_node_p,type_var_heap,bes)
convertTypeDefTypeNode (TempQV _) annotation attribution type_var_heap bes
	# (type_node_p,bes) = accBackEnd (BEVarNTypeNode annotation attribution -1) bes
	= (type_node_p,type_var_heap,bes)
convertTypeDefTypeNode (TempQDV _) annotation attribution type_var_heap bes
	# (type_node_p,bes) = accBackEnd (BEVarNTypeNode annotation attribution -1) bes
	= (type_node_p,type_var_heap,bes)
convertTypeDefTypeNode (a --> b) annotation attribution type_var_heap bes
	# (symbol_p,bes) = accBackEnd (BEBasicTypeSymbol BEFunType) bes
	  (type_arg_p,type_var_heap,bes) = convertTypeDefTypeArgs [a, b] type_var_heap bes
	  (type_node_p,bes) = accBackEnd (BESymbolTypeNode annotation attribution symbol_p type_arg_p) bes
	= (type_node_p,type_var_heap,bes)
convertTypeDefTypeNode (TArrow1 a) annotation attribution type_var_heap bes
	# (symbol_p,bes) = accBackEnd (BEBasicTypeSymbol BEFunType) bes
	  (type_arg_p,type_var_heap,bes) = convertTypeDefTypeArgs [a] type_var_heap bes
	  (type_node_p,bes) = accBackEnd (BESymbolTypeNode annotation attribution symbol_p type_arg_p) bes
	= (type_node_p,type_var_heap,bes)
convertTypeDefTypeNode TArrow annotation attribution type_var_heap bes
	# (type_node_p,bes) = beFunction2 (BESymbolTypeNode annotation attribution) (beBasicTypeSymbol BEFunType) beNoTypeArgs bes
	= (type_node_p,type_var_heap,bes)
convertTypeDefTypeNode (a :@: b) annotation attribution type_var_heap bes
	# (symbol_p,bes) = accBackEnd (BEBasicTypeSymbol BEApplyType) bes
	  (type_arg_p,type_var_heap,bes) = convertTypeDefTypeArgs [{at_attribute=TA_Multi, at_type=consVariableToType a} : b] type_var_heap bes
	  (type_node_p,bes) = accBackEnd (BESymbolTypeNode annotation attribution symbol_p type_arg_p) bes
	= (type_node_p,type_var_heap,bes)
convertTypeDefTypeNode TE annotation attribution type_var_heap bes
	# (type_node_p,bes) = beFunction2 (BESymbolTypeNode annotation attribution) beDontCareTypeDefinitionSymbol beNoTypeArgs bes
	= (type_node_p,type_var_heap,bes)
convertTypeDefTypeNode (TFA vars type) annotation attribution type_var_heap bes
	= convertTypeDefTypeNode type annotation attribution type_var_heap bes
convertTypeDefTypeNode (TFAC vars type contexts) annotation attribution type_var_heap bes
	# (type_node_p,type_var_heap,bes) = convertTypeDefTypeNode type BENoAnnot BENoUniAttr type_var_heap bes
	  (type_node_p,bes) = convert_contexts contexts type_node_p annotation attribution bes
	= (type_node_p,type_var_heap,bes)
convertTypeDefTypeNode (TGenericFunctionInDictionary gds type_kind {gi_module,gi_index}) annotation attribution type_var_heap bes
	# (type_node_p,bes) = beFunction2 (BESymbolTypeNode annotation attribution) (beTypeSymbol gi_index gi_module) beNoTypeArgs bes
	= (type_node_p,type_var_heap,bes)

consVariableToType :: ConsVariable -> Type
consVariableToType (CV typeVar)
	=	TV typeVar
consVariableToType (TempCV varId)
	=	TempV varId
consVariableToType (TempQCV varId)
	=	TempQV varId
consVariableToType (TempQCDV varId)
	=	TempQDV varId

convertTypeArgs :: [AType] -> BEMonad BETypeArgP
convertTypeArgs args
	=	sfoldr (beTypeArgs o convertAnnotTypeNode) beNoTypeArgs args

convertExternalTypeArgs :: [AType] -> BEMonad BETypeArgP
convertExternalTypeArgs args
	=	sfoldr (beTypeArgs o convertAnnotExternalTypeNode) beNoTypeArgs args

convertTypeDefTypeArgs :: [AType] !*TypeVarHeap !*BackEndState -> (!BETypeArgP,!*TypeVarHeap,!*BackEndState)
convertTypeDefTypeArgs args type_var_heap bes
	= convert_type_def_type_args args type_var_heap bes
where
	convert_type_def_type_args [] type_var_heap bes
		# (type_arg_p,bes) = beNoTypeArgs bes
		= (type_arg_p,type_var_heap,bes)
	convert_type_def_type_args [a:x] type_var_heap bes
		# (atype_arg,type_var_heap,bes)
			= convertTypeDefAnnotTypeNode a type_var_heap bes
		  (atype_args,type_var_heap,bes) = convert_type_def_type_args x type_var_heap bes
		  (type_arg_p,bes) = accBackEnd (BETypeArgs atype_arg atype_args) bes
		= (type_arg_p,type_var_heap,bes)

convertAnnotatedTypeArgs :: [AType] StrictnessList -> BEMonad BETypeArgP
convertAnnotatedTypeArgs args strictness
	= foldr args 0
	where
		foldr [] i
			= beNoTypeArgs
		foldr [a:x] i
			= (beTypeArgs o (convertAnnotAndTypeNode (arg_strictness_annotation i strictness))) a (foldr x (i+1))

convertAnnotatedExternalTypeArgs :: [AType] StrictnessList -> BEMonad BETypeArgP
convertAnnotatedExternalTypeArgs args strictness
	= foldr args 0
	where
		foldr [] i
			= beNoTypeArgs
		foldr [a:x] i
			= (beTypeArgs o (convertAnnotAndExternalTypeNode (arg_strictness_annotation i strictness))) a (foldr x (i+1))

convertTypeDefAnnotatedTypeArgs :: [AType] StrictnessList !*TypeVarHeap !*BackEndState
										  -> (!BETypeArgP,!*TypeVarHeap,!*BackEndState)
convertTypeDefAnnotatedTypeArgs args strictness type_var_heap bes
	= convert_type_def_annotated_type_args args 0 type_var_heap bes
where
	convert_type_def_annotated_type_args [a:x] i type_var_heap bes
		# (atype_arg,type_var_heap,bes)
			= convertTypeDefAnnotAndTypeNode (arg_strictness_annotation i strictness) a type_var_heap bes
		  (atype_args,type_var_heap,bes) = convert_type_def_annotated_type_args x (i+1) type_var_heap bes
		  (type_arg_p,bes) = accBackEnd (BETypeArgs atype_arg atype_args) bes
		= (type_arg_p,type_var_heap,bes)
	convert_type_def_annotated_type_args [] i type_var_heap bes
		# (type_arg_p,bes) = beNoTypeArgs bes
		= (type_arg_p,type_var_heap,bes)

convertTransformedBody :: Int Int Ident TransformedBody Int -> BEMonad BERuleAltP
convertTransformedBody functionIndex lineNumber aliasDummyId body main_dcl_module_n
	| isCodeBlock body.tb_rhs
		=	declareVars body aliasDummyId
		o`	convertCodeBody functionIndex lineNumber aliasDummyId body main_dcl_module_n
	// otherwise
		=	declareVars body aliasDummyId
		o`	convertBody True functionIndex lineNumber aliasDummyId (map FP_Variable body.tb_args) body.tb_rhs main_dcl_module_n

isCodeBlock :: Expression -> Bool
isCodeBlock (Case {case_expr=Var _, case_guards=AlgebraicPatterns _ [{ap_expr}]})
	=	isCodeBlock ap_expr
isCodeBlock (ABCCodeExpr _ _)
	=	True
isCodeBlock (AnyCodeExpr _ _ _)
	=	True
isCodeBlock expr
	=	False

convertFunctionBody :: Int Int Ident FunctionBody Int -> BEMonad BERuleAltP
convertFunctionBody functionIndex lineNumber aliasDummyId (TransformedBody body) main_dcl_module_n
	=	convertTransformedBody functionIndex lineNumber aliasDummyId body main_dcl_module_n

convertCodeBody :: Int Int Ident TransformedBody Int -> BEMonad BERuleAltP
convertCodeBody functionIndex lineNumber aliasDummyId body main_dcl_module_n
	=	convertBody False functionIndex lineNumber aliasDummyId patterns expr main_dcl_module_n
	where
		patterns
			=	map (lookUpVar body.tb_rhs) body.tb_args
		expr
			=	codeBlock body.tb_rhs

		lookUpVar :: Expression FreeVar -> FunctionPattern
		lookUpVar (Case {case_expr=Var boundVar, case_guards=AlgebraicPatterns _ [ap]}) freeVar
			| freeVar.fv_info_ptr == boundVar.var_info_ptr
				=	FP_Algebraic ap.ap_symbol subPatterns
				with
					subPatterns
						=	map (lookUpVar ap.ap_expr) ap.ap_vars
			// otherwise
				=	lookUpVar ap.ap_expr freeVar
		lookUpVar _ freeVar
			=	FP_Variable freeVar

		codeBlock :: Expression -> Expression
		codeBlock (Case {case_expr=Var (var_infoPtr), case_guards=AlgebraicPatterns _ [{ap_expr}]})
			=	codeBlock ap_expr
		codeBlock expr
			=	expr

ruleAlt setRefCounts line lhsDefsM lhsM rhsDefsM rhsStrictsM rhsM be
	| setRefCounts
		# (lhs, be)
			=	lhsM be
		# be
			=	appBackEnd (BESetNodeDefRefCounts lhs) be	
		# (lhsDefs, be)
			=	lhsDefsM be
		=	beFunction3 (BERuleAlt line lhsDefs lhs) rhsDefsM rhsStrictsM rhsM be
	// otherwise
		=	beRuleAlt line lhsDefsM lhsM rhsDefsM rhsStrictsM rhsM be

convertBody :: Bool Int Int Ident [FunctionPattern] Expression Int -> BEMonad BERuleAltP
convertBody _ functionIndex lineNumber aliasDummyId args (ABCCodeExpr instructions inline) main_dcl_module_n
	=	beNoNodeDefs ==> \noNodeDefs
	->	beCodeAlt
			lineNumber
			(return noNodeDefs)
			(convertBackEndLhs functionIndex args main_dcl_module_n)
			(beAbcCodeBlock inline (convertStrings instructions))
convertBody _ functionIndex lineNumber aliasDummyId args (AnyCodeExpr inParams outParams instructions) main_dcl_module_n
	=	beNoNodeDefs ==> \noNodeDefs
	->	beCodeAlt
			lineNumber
			(return noNodeDefs)
			(convertBackEndLhs functionIndex args main_dcl_module_n)
			(beAnyCodeBlock (convertCodeParameters inParams) (convertCodeParameters outParams) (convertStrings instructions))
convertBody setRefCounts functionIndex lineNumber aliasDummyId args rhs main_dcl_module_n
	=	beNoNodeDefs ==> \noNodeDefs
	->	ruleAlt setRefCounts
			lineNumber
			(return noNodeDefs)
			(convertBackEndLhs functionIndex args main_dcl_module_n)
			(convertRhsNodeDefs aliasDummyId rhs main_dcl_module_n)
			(convertRhsStrictNodeIds rhs)
			(convertRootExpr aliasDummyId rhs main_dcl_module_n)

convertBackEndLhs :: Int [FunctionPattern] Int -> BEMonad BENodeP
convertBackEndLhs functionIndex patterns main_dcl_module_n
	=	beNormalNode (beFunctionSymbol functionIndex main_dcl_module_n) (convertPatterns patterns)

convertStrings :: [{#Char}] -> BEMonad BEStringListP
convertStrings strings
	=	sfoldr (\s -> beFunction1 (BEStringList s)) beNoStrings strings

convertCodeParameters :: (CodeBinding a) -> BEMonad BECodeParameterP | varInfoPtr a
convertCodeParameters codeParameters
	=	sfoldr (\ {bind_src,bind_dst} -> beFunction2 (BECodeParameterList bind_src) (convertVar (varInfoPtr bind_dst)))
				beNoCodeParameters codeParameters

class varInfoPtr a :: a -> VarInfoPtr

instance varInfoPtr BoundVar where
	varInfoPtr boundVar
		=	boundVar.var_info_ptr

instance varInfoPtr FreeVar where
	varInfoPtr freeVar
		=	freeVar.fv_info_ptr

convertPatterns :: [FunctionPattern] -> BEMonad BEArgP
convertPatterns patterns
	=	sfoldr (beArgs o convertPattern) beNoArgs patterns

convertPattern :: FunctionPattern -> BEMonad BENodeP
convertPattern (FP_Variable freeVar)
	=	convertFreeVarPattern freeVar
convertPattern (FP_Algebraic {glob_module, glob_object={ds_index}} subpatterns)
	=	beNormalNode (beConstructorSymbol glob_module ds_index) (convertPatterns subpatterns)

convertFreeVarPattern :: FreeVar  -> BEMonad BENodeP
convertFreeVarPattern freeVar
	=	beNodeIdNode (convertVar freeVar.fv_info_ptr) beNoArgs

convertLhsArgs :: [FreeVar] -> BEMonad BEArgP
convertLhsArgs freeVars
	=	sfoldr (beArgs o convertFreeVarPattern) beNoArgs freeVars

convertVarPtr :: VarInfoPtr  -> BEMonad BENodeP
convertVarPtr var
	=	beNodeIdNode (convertVar var) beNoArgs

convertVars :: [VarInfoPtr] -> BEMonad BEArgP
convertVars vars
	=	sfoldr (beArgs o convertVarPtr) beNoArgs vars

convertRootExpr :: Ident Expression Int -> BEMonad BENodeP
convertRootExpr aliasDummyId (Let {let_expr}) main_dcl_module_n
	=	convertRootExpr aliasDummyId let_expr main_dcl_module_n
convertRootExpr aliasDummyId (Conditional {if_cond=cond, if_then=then, if_else=Yes else}) main_dcl_module_n
	=	beGuardNode
			(convertRootExpr aliasDummyId cond main_dcl_module_n)
			(convertRhsNodeDefs aliasDummyId then main_dcl_module_n)
			(convertRhsStrictNodeIds then)
			(convertRootExpr aliasDummyId then main_dcl_module_n)
			(convertRhsNodeDefs aliasDummyId else main_dcl_module_n )
			(convertRhsStrictNodeIds else)
			(convertRootExpr aliasDummyId else main_dcl_module_n)
convertRootExpr aliasDummyId (Conditional {if_cond=cond, if_then=then, if_else=No}) main_dcl_module_n
		=	beGuardNode
				(convertRootExpr aliasDummyId cond main_dcl_module_n)
				(convertRhsNodeDefs aliasDummyId then main_dcl_module_n)
				(convertRhsStrictNodeIds then)
				(convertRootExpr aliasDummyId then main_dcl_module_n)
				beNoNodeDefs
				beNoStrictNodeIds
				(beNormalNode (beBasicSymbol BEFailSymb) beNoArgs)
convertRootExpr aliasDummyId (Case kees=:{case_expr=Var var, case_guards}) main_dcl_module_n
	=	beSwitchNode (convertVar var.var_info_ptr) (convertCases case_guards aliasDummyId var (defaultCase kees) main_dcl_module_n)
	where
		defaultCase {case_default=Yes defaul} 
			=	DefaultCase defaul
		defaultCase {case_explicit, case_default=No, case_ident}
			| case_explicit
			 	=	case case_ident of
			 			Yes ident
			 				->	DefaultCaseFail ident
			 			_
							->	DefaultCaseFail {id_name="kees_be", id_info=nilPtr}
			// otherwise
			 	=	DefaultCaseNone
convertRootExpr _ (FailExpr fail_ident) _
	=	beNormalNode (beLiteralSymbol BEFailSymb fail_ident.id_name) beNoArgs
convertRootExpr _ expr main_dcl_module_n
	=	convertExpr expr main_dcl_module_n

convertCondExpr :: Expression Int -> BEMonad BENodeP
convertCondExpr (Conditional {if_cond=cond, if_then=then, if_else=Yes else}) main_dcl_module_n
		=	beGuardNode
				(convertCondExpr cond main_dcl_module_n)
				beNoNodeDefs
				beNoStrictNodeIds
				(convertCondExpr then main_dcl_module_n)
				beNoNodeDefs
				beNoStrictNodeIds
				(convertCondExpr else main_dcl_module_n)
convertCondExpr expr main_dcl_module_n
	=	convertExpr expr main_dcl_module_n

collectNodeDefs :: Ident Expression -> [LetBind]
collectNodeDefs aliasDummyId (Let {let_strict_binds, let_lazy_binds})
	= filterStrictAlias let_strict_binds let_lazy_binds
  where
	filterStrictAlias [] let_lazy_binds
		= let_lazy_binds
	filterStrictAlias [strict_bind=:{lb_src=App app}:strict_binds] let_lazy_binds
		| not (isNilPtr app.app_symb.symb_ident.id_info) && app.app_symb.symb_ident==aliasDummyId
			// the compiled source was a strict alias like "#! x = y"
			= case hd app.app_args of
				Var _
					// the node is still such an alias and must be ignored
					-> filterStrictAlias strict_binds let_lazy_binds
				hd_app_args
					// the node is not an alias anymore: remove just the _dummyForStrictAlias call
					-> [{ strict_bind & lb_src = hd_app_args } : filterStrictAlias strict_binds let_lazy_binds]
	filterStrictAlias [strict_bind:strict_binds] let_lazy_binds
		= [strict_bind: filterStrictAlias strict_binds let_lazy_binds]
collectNodeDefs _ _
	=	[]

convertRhsNodeDefs :: Ident Expression Int -> BEMonad BENodeDefP
convertRhsNodeDefs aliasDummyId expr main_dcl_module_n
	=	convertNodeDefs (collectNodeDefs aliasDummyId expr)
where
	convertNodeDefs :: [LetBind] -> BEMonad BENodeDefP
	convertNodeDefs binds
		= sfoldr (\ {lb_src=expr,lb_dst=freeVar}
					-> beFunction3 BENodeDefList (getVariableSequenceNumber freeVar.fv_info_ptr) (convertExpr expr main_dcl_module_n))
				 beNoNodeDefs binds

collectStrictNodeIds :: Expression -> [FreeVar]
collectStrictNodeIds (Let {let_strict_binds, let_expr})
	=	[lb_dst \\ {lb_dst} <- let_strict_binds]
collectStrictNodeIds _
	=	[]

convertStrictNodeIds :: [FreeVar] -> BEMonad BEStrictNodeIdP
convertStrictNodeIds freeVars
	=	sfoldr (\ {fv_info_ptr} -> beFunction2 BEStrictNodeIdList (convertVar fv_info_ptr)) beNoStrictNodeIds freeVars

convertRhsStrictNodeIds :: Expression -> BEMonad BEStrictNodeIdP
convertRhsStrictNodeIds expression
	=	convertStrictNodeIds (collectStrictNodeIds expression)

convertLiteralSymbol :: BasicValue -> BEMonad BESymbolP
convertLiteralSymbol (BVI intString)
	=	beLiteralSymbol BEIntDenot intString
convertLiteralSymbol (BVInt int)
	=	beLiteralSymbol BEIntDenot (toString int)
convertLiteralSymbol (BVB bool)
	=	beBoolSymbol bool
convertLiteralSymbol (BVC charString)
	=	beLiteralSymbol BECharDenot charString
convertLiteralSymbol (BVR realString)
	=	beLiteralSymbol BERealDenot realString
convertLiteralSymbol (BVS string)
	=	beLiteralSymbol BEStringDenot string 

convertTypeSymbolIdent :: TypeSymbIdent -> BEMonad BETypeSymbolP
convertTypeSymbolIdent {type_index={glob_module, glob_object}}
	=	beTypeSymbol glob_object glob_module // ->> ("convertTypeSymbolIdent", (glob_module, glob_object))

convertExternalTypeSymbolIdent :: TypeSymbIdent -> BEMonad BETypeSymbolP
convertExternalTypeSymbolIdent {type_index={glob_module, glob_object}}
	= beExternalTypeSymbol glob_object glob_module

convertExpr :: Expression Int -> BEMonad BENodeP
convertExpr  expr main_dcl_module_n
	= convertExpr expr
where
	convertExpr :: Expression -> BEMonad BENodeP
	convertExpr  (BasicExpr value)
		=	beNormalNode (convertLiteralSymbol value) beNoArgs
	convertExpr  (App {app_symb, app_args})
		=	beNormalNode (convertSymbol app_symb) (convertArgs app_args)
		where
			convertSymbol :: !SymbIdent -> BEMonad BESymbolP
			convertSymbol {symb_kind=SK_Function {glob_module, glob_object}}
				=	beFunctionSymbol glob_object glob_module
			convertSymbol {symb_kind=SK_LocalMacroFunction glob_object}
				=	beFunctionSymbol glob_object main_dcl_module_n
			convertSymbol {symb_kind=SK_GeneratedFunction _ index}
				=	beFunctionSymbol index main_dcl_module_n
			convertSymbol {symb_kind=SK_Constructor {glob_module, glob_object}}
				=	beConstructorSymbol glob_module glob_object // ->> ("convertSymbol", (glob_module, glob_object))
			convertSymbol symbol
				=	undef // <<- ("backendconvert, convertSymbol: unknown symbol") // , symbol)
	convertExpr (Var var)
		=	beNodeIdNode (convertVar var.var_info_ptr) beNoArgs
	convertExpr (f @ [a])
		=	beNormalNode (beBasicSymbol BEApplySymb) (convertArgs [f, a])
	convertExpr (f @ [a:as])
		=	convertExpr (f @ [a] @ as)
	convertExpr (Selection selectorKind expression selections)
		=	convertSelections (convertExpr expression) (addKinds selectorKind selections)
		where
			addKinds NormalSelector selections
				=	[(BESelector, selection) \\ selection <- selections]
			addKinds UniqueSingleArraySelector selections
				=	[(BESelector, selection) \\ selection <- selections]
			addKinds UniqueSingleArraySelectorUniqueElementResult selections
				=	[(BESelector, selection) \\ selection <- selections]
			addKinds _ [selection]
				=	[(BESelector_U, selection)]
			addKinds _ [selection : selections]
				=	[(BESelector_F, selection) : addMoreKinds selections]
				where
					addMoreKinds []
						=	[]
					addMoreKinds [selection]
						=	[(BESelector_L, selection)]
					addMoreKinds [selection : selections]
						=	[(BESelector_N, selection) : addMoreKinds selections]
			addKinds _ []
				=	[]
	convertExpr (RecordUpdate _ expr updates)
		=	beUpdateNode (beArgs (convertExpr expr) (convertUpdates updates))
		where
			convertUpdates []
				=	beNoArgs
			convertUpdates [{bind_src=NoBind _}:updates]
				=	convertUpdates updates
			convertUpdates [{bind_src, bind_dst=bind_dst=:{glob_module, glob_object={fs_index}}}:updates]
				=	(beArgs
						(beSelectorNode BESelector (beFieldSymbol fs_index glob_module)
						(beArgs (convertExpr bind_src)
						beNoArgs))
					(convertUpdates updates))
	convertExpr (Update expr1 [singleSelection] expr2)
		=	case singleSelection of
				RecordSelection _ _
					->	beUpdateNode (convertArgs [expr1, Selection NormalSelector expr2 [singleSelection]])
				ArraySelection {glob_object={ds_index}, glob_module} _ index
					->	beNormalNode
							(beFunctionSymbol ds_index glob_module)
							(convertArgs [expr1, index, expr2])
				DictionarySelection dictionaryVar dictionarySelections _ index
					->	convertExpr (Selection NormalSelector (Var dictionaryVar) dictionarySelections @ [expr1, index, expr2])
	convertExpr (Update expr1 selections expr2)
		=	case lastSelection of
				RecordSelection _ _
					->	beUpdateNode (beArgs selection (convertArgs [Selection NormalSelector expr2 [lastSelection]]))
				ArraySelection {glob_object={ds_index}, glob_module} _ index
					->	beNormalNode (beSpecialArrayFunctionSymbol BE_ArrayUpdateFun ds_index glob_module) (beArgs selection (convertArgs [index, expr2]))
				DictionarySelection dictionaryVar dictionarySelections _ index
					->	beNormalNode beDictionaryUpdateFunSymbol
								(beArgs dictionary (beArgs selection (convertArgs [index, expr2])))
						with
							dictionary
								=	convertExpr (Selection NormalSelector (Var dictionaryVar) dictionarySelections)
		where
			lastSelection
				=	last selections
			selection
				=	convertSelections (convertExpr expr1) (addKinds (init selections))
			addKinds [selection : selections]
				=	[(BESelector_F, selection) : addMoreKinds selections]
				where
					addMoreKinds selections
						=	[(BESelector_N, selection) \\ selection <- selections]
			addKinds []
				=	[]
	convertExpr (TupleSelect {ds_arity} n expr)
		=	beTupleSelectNode ds_arity n (convertExpr expr)
	convertExpr (MatchExpr {glob_module, glob_object={ds_index,ds_arity}} expr)
		| glob_module==cPredefinedModuleIndex
			&& (let pd_cons_index=ds_index+FirstConstructorPredefinedSymbolIndex in
				pd_cons_index==PD_UnboxedConsSymbol || pd_cons_index==PD_UnboxedTailStrictConsSymbol || pd_cons_index==PD_OverloadedConsSymbol ||
				pd_cons_index==PD_UnboxedJustSymbol || pd_cons_index==PD_OverloadedJustSymbol)
			= case expr of
				App {app_args=[src_expr],app_symb={symb_kind=SK_Function {glob_module=decons_module,glob_object=deconsindex}}}
					->	beMatchNode ds_arity (beOverloadedConsSymbol glob_module ds_index decons_module deconsindex) (convertExpr src_expr)
				_
					->	convertExpr expr
			=	beMatchNode ds_arity (beConstructorSymbol glob_module ds_index) (convertExpr expr)
	convertExpr (Conditional {if_cond=cond, if_then, if_else=Yes else})
		=	beIfNode (convertExpr cond) (convertExpr if_then) (convertExpr else)

	convertArgs :: [Expression] -> BEMonad BEArgP
	convertArgs exprs
		=	sfoldr (beArgs o convertExpr) beNoArgs exprs

	convertSelections :: (BEMonad BENodeP) [(BESelectorKind, Selection)] -> (BEMonad BENodeP)
	convertSelections expression selections
		=	foldl convertSelection expression selections
	
	convertSelection :: (BEMonad BENodeP) (BESelectorKind, Selection) -> (BEMonad BENodeP)
	convertSelection expression (kind, RecordSelection {glob_object={ds_index}, glob_module} _)
		=	beSelectorNode kind (beFieldSymbol ds_index glob_module) (beArgs expression beNoArgs)
	convertSelection expression (kind, ArraySelection {glob_object={ds_index}, glob_module} _ index)
		=	beNormalNode (beArraySelectionSymbol kind ds_index glob_module) (beArgs expression (convertArgs [index]))
	where
		beArraySelectionSymbol BESelector ds_index glob_module
			= beFunctionSymbol ds_index glob_module
		beArraySelectionSymbol BESelector_U ds_index glob_module
			= beSpecialArrayFunctionSymbol BE_UnqArraySelectFun ds_index glob_module
		beArraySelectionSymbol BESelector_F ds_index glob_module
			= beSpecialArrayFunctionSymbol BE_UnqArraySelectFun ds_index glob_module
		beArraySelectionSymbol BESelector_L ds_index glob_module
			= beSpecialArrayFunctionSymbol BE_UnqArraySelectLastFun ds_index glob_module
		beArraySelectionSymbol BESelector_N ds_index glob_module
			= beSpecialArrayFunctionSymbol BE_UnqArraySelectLastFun ds_index glob_module
	convertSelection expression (kind, DictionarySelection dictionaryVar dictionarySelections _ index)
		=	case kind of
				BESelector
					->	beNormalNode (beBasicSymbol BEApplySymb)
								(beArgs
									(beNormalNode (beBasicSymbol BEApplySymb)
									(beArgs dictionary
										(beArgs expression beNoArgs)))
								(convertArgs [index]))
				BESelector_F
					# uselect_selection = replace_select_by_uselect dictionarySelections
					# uselect_member = convertExpr (Selection NormalSelector (Var dictionaryVar) uselect_selection)
					->	beNormalNode (beBasicSymbol BEApplySymb)
								(beArgs
									(beNormalNode (beBasicSymbol BEApplySymb)
									(beArgs uselect_member
										(beArgs expression beNoArgs)))
								(convertArgs [index]))
				_
					->	beNormalNode beDictionarySelectFunSymbol
								(beArgs dictionary (beArgs expression (convertArgs [index])))
			where
				dictionary
					=	convertExpr (Selection NormalSelector (Var dictionaryVar) dictionarySelections)

				replace_select_by_uselect :: ![Selection] -> [Selection]
				replace_select_by_uselect [RecordSelection rs=:{glob_object={ds_index}} field_number]
					// Array member field indices: 0 _createArray, 1 createArray, 2 replace, 3 select, 4 size, 5 update 6 uselect, 7 usize
					| ds_index==3 && field_number==3
						= [RecordSelection {rs & glob_object.ds_index=6} 6]	// ds_ident not updated, but is not used
				replace_select_by_uselect [selection:selections]
					= [selection:replace_select_by_uselect selections]

:: DefaultCase
	=	DefaultCase Expression
	|	DefaultCaseFail !Ident
	|	DefaultCaseNone

class convertCases a :: a Ident BoundVar DefaultCase Int -> BEMonad BEArgP

instance convertCases CasePatterns where
	convertCases (AlgebraicPatterns _ patterns) aliasDummyId var default_case main_dcl_module_n
		=	convertCases patterns aliasDummyId var default_case main_dcl_module_n
	convertCases (BasicPatterns _ patterns) aliasDummyId var default_case main_dcl_module_n
		=	convertCases patterns aliasDummyId var default_case main_dcl_module_n
	convertCases (OverloadedPatterns _ decons_expr patterns) aliasDummyId var default_case main_dcl_module_n
		=	convertOverloadedPatterns patterns decons_expr aliasDummyId var default_case main_dcl_module_n
	// +++ other patterns ???

instance convertCases [a] | convertCase a where
	convertCases patterns aliasDummyId var optionalCase main_dcl_module_n
		=	sfoldr (beArgs o convertCase main_dcl_module_n (localRefCounts patterns optionalCase)
						 aliasDummyId var) (convertDefaultCase optionalCase aliasDummyId main_dcl_module_n) patterns

localRefCounts :: [pattern] DefaultCase -> Bool
localRefCounts [_] DefaultCaseNone
	=	False
localRefCounts [_] (DefaultCaseFail _)
	=	False
localRefCounts _ _
	=	True

class convertCase a :: Int Bool Ident BoundVar a -> BEMonad BENodeP

caseNode localRefCounts arity symbolM defsM strictsM rhsM be
	| localRefCounts
		# be
		 	=	appBackEnd BEEnterLocalScope be
		# (symbol, be)
			=	symbolM be
		# (rhs, be)
			=	rhsM be
		# (defs, be)
			=	defsM be
		# (stricts, be)
			=	strictsM be
		# (kees, be)
			=	accBackEnd (BECaseNode arity symbol defs stricts rhs) be
		# be
		 	=	appBackEnd (BELeaveLocalScope kees) be
		=	(kees, be)
	// otherwise
		# (symbol, be)
			=	symbolM be
		# (rhs, be)
			=	rhsM be
		# (defs, be)
			=	defsM be
		# (stricts, be)
			=	strictsM be
		# (kees, be)
			=	accBackEnd (BECaseNode arity symbol defs stricts rhs) be
		=	(kees, be)

defaultNode defsM strictsM rhsM be
	# be
		=	appBackEnd BEEnterLocalScope be
	# (defaul, be)
		=	beDefaultNode defsM strictsM rhsM be
	# be
	 	=	appBackEnd (BELeaveLocalScope defaul) be
	=	(defaul, be)

pushNode arity var symbolM argM nodeIdsM be
	# (symbol, be)
		=	symbolM be
	# (nodeIds, be)
		=	nodeIdsM be
	# (sequenceNumber, be)
		=	getVariableSequenceNumber var.var_info_ptr be
	# be
		=	appBackEnd (BEAddNodeIdsRefCounts sequenceNumber symbol nodeIds) be
	# (arg, be)
		=	argM be
	=	accBackEnd (BEPushNode arity symbol arg nodeIds) be

overloadedPushNode arity var symbolM argM nodeIdsM deconsNodeM be
	:== let
			(symbol, be1)
				=	symbolM be
			(nodeIds, be2)
				=	nodeIdsM be1
			(sequenceNumber, be3)
				=	getVariableSequenceNumber var.var_info_ptr be2
			be4
				=	appBackEnd (BEAddNodeIdsRefCounts sequenceNumber symbol nodeIds) be3
			(arg, be5)
				=	argM be4
			(deconsNodeP,be6)
				= deconsNodeM be5
	in		accBackEnd (BEOverloadedPushNode arity symbol arg nodeIds deconsNodeP) be6

instance convertCase AlgebraicPattern where
	convertCase main_dcl_module_n localRefCounts aliasDummyId var {ap_symbol={glob_module,glob_object={ds_index}}, ap_vars, ap_expr}
		| symbolArity == 0
			=	caseNode localRefCounts 0
					(beConstructorSymbol glob_module ds_index)
					(convertRhsNodeDefs aliasDummyId ap_expr main_dcl_module_n)
					(convertRhsStrictNodeIds ap_expr)
					(convertRootExpr aliasDummyId ap_expr main_dcl_module_n)
		// otherwise
			=	caseNode localRefCounts symbolArity
					(beConstructorSymbol glob_module ds_index) 
					(convertRhsNodeDefs aliasDummyId ap_expr main_dcl_module_n)
					(convertRhsStrictNodeIds ap_expr)
					(pushNode symbolArity var
						(beConstructorSymbol glob_module ds_index)
						(beArgs (convertExpr (Var var) main_dcl_module_n) (beArgs (convertRootExpr aliasDummyId ap_expr main_dcl_module_n) beNoArgs))
						(convertPatternVars ap_vars))
		where
			symbolArity
				=	length ap_vars		// curried patterns ???

instance convertCase BasicPattern where
	convertCase main_dcl_module_n localRefCounts aliasDummyId _ {bp_value, bp_expr}
		=	caseNode localRefCounts 0
				(convertLiteralSymbol bp_value)
				(convertRhsNodeDefs aliasDummyId bp_expr main_dcl_module_n)
				(convertRhsStrictNodeIds bp_expr)
				(convertRootExpr aliasDummyId bp_expr main_dcl_module_n)

convertOverloadedPatterns patterns decons_expr aliasDummyId var optionalCase main_dcl_module_n
	=	sfoldr (beArgs o convertOverloadedListPattern decons_expr (localRefCounts patterns optionalCase))
				(convertDefaultCase optionalCase aliasDummyId main_dcl_module_n) patterns
where
	convertOverloadedListPattern :: Expression Bool AlgebraicPattern -> BEMonad BENodeP
	convertOverloadedListPattern decons_expr localRefCounts {ap_symbol={glob_module,glob_object={ds_index}}, ap_vars=[], ap_expr}
		=	caseNode localRefCounts 0
				(beConstructorSymbol glob_module ds_index)
				(convertRhsNodeDefs aliasDummyId ap_expr main_dcl_module_n)
				(convertRhsStrictNodeIds ap_expr)
				(convertRootExpr aliasDummyId ap_expr main_dcl_module_n)
	convertOverloadedListPattern decons_expr=:(App {app_args=[],app_symb={symb_kind=SK_Function {glob_module=decons_module,glob_object=deconsindex}}}) localRefCounts {ap_symbol={glob_module,glob_object={ds_index}}, ap_vars, ap_expr}
		=	caseNode localRefCounts symbolArity
				(beOverloadedConsSymbol glob_module ds_index decons_module deconsindex)
				(convertRhsNodeDefs aliasDummyId ap_expr main_dcl_module_n)
				(convertRhsStrictNodeIds ap_expr)
				(pushNode symbolArity var
					(beOverloadedConsSymbol glob_module ds_index decons_module deconsindex)
					(beArgs (convertExpr (Var var) main_dcl_module_n) (beArgs (convertRootExpr aliasDummyId ap_expr main_dcl_module_n) beNoArgs))
					(convertPatternVars ap_vars))
		where
			symbolArity = length ap_vars
	convertOverloadedListPattern decons_expr localRefCounts {ap_symbol={glob_module,glob_object={ds_index}}, ap_vars, ap_expr}
		=	caseNode localRefCounts symbolArity
				(beConstructorSymbol glob_module ds_index)
				(convertRhsNodeDefs aliasDummyId ap_expr main_dcl_module_n)
				(convertRhsStrictNodeIds ap_expr)
				(overloadedPushNode symbolArity var
					(beConstructorSymbol glob_module ds_index)
					(beArgs (convertExpr (Var var) main_dcl_module_n) (beArgs (convertRootExpr aliasDummyId ap_expr main_dcl_module_n) beNoArgs))
					(convertPatternVars ap_vars)
					(convertExpr decons_expr main_dcl_module_n))
		where
			symbolArity = length ap_vars

convertPatternVars :: [FreeVar] -> BEMonad BENodeIdListP
convertPatternVars vars
	=	sfoldr (\ {fv_info_ptr} -> beFunction2 BENodeIdList (convertVar fv_info_ptr)) beNoNodeIds vars

convertDefaultCase DefaultCaseNone _ _
	=	beNoArgs
convertDefaultCase (DefaultCaseFail ident) aliasDummyId main_dcl_module_n
	=	beArgs
			(defaultNode
				beNoNodeDefs
				beNoStrictNodeIds
				(beNormalNode (beLiteralSymbol BEFailSymb ident.id_name) beNoArgs))
			beNoArgs
convertDefaultCase (DefaultCase expr) aliasDummyId main_dcl_module_n
	=	beArgs
			(defaultNode
				(convertRhsNodeDefs aliasDummyId expr main_dcl_module_n)
				(convertRhsStrictNodeIds expr)
				(convertRootExpr aliasDummyId expr main_dcl_module_n))
			beNoArgs

convertVar :: VarInfoPtr -> BEMonad BENodeIdP
convertVar varInfo
	= \be0 -> let (variable_sequence_number,be) = getVariableSequenceNumber varInfo be0 in
		beNodeId variable_sequence_number be

getVariableSequenceNumber :: VarInfoPtr *BackEndState-> (!Int,!*BackEndState)
getVariableSequenceNumber varInfoPtr be
	# (vi,be) = read_from_var_heap varInfoPtr be
	= case vi of
		VI_SequenceNumber sequenceNumber
			-> (sequenceNumber,be)
		VI_AliasSequenceNumber {var_info_ptr}
			-> getVariableSequenceNumber var_info_ptr be

set_dictionary_field_for_instance_member_functions :: !Int !{#ClassInstance} !{#ClassDef} !{#CheckedTypeDef} !{#SelectorDef} !{#FunDef} !Int !{#DclModule} !*BackEndState -> *BackEndState
set_dictionary_field_for_instance_member_functions i instance_defs class_defs type_defs selector_defs icl_functions main_dcl_module_n dcls bes
	| i<size instance_defs
		# bes = set_dictionary_field_for_instance_member_functions_for_instance instance_defs.[i] class_defs type_defs selector_defs icl_functions main_dcl_module_n dcls bes
		= set_dictionary_field_for_instance_member_functions (i+1) instance_defs class_defs type_defs selector_defs icl_functions main_dcl_module_n dcls bes
		= bes
where
	set_dictionary_field_for_instance_member_functions_for_instance :: !ClassInstance !{#ClassDef} !{#CheckedTypeDef} !{#SelectorDef} !{#FunDef} !Int !{#DclModule} !*BackEndState -> *BackEndState
	set_dictionary_field_for_instance_member_functions_for_instance {ins_class_index={gi_module=class_module,gi_index},ins_members} class_defs com_type_defs com_selector_defs icl_functions main_dcl_module_n dcls bes
		| class_module==main_dcl_module_n
			# {class_dictionary={ds_index}} = class_defs.[gi_index]
			  selector_defs = com_selector_defs
			  {td_rhs=RecordType {rt_fields}} = com_type_defs.[ds_index]
			= set_dictionary_field_for_instance_member_functions_for_instance_members 0 ins_members rt_fields selector_defs class_module bes
			# {class_dictionary={ds_index}} = dcls.[class_module].dcl_common.com_class_defs.[gi_index]
			  selector_defs = dcls.[class_module].dcl_common.com_selector_defs
			  {td_rhs=RecordType {rt_fields}} = dcls.[class_module].dcl_common.com_type_defs.[ds_index]
			= set_dictionary_field_for_instance_member_functions_for_instance_members 0 ins_members rt_fields selector_defs class_module bes

	set_dictionary_field_for_instance_member_functions_for_instance_members :: !Int !{#ClassInstanceMember} !{#FieldSymbol} !{#SelectorDef} !Int !*BackEndState -> *BackEndState
	set_dictionary_field_for_instance_member_functions_for_instance_members i ins_members fields selector_defs class_module bes
		| i<size ins_members
			# {cim_arity,cim_index} = ins_members.[i]
			  {fs_index} = fields.[i]
			  {sd_type_ptr} = selector_defs.[fs_index]
			  (sd_type_in_ptr,bes) = read_from_var_heap sd_type_ptr bes
			| cim_index<0
				| cim_arity==main_dcl_module_n
					# cim_index = -1-cim_index
					| sd_type_in_ptr=:VI_ExpandedMemberType _ _
						# (r0,bes) = accBackEnd (BESetDictionaryFieldOfMember cim_index fs_index class_module) bes
						= set_dictionary_field_for_instance_member_functions_for_instance_members (i+1) ins_members fields selector_defs class_module bes
						= abort "No VI_ExpandedMemberType in set_dictionary_field_for_instance_member_functions_for_instance_members"
					= set_dictionary_field_for_instance_member_functions_for_instance_members (i+1) ins_members fields selector_defs class_module bes
			| sd_type_in_ptr=:VI_ExpandedMemberType _ _
				# (r0,bes) = accBackEnd (BESetDictionaryFieldOfMember cim_index fs_index class_module) bes
				= set_dictionary_field_for_instance_member_functions_for_instance_members (i+1) ins_members fields selector_defs class_module bes
				= abort "No VI_ExpandedMemberType in set_dictionary_field_for_instance_member_functions_for_instance_members"
		= bes

set_dictionary_field_for_instance_member_functions_for_implementation_module :: !CommonDefs !{#FunDef} !ModuleIndex !{#DclModule} !*BackEndState -> *BackEndState
set_dictionary_field_for_instance_member_functions_for_implementation_module {com_instance_defs,com_class_defs,com_type_defs,com_selector_defs}
		icl_functions main_dcl_module_n dcls bes
	= set_dictionary_field_for_instance_member_functions 0 com_instance_defs com_class_defs com_type_defs com_selector_defs icl_functions main_dcl_module_n dcls bes

set_dictionary_field_for_special_instance_member_functions :: !DclModule !CommonDefs !{#FunDef} !ModuleIndex !{#DclModule} !*BackEndState -> *BackEndState
set_dictionary_field_for_special_instance_member_functions {dcl_module_kind=MK_None} icl_common icl_functions main_dcl_module_n dcls bes
	= bes
set_dictionary_field_for_special_instance_member_functions {dcl_common={com_instance_defs},dcl_sizes} {com_class_defs,com_type_defs,com_selector_defs} icl_functions main_dcl_module_n dcls bes
	= set_dictionary_field_for_instance_member_functions dcl_sizes.[cInstanceDefs] com_instance_defs com_class_defs com_type_defs com_selector_defs icl_functions main_dcl_module_n dcls bes

convertForeignExports :: [ForeignExport] Int BackEnd -> BackEnd
convertForeignExports [{fe_fd_index,fe_stdcall}:icl_foreign_exports] main_dcl_module_n backEnd
	# backEnd = convertForeignExports icl_foreign_exports main_dcl_module_n backEnd
	# (function_symbol_p,backEnd) = BEFunctionSymbol fe_fd_index main_dcl_module_n backEnd
	= BEInsertForeignExport function_symbol_p (if fe_stdcall 1 0) backEnd
convertForeignExports [] main_dcl_module_n backEnd
	= backEnd

foldStateWithIndex function n
	:== foldStateWithIndexTwice 0
	where
		foldStateWithIndexTwice index
			| index == n
				=	identity
			// otherwise
				=	function index
				o`	foldStateWithIndexTwice (index+1)

markExports :: DclModule {#ClassDef} {#CheckedTypeDef} {#ClassDef} {#CheckedTypeDef} -> BackEnder
markExports {dcl_functions,dcl_common={com_type_defs,com_cons_defs,com_selector_defs,com_class_defs}} dclClasses dclTypes iclClasses iclTypes
	=	foldStateWithIndex (beExportType False) (size com_type_defs)
	o	foldStateWithIndex export_constructor (size com_cons_defs)
	o	foldStateWithIndex (beExportField False) (size com_selector_defs)
	o	foldStateWithIndex (exportDictionary iclClasses iclTypes) (size com_class_defs)
	o	foldStateWithIndex beExportFunction (size dcl_functions)
	where
		exportDictionary :: {#ClassDef} {#CheckedTypeDef} Index -> BackEnder
		exportDictionary iclClasses iclTypes classIndex
			=	beExportType True classIndex
			o	foldStateA exportDictionaryField rt_fields
			where
				iclTypeIndex
					=	iclClasses.[classIndex].class_dictionary.ds_index
				{td_rhs = RecordType {rt_fields}}
					=	iclTypes.[iclTypeIndex]

				exportDictionaryField :: FieldSymbol -> BackEnder
				exportDictionaryField {fs_index}
					=	beExportField True fs_index

		export_constructor constructor_index
			| not (IsNewTypeOrAbstractNewTypeCons com_cons_defs.[constructor_index].cons_number)
				= beExportConstructor constructor_index
				= \ bs=:{bes_backEnd} -> bs
