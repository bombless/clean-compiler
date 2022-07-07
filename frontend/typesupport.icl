implementation module typesupport

import StdEnv, StdStrictLists, compare_types
import syntax, expand_types, unitype, utilities, checktypes

::	Store	:== Int

::	AttrCoercion =
	{	ac_demanded	:: !Int
	,	ac_offered	:: !Int
	}

::	TempSymbolType =
	{	tst_args		:: ![AType]
	,	tst_arity		:: !Int
	,	tst_lifted		:: !Int
	,	tst_result		:: !AType
	,	tst_context		:: ![TypeContext]
	,	tst_var_contexts :: !(VarContexts TypeContext)
	,	tst_attr_env	:: ![AttrCoercion]
	}

::	FunctionType = CheckedType !SymbolType !Int
				 | UncheckedType !TempSymbolType
				 | ..

::	AttributeEnv	:== {! TypeAttribute }
::	VarEnv 			:== {! Type }

::	CleanUpExprTypeState =
	{	cuets_var_env		:: !.VarEnv
	,	cuets_heaps			:: !.TypeHeaps
	,	cuets_var_store		:: !Int
	}

class clean_up_expr_type a ::  !a !*CleanUpExprTypeState -> (!a, !*CleanUpExprTypeState)

instance clean_up_expr_type AType
where
	clean_up_expr_type {at_attribute,at_type} cus
		# at_attribute = cleanUpExprTypeAttribute at_attribute
		  (at_type, cus) = clean_up_expr_type at_type cus
		= ({at_attribute = at_attribute, at_type = at_type}, cus)

cleanUpExprTypeAttribute :: !TypeAttribute -> TypeAttribute
cleanUpExprTypeAttribute TA_Unique
	= TA_Unique
cleanUpExprTypeAttribute TA_Multi
	= TA_Multi
cleanUpExprTypeAttribute (TA_TempVar _)
	= TA_Multi
cleanUpExprTypeAttribute av=:(TA_Var _)
	= av
cleanUpExprTypeAttribute type_attribute
	= abort ("cleanUpExprTypeAttribute "+++toString type_attribute)

instance clean_up_expr_type Type
where
	clean_up_expr_type (TempV tv_number) cuets
		# (type, cuets) = cuets!cuets_var_env.[tv_number]
		= cleanUpExprTypeVariable type tv_number cuets
	clean_up_expr_type (TA tc types) cuets
		# (types, cuets) = clean_up_expr_type types cuets
		= (TA tc types, cuets)
	clean_up_expr_type (TAS tc types strictness) cuets
		# (types, cuets) = clean_up_expr_type types cuets
		= (TAS tc types strictness, cuets)
	clean_up_expr_type (argtype --> restype) cuets
		# (argtype, cuets) = clean_up_expr_type argtype cuets
		  (restype, cuets) = clean_up_expr_type restype cuets
		=  (argtype --> restype, cuets)
	clean_up_expr_type t=:(TB _) cuets
		=  (t, cuets)
	clean_up_expr_type (TArrow1 argtype) cuets
		# (argtype, cuets) = clean_up_expr_type argtype cuets
		=  (TArrow1 argtype, cuets)
	clean_up_expr_type t=:TArrow cuets
		=  (t, cuets)
	clean_up_expr_type (TempCV tempvar :@: types) cuets
		# (type, cuets) = cuets!cuets_var_env.[tempvar]
		  (type, cuets) = cleanUpExprTypeVariable type tempvar cuets
		  (types, cuets) = clean_up_expr_type types cuets
		= (simplifyTypeApplication type types, cuets)
	clean_up_expr_type (TempQCV qv_number :@: types) cuets
		# (type, cuets) = cuets!cuets_var_env.[qv_number]
		  (TV tv, cuets) = cleanUpExprTypeVariable type qv_number cuets
		  (types, cuets) = clean_up_expr_type types cuets
		= (CV tv :@: types, cuets)
	clean_up_expr_type (TempQCDV qv_number :@: types) cuets
		# (type, cuets) = cuets!cuets_var_env.[qv_number]
		  (TV tv, cuets) = cleanUpExprTypeVariable type qv_number cuets
		  (types, cuets) = clean_up_expr_type types cuets
		= (CV tv :@: types, cuets)
	clean_up_expr_type (cv :@: types) cuets
		# (types, cuets) = clean_up_expr_type types cuets
		= (cv :@: types, cuets)
	clean_up_expr_type (TempQV qv_number) cuets
		# (type, cuets) = cuets!cuets_var_env.[qv_number]
		= cleanUpExprTypeVariable type qv_number cuets
	clean_up_expr_type (TempQDV qv_number) cuets
		# (type, cuets) = cuets!cuets_var_env.[qv_number]
		= cleanUpExprTypeVariable type qv_number cuets
	clean_up_expr_type tv=:(TV _) cuets
		= (tv, cuets)
	clean_up_expr_type TAll cuets
		= (TAll, cuets)
	clean_up_expr_type (TFA vars type) cuets
		# (type, cuets) = clean_up_expr_type type cuets
		= (TFA vars type, cuets)
	clean_up_expr_type type cuets
		= abort "clean_up_expr_type Type (typesupport.icl): unknown type"

cleanUpExprTypeVariable TE tv_number {cuets_heaps,cuets_var_store,cuets_var_env}
	# (tv_info_ptr, th_vars) = newPtr TVI_Empty cuets_heaps.th_vars
	  new_var = TV {tv_ident = NewVarId cuets_var_store, tv_info_ptr = tv_info_ptr}
	  cuets_var_env & [tv_number] = new_var
	  cuets_heaps & th_vars = th_vars
	= (new_var, {cuets_var_env = cuets_var_env, cuets_heaps = cuets_heaps, cuets_var_store = inc cuets_var_store})
cleanUpExprTypeVariable (TLifted var) tv_number cuets
	= (TV var, cuets)
cleanUpExprTypeVariable type tv_number cuets
	= (type, cuets)

instance clean_up_expr_type [a] | clean_up_expr_type a
where
	clean_up_expr_type l cuets = mapSt clean_up_expr_type l cuets

instance clean_up_expr_type CaseType
where
	clean_up_expr_type ctype=:{ct_pattern_type,ct_result_type, ct_cons_types} cuets
		# (ct_pattern_type, cuets) = clean_up_expr_type ct_pattern_type cuets
		  (ct_result_type, cuets) = clean_up_expr_type ct_result_type cuets
		  (ct_cons_types, cuets) = mapSt (mapSt clean_up_arg_type) ct_cons_types cuets
		= ({ctype & ct_pattern_type = ct_pattern_type, ct_cons_types = ct_cons_types, ct_result_type = ct_result_type}, cuets)
	where
		clean_up_arg_type {at_type = TFA avars type, at_attribute} cuets
			# at_attribute = cleanUpExprTypeAttribute at_attribute
			  (type, cuets) = clean_up_expr_type type cuets
			= ({at_type = TFA avars type, at_attribute = at_attribute}, cuets)
		clean_up_arg_type {at_type = TFAC avars type contexts, at_attribute} cuets
			# at_attribute = cleanUpExprTypeAttribute at_attribute
			  (type, cuets) = clean_up_expr_type type cuets
			= ({at_type = TFAC avars type contexts, at_attribute = at_attribute}, cuets)
		clean_up_arg_type at cuets
			= clean_up_expr_type at cuets

instance clean_up_expr_type DictionaryAndClassType
where
	clean_up_expr_type {dc_var,dc_class_type} cuets
		# (dc_class_type,cuets) = clean_up_expr_type dc_class_type cuets
		= ({dc_var=dc_var,dc_class_type=dc_class_type},cuets)

::	CleanUpState =
	{	cus_var_env					:: !.VarEnv
	,	cus_attr_env				:: !.AttributeEnv
	,	cus_appears_in_lifted_part	:: !.LargeBitvect
	,	cus_heaps					:: !.TypeHeaps
	,	cus_var_store				:: !Int
	,	cus_attr_store				:: !Int
	,	cus_exis_vars				:: ![(Int,TypeAttribute)]
	,	cus_error					:: !.ErrorAdmin
	}

::	CleanUpInput =
	{	cui_coercions		:: !{! CoercionTree}
	,	cui_attr_part		:: !AttributePartition
	,	cui_is_lifted_part	:: !Bool
	}

::	VarInfo | VI_ContextSpecified

class clean_up a ::  !CleanUpInput !a !*CleanUpState -> (!a, !*CleanUpState)

instance clean_up AType
where
	clean_up cui atype=:{at_attribute, at_type = TempQV qv_number} cus
		= clean_up_top_level_q_variable cui at_attribute qv_number cus
	clean_up cui atype=:{at_attribute, at_type = TempQDV qv_number} cus
		= clean_up_top_level_q_variable cui at_attribute qv_number cus
	clean_up cui atype=:{at_attribute,at_type} cus
		# (at_attribute, cus) = cleanUpTypeAttribute False cui at_attribute cus 
		  (at_type, cus) = clean_up cui at_type cus
		= ({atype & at_attribute = at_attribute, at_type = at_type}, cus)

clean_up_top_level_q_variable cui at_attribute qv_number cus
	# (at_attribute, cus)	= cleanUpTypeAttribute True cui at_attribute cus
	# (type, cus)			= cus!cus_var_env.[qv_number]
	  (var, cus)			= cleanUpVariable type qv_number cus
	  cus = {cus & cus_exis_vars = add_new_exis_attr_var type qv_number at_attribute cus.cus_exis_vars}
	= ({at_attribute = at_attribute, at_type = var}, cus)
where
	add_new_exis_attr_var TE ev_number ev_attr cus_exis_vars
		= [(ev_number, ev_attr) : cus_exis_vars]
	add_new_exis_attr_var type ev_number ev_attr cus_exis_vars
		= cus_exis_vars

attrIsUndefined TA_None = True
attrIsUndefined _ 		= False

cleanUpTypeAttribute :: !Bool !CleanUpInput TypeAttribute !*CleanUpState -> (!TypeAttribute, !*CleanUpState)
cleanUpTypeAttribute _ cui TA_Unique cus
	= (TA_Unique, cus)
cleanUpTypeAttribute _ cui TA_Multi cus
	= (TA_Multi, cus)
cleanUpTypeAttribute may_be_existential cui tv=:(TA_TempVar av_number) cus
	# av_group_nr = cui.cui_attr_part.[av_number]
	  coercion_tree = cui.cui_coercions.[av_group_nr]
	| isNonUnique coercion_tree
		= (TA_Multi, cus)
	| isUnique coercion_tree
		= (TA_Unique, cus)
	# cus 			= check_appearance cui.cui_is_lifted_part av_group_nr cus
	# (attr, cus)	= clean_up_attribute_variable av_group_nr (cus!cus_attr_env.[av_group_nr])
	| isExistential coercion_tree
		| may_be_existential
			= (attr, { cus & cus_error = checkError "attribute variable could not be universally quantified" "" cus.cus_error})
			= (attr, cus)
		= (attr, cus)
where
	check_appearance is_lifted_part group_nr cus=:{cus_appears_in_lifted_part, cus_error}
		| is_lifted_part
			= { cus & cus_appears_in_lifted_part = bitvectSet group_nr cus_appears_in_lifted_part}
		| bitvectSelect group_nr cus_appears_in_lifted_part
			= { cus &	cus_appears_in_lifted_part = bitvectReset group_nr cus_appears_in_lifted_part,
						cus_error = checkError "attribute variable of lifted argument appears in the specified type" "" cus_error}
			= cus

	clean_up_attribute_variable av_group_nr (TA_None, cus=:{cus_heaps,cus_attr_store,cus_attr_env})
		# (av, th_attrs) = NewAttrVar cus_attr_store cus_heaps.th_attrs
		  new_attr_var = TA_Var av
		= (new_attr_var, { cus &	cus_attr_env = { cus_attr_env & [av_group_nr] = new_attr_var},
				 					cus_heaps = { cus_heaps & th_attrs = th_attrs }, cus_attr_store = inc cus_attr_store})	
	clean_up_attribute_variable av_group_nr attr_and_cus
		= attr_and_cus
cleanUpTypeAttribute _ cui av=:(TA_Var _) cus
	= (av, cus)
cleanUpTypeAttribute _ cui type_attribute cus
	= abort ("cleanUpTypeAttribute "+++toString type_attribute)

instance clean_up Type
where
	clean_up cui (TempV tv_number) cus
		# (type, cus) = cus!cus_var_env.[tv_number]
		= cleanUpVariable type tv_number cus
	clean_up cui (TA tc types) cus
		# (types, cus) = clean_up cui types cus
		= (TA tc types, cus)
	clean_up cui (TAS tc types strictness) cus
		# (types, cus) = clean_up cui types cus
		= (TAS tc types strictness, cus)
	clean_up cui (argtype --> restype) cus
		# (argtype, cus) = clean_up cui argtype cus
		  (restype, cus) = clean_up cui restype cus
		=  (argtype --> restype, cus)
	clean_up cui t=:(TB _) cus
		=  (t, cus)
	clean_up cui (TArrow1 argtype) cus
		# (argtype, cus) = clean_up cui argtype cus
		=  (TArrow1 argtype, cus)
	clean_up cui t=:TArrow cus
		=  (t, cus)
	clean_up cui (TempCV tempvar :@: types) cus
		# (type, cus) = cus!cus_var_env.[tempvar]
		# (type, cus) = cleanUpVariable type tempvar cus
		  (types, cus) = clean_up cui types cus
		= (simplifyTypeApplication type types, cus)
	clean_up cui (TempQCV qv_number :@: types) cus=:{cus_exis_vars}
		# (type, cus) = cus!cus_var_env.[qv_number]
		  (TV tv, cus) = cleanUpVariable type qv_number {cus & cus_exis_vars = add_new_variable type qv_number cus_exis_vars}
		  (types, cus) = clean_up cui types cus
		= (CV tv :@: types, cus)
	clean_up cui (TempQCDV qv_number :@: types) cus=:{cus_exis_vars}
		# (type, cus) = cus!cus_var_env.[qv_number]
		  (TV tv, cus) = cleanUpVariable type qv_number {cus & cus_exis_vars = add_new_variable type qv_number cus_exis_vars}
		  (types, cus) = clean_up cui types cus
		= (CV tv :@: types, cus)
	clean_up cui (cv :@: types) cus
		# (types, cus) = clean_up cui types cus
		= (cv :@: types, cus)
	clean_up cui (TempQV qv_number) cus=:{cus_error,cus_exis_vars}
		# (type, cus) = cus!cus_var_env.[qv_number]
		= cleanUpVariable type qv_number {cus & cus_exis_vars = add_new_variable type qv_number cus_exis_vars}
	clean_up cui (TempQDV qv_number) cus=:{cus_error,cus_exis_vars}
		# (type, cus) = cus!cus_var_env.[qv_number]
		= cleanUpVariable type qv_number {cus & cus_exis_vars = add_new_variable type qv_number cus_exis_vars}
	clean_up cui tv=:(TV _) cus
		= (tv, cus)
	clean_up cui TAll cus
		= (TAll, cus)
	clean_up cui (TFA vars type) cus
		# (type, cus) = clean_up cui type cus
		= (TFA vars type, cus)
	clean_up cui type cus
		= abort "clean_up Type (typesupport.icl): unknown type"

add_new_variable TE qv_number cus_exis_vars
	= [(qv_number, TA_None) : cus_exis_vars]
add_new_variable type qv_number cus_exis_vars
	= cus_exis_vars

instance clean_up [a] | clean_up a
where
	clean_up cui l cus = mapSt (clean_up cui) l cus

cleanUpVariable TE tv_number cus=:{cus_heaps,cus_var_store,cus_var_env}
	# (tv_info_ptr, th_vars) = newPtr TVI_Empty cus_heaps.th_vars
	  new_var = TV {tv_ident = NewVarId cus_var_store, tv_info_ptr = tv_info_ptr}
	= (new_var, {cus & cus_var_env = { cus_var_env & [tv_number] = new_var},
					   cus_heaps = { cus_heaps & th_vars = th_vars }, cus_var_store = inc cus_var_store})
cleanUpVariable (TLifted var) tv_number cus=:{cus_error}
	= (TV var, { cus & cus_error = liftedError var cus_error})
cleanUpVariable type tv_number cus
	= (type, cus)

::	CleanUpResult :== BITVECT

cClosed				:== 0
cDefinedVar			:== 1
cUndefinedVar		:== 2
cLiftedVar			:== 4
cQVar				:== 8

cleanUpClosedVariable tvar=:(TV _) env
	= (cDefinedVar, tvar, env)
cleanUpClosedVariable (TLifted tvar) env
	= (cLiftedVar, TV tvar, env)
cleanUpClosedVariable (TExternal tvar) env
	= (cClosed, TV tvar, env)
cleanUpClosedVariable TE env
	= (cUndefinedVar, TE, env)
cleanUpClosedVariable tvar env
	= (cDefinedVar, tvar, env)

combineCleanUpResults cur1 cur2 :== cur1 bitor cur2

checkCleanUpResult cur prop :== not (cur bitand prop == 0)

class cleanUpClosed a :: !a !u:VarEnv -> (!CleanUpResult, !a, !u:VarEnv)

instance cleanUpClosed AType
where
	cleanUpClosed atype=:{at_type} env
		# (cur, at_type, env) = cleanUpClosed at_type env
		= (cur, { atype & at_attribute = TA_Multi, at_type = at_type}, env)

instance cleanUpClosed Type
where
	cleanUpClosed (TempV tv_number) env
		# (type, env) = env![tv_number]
		= cleanUpClosedVariable type env
	cleanUpClosed (TA tc types) env
		# (cur, types, env) = cleanUpClosed types env
		= (cur, TA tc types, env)
	cleanUpClosed (TAS tc types strictness) env
		# (cur, types, env) = cleanUpClosed types env
		= (cur, TAS tc types strictness, env)
	cleanUpClosed (argtype --> restype) env
		# (cur, (argtype,restype), env) = cleanUpClosed (argtype,restype) env
		= (cur, argtype --> restype, env)
	cleanUpClosed (TArrow1 argtype) env
		# (cur, argtype, env) = cleanUpClosed argtype env
		= (cur, TArrow1 argtype, env)
	cleanUpClosed (TempCV tv_number :@: types) env
		# (type, env) = env![tv_number]
		# (cur1, type, env) = cleanUpClosedVariable type env
		# (cur2, types, env) = cleanUpClosed types env
		| type=:TE
			= (combineCleanUpResults cur1 cur2, CVE :@: types, env)
			= (combineCleanUpResults cur1 cur2, simplifyTypeApplication type types, env)
	cleanUpClosed t=:(TempQCV _ :@: types) env
		= (cQVar, t, env)
	cleanUpClosed t=:(TempQCDV _ :@: types) env
		= (cQVar, t, env)
	cleanUpClosed t=:(TempQV _) env
		= (cQVar, t, env)
	cleanUpClosed t=:(TempQDV _) env
		= (cQVar, t, env)
	cleanUpClosed t env
		= (cClosed, t, env)

instance cleanUpClosed (a,b) | cleanUpClosed a & cleanUpClosed b
where
	cleanUpClosed (x,y) env
		# (cur1, x, env) = cleanUpClosed x env
		# (cur2, y, env) = cleanUpClosed y env
		= (combineCleanUpResults cur1 cur2, (x,y), env)

instance cleanUpClosed [a] | cleanUpClosed a
where
	cleanUpClosed [] env
		= (cClosed, [], env)
	cleanUpClosed [t:ts] env
		# (cur, (t,ts), env) = cleanUpClosed (t,ts) env
		= (cur, [t:ts], env)

undefinedVarInType :: !Type !VarEnv -> Bool
undefinedVarInType (TempV tv_number) env
	= env.[tv_number]=:TE
undefinedVarInType (TA tc types) env
	= undefinedVarInATypes types env
undefinedVarInType (TAS tc types strictness) env
	= undefinedVarInATypes types env
undefinedVarInType (argtype --> restype) env
	= undefinedVarInType argtype.at_type env || undefinedVarInType restype.at_type env
undefinedVarInType (TArrow1 argtype) env
	= undefinedVarInType argtype.at_type env
undefinedVarInType (TempCV tv_number :@: types) env
	= env.[tv_number]=:TE || undefinedVarInATypes types env
undefinedVarInType t env
	= False

undefinedVarInATypes :: ![AType] !VarEnv -> Bool
undefinedVarInATypes [t:ts] env
	= undefinedVarInType t.at_type env || undefinedVarInATypes ts env
undefinedVarInATypes [] env
	= False

undefinedVarInNonFunDepTypes :: ![Type] !BITVECT !VarEnv -> Bool
undefinedVarInNonFunDepTypes [t:ts] fun_dep_vars env
	| fun_dep_vars bitand 1<>0
		= undefinedVarInNonFunDepTypes ts (fun_dep_vars>>1) env
	| undefinedVarInType t env
		= True
		= undefinedVarInNonFunDepTypes ts (fun_dep_vars>>1) env
undefinedVarInNonFunDepTypes [] fun_dep_vars env
	= False

definedVarInType :: !Type !VarEnv -> Bool
definedVarInType (TempV tv_number) env
	= not env.[tv_number]=:TE
definedVarInType (TA tc types) env
	= definedVarInATypes types env
definedVarInType (TAS tc types strictness) env
	= definedVarInATypes types env
definedVarInType (argtype --> restype) env
	= definedVarInType argtype.at_type env || definedVarInType restype.at_type env
definedVarInType (TArrow1 argtype) env
	= definedVarInType argtype.at_type env
definedVarInType (TempCV tv_number :@: types) env
	= not env.[tv_number]=:TE || definedVarInATypes types env
definedVarInType t env
	= False

definedVarInATypes :: ![AType] !VarEnv -> Bool
definedVarInATypes [t:ts] env
	= definedVarInType t.at_type env || definedVarInATypes ts env
definedVarInATypes [] env
	= False

definedVarInNonFunDepTypes :: ![Type] !BITVECT !VarEnv -> Bool
definedVarInNonFunDepTypes [t:ts] fun_dep_vars env
	| fun_dep_vars bitand 1<>0
		= definedVarInNonFunDepTypes ts (fun_dep_vars>>1) env
	| definedVarInType t env
		= True
		= definedVarInNonFunDepTypes ts (fun_dep_vars>>1) env
definedVarInNonFunDepTypes [] fun_dep_vars env
	= False

defineVarsInTypeVariable :: !Type !Int !*VarEnv !Int !*TypeHeaps -> (!*VarEnv,!Int,!*TypeHeaps)
defineVarsInTypeVariable TE tv_number env next_var_n type_heaps
	# (tv_info_ptr, th_vars) = newPtr TVI_Empty type_heaps.th_vars
	  type_heaps & th_vars = th_vars
	  env & [tv_number] = TV {tv_ident = NewVarId next_var_n, tv_info_ptr = tv_info_ptr}
	  next_var_n = next_var_n+1
	= (env,next_var_n,type_heaps)
defineVarsInTypeVariable type tv_number env next_var_n type_heaps
	= (env,next_var_n,type_heaps)

defineVarsInType :: !Type !*VarEnv !Int !*TypeHeaps -> (!*VarEnv,!Int,!*TypeHeaps)
defineVarsInType (TempV tv_number) env next_var_n type_heaps
	# (type, env) = env![tv_number]
	= defineVarsInTypeVariable type tv_number env next_var_n type_heaps
defineVarsInType (TA tc types) env next_var_n type_heaps
	= defineVarsInATypes types env next_var_n type_heaps
defineVarsInType (TAS tc types strictness) env next_var_n type_heaps
	= defineVarsInATypes types env next_var_n type_heaps
defineVarsInType (argtype --> restype) env next_var_n type_heaps
	# (env,next_var_n,type_heaps) = defineVarsInType argtype.at_type env next_var_n type_heaps
	= defineVarsInType restype.at_type env next_var_n type_heaps
defineVarsInType (TArrow1 argtype) env next_var_n type_heaps
	= defineVarsInType argtype.at_type env next_var_n type_heaps
defineVarsInType (TempCV tv_number :@: types) env next_var_n type_heaps
	# (type, env) = env![tv_number]
	# (env,next_var_n,type_heaps) = defineVarsInTypeVariable type tv_number env next_var_n type_heaps
	= defineVarsInATypes types env next_var_n type_heaps
defineVarsInType t env next_var_n type_heaps
	= (env,next_var_n,type_heaps)

defineVarsInATypes :: ![AType] !*VarEnv !Int !*TypeHeaps -> (!*VarEnv,!Int,!*TypeHeaps)
defineVarsInATypes [{at_type}:ts] env next_var_n type_heaps
	# (env,next_var_n,type_heaps)
		= defineVarsInType at_type env next_var_n type_heaps
	= defineVarsInATypes ts env next_var_n type_heaps
defineVarsInATypes [] env next_var_n type_heaps
	= (env,next_var_n,type_heaps)

defineVarsInFunDepTypes :: ![Type] !BITVECT !*VarEnv !Int !*TypeHeaps -> (!*VarEnv,!Int,!*TypeHeaps)
defineVarsInFunDepTypes [t:ts] fun_dep_vars env next_var_n type_heaps
	| fun_dep_vars bitand 1==0
		= defineVarsInFunDepTypes ts (fun_dep_vars>>1) env next_var_n type_heaps
	# (env,next_var_n,type_heaps)
		= defineVarsInType t env next_var_n type_heaps
	= defineVarsInFunDepTypes ts (fun_dep_vars>>1) env next_var_n type_heaps
defineVarsInFunDepTypes [] fun_dep_vars env next_var_n type_heaps
	= (env,next_var_n,type_heaps)

errorHeading :: !String !*ErrorAdmin -> *ErrorAdmin
errorHeading error_kind err=:{ea_file,ea_loc = []}
	= { err & ea_file = ea_file <<< error_kind <<< ':', ea_ok = False }
errorHeading error_kind err=:{ea_file,ea_loc = [ep : _]}
	= { err & ea_file = ea_file <<< error_kind <<< ' ' <<< ep <<< ':', ea_ok = False }

errorHeadingWithPositionNameAndLine :: !String !Position !String !Int !*ErrorAdmin -> *ErrorAdmin
errorHeadingWithPositionNameAndLine error_kind pos ident_name line_n err=:{ea_file}
	# ea_file = (writePositionModuleName pos (ea_file <<< error_kind <<< " [")) <<< ','
	| line_n == cNotALineNumber
		= {err & ea_file = ea_file <<< ident_name <<< "]:", ea_ok = False}
		= {err & ea_file = ea_file <<< line_n <<< ',' <<< ident_name <<< "]:", ea_ok = False}

liftedContextError class_symb err
	# err = errorHeading "Overloading error" err
	= {err & ea_file = err.ea_file <<< " type variable of type of lifted argument appears in class \"" <<< class_symb <<< "\"\n"}

existentialError err
	# err = errorHeading "Type error" err
	= { err & ea_file = err.ea_file <<< "existential type variable appears in the derived type specification\n" }

liftedError type_var err
	# err = errorHeading "Type error" err
	= { err & ea_file = err.ea_file <<< "type variable " <<< type_var <<< " of type of lifted argument appears in the specified type\n" }

liftedTypeVarMissingError type_var err
	# err = errorHeading "Type error" err
	= { err & ea_file = err.ea_file <<< "type variable " <<< type_var <<< " does not occur in the type of a lifted argument\n" }

liftedAttributeVarMissingError type_var err
	# err = errorHeading "Type error" err
	= { err & ea_file = err.ea_file <<< "attribute variable " <<< type_var <<< " does not occur in the type of a lifted argument\n" }

startRuleError mess fun_ident fun_pos err
	# err = setErrorPosition fun_ident fun_pos err
	# err = errorHeading "Type error" err
	= { err & ea_file = err.ea_file <<< mess }

extendSymbolType :: !SymbolType !Int !*TypeHeaps -> (!SymbolType, !*TypeHeaps)
extendSymbolType st=:{st_arity,st_args,st_vars,st_attr_vars} nr_of_extra_args type_heaps
	| nr_of_extra_args > 0
		# (st_args, (st_vars, st_attr_vars, type_heaps))
			= newAttributedVariables nr_of_extra_args st_args (st_vars, st_attr_vars, type_heaps)
		= ({ st & st_args = st_args, st_vars = st_vars, st_attr_vars = st_attr_vars, st_arity = st_arity + nr_of_extra_args }, type_heaps)
		= (st, type_heaps)

cleanSymbolType :: !Int !*TypeHeaps -> (!SymbolType, !*TypeHeaps)
cleanSymbolType arity type_heaps
	# (st_result, clean_state) = newAttributedVariable 0 ([], [], type_heaps)
	  (st_args, (st_vars, st_attr_vars, type_heaps)) = newAttributedVariables arity [] clean_state
	= ({ st_arity = arity, st_vars = st_vars , st_args = st_args, st_args_strictness=NotStrict, st_result = st_result, st_context = [],
			st_attr_env = [], st_attr_vars = st_attr_vars }, type_heaps)

newAttributedVariables var_number attributed_variables clean_state=:(_,_,_) /* Temporary hack */
	| var_number == 0
		= (attributed_variables, clean_state)
		# (attributed_variable, clean_state) = newAttributedVariable var_number clean_state
		= newAttributedVariables (dec var_number) [ attributed_variable : attributed_variables ] clean_state

newAttributedVariable var_number (variables, attributes, type_heaps=:{th_vars,th_attrs})
	# (tv_info_ptr, th_vars) = newPtr TVI_Empty th_vars
	  new_var = { tv_ident = NewVarId var_number, tv_info_ptr = tv_info_ptr }
	  (new_attr_var, th_attrs) = NewAttrVar var_number th_attrs
	= ({ at_attribute = TA_Var new_attr_var, at_type = TV new_var},
		([ new_var : variables ], [ new_attr_var : attributes ], { type_heaps & th_vars = th_vars, th_attrs = th_attrs }))

equal_expanded_context :: !Type !Type !{#CommonDefs} !*TypeHeaps -> (!Bool,!*TypeHeaps)
equal_expanded_context type1 type2 common_defs_a type_heaps
	# (expanded1,expanded_type1,type_heaps) = tryToExpand type1 TA_Multi common_defs_a type_heaps
	# (expanded2,expanded_type2,type_heaps) = tryToExpand type2 TA_Multi common_defs_a type_heaps
	| expanded1 || expanded2
		= equal_context expanded_type1 expanded_type2 common_defs_a type_heaps
		= (False,type_heaps)

// extended version of instance == in module compare_types that expands synonym types

class equal_context t :: !t !t !{#CommonDefs} !*TypeHeaps -> (!Bool,!*TypeHeaps)

instance equal_context TypeContext where
	equal_context tc1 tc2 common_defs_a type_heaps
		| tc1.tc_class == tc2.tc_class
			= equal_context tc1.tc_types tc2.tc_types common_defs_a type_heaps;
			= (False,type_heaps)

instance equal_context AType where
	equal_context atype1 atype2 common_defs_a type_heaps
		= equal_context atype1.at_type atype2.at_type common_defs_a type_heaps

instance equal_context Type where
	equal_context type1=:(TA tc1 types1) type2=:(TA tc2 types2) common_defs_a type_heaps
		| tc1 == tc2
			= equal_context types1 types2 common_defs_a type_heaps
			= equal_expanded_context type1 type2 common_defs_a type_heaps
	equal_context type1=:(TA tc1 types1) type2=:(TAS tc2 types2 _) common_defs_a type_heaps
		| tc1 == tc2
			= equal_context types1 types2 common_defs_a type_heaps
			= equal_expanded_context type1 type2 common_defs_a type_heaps
	equal_context (TA tc1 types1) _ common_defs_a type_heaps
		= (False,type_heaps)
	equal_context type1=:(TAS tc1 types1 _) type2=:(TA tc2 types2) common_defs_a type_heaps
		| tc1 == tc2
			= equal_context types1 types2 common_defs_a type_heaps
			= equal_expanded_context type1 type2 common_defs_a type_heaps
	equal_context type1=:(TAS tc1 types1 _) type2=:(TAS tc2 types2 _) common_defs_a type_heaps
		| tc1 == tc2
			= equal_context types1 types2 common_defs_a type_heaps
			= equal_expanded_context type1 type2 common_defs_a type_heaps
	equal_context (TAS tc1 types1 _) _ common_defs_a type_heaps
		= (False,type_heaps)
	equal_context t1 t2 common_defs_a type_heaps
		| equal_constructor t1 t2
			= equal_constructor_args t1 t2 common_defs_a type_heaps
			= (False,type_heaps) 
	where
		equal_constructor_args (TV varid1) (TV varid2) common_defs_a type_heaps
			= (varid1 == varid2,type_heaps)
		equal_constructor_args (TempV varid1) (TempV varid2) common_defs_a type_heaps
			= (varid1 == varid2,type_heaps)
		equal_constructor_args (arg_type1-->restype1) (arg_type2-->restype2) common_defs_a type_heaps
			# (equal,type_heaps) = equal_context arg_type1 arg_type2 common_defs_a type_heaps
			| equal
				= equal_context restype1 restype2 common_defs_a type_heaps
				= (False,type_heaps)
		equal_constructor_args (TB tb1) (TB tb2) common_defs_a type_heaps
			= (tb1 == tb2,type_heaps)
		equal_constructor_args (type1 :@: types1) (type2 :@: types2) common_defs_a type_heaps
			| type1==type2
				= equal_context types1 types2 common_defs_a type_heaps
				= (False,type_heaps)
		equal_constructor_args (GTV varid1) (GTV varid2) common_defs_a type_heaps
			= (varid1==varid2,type_heaps)
		equal_constructor_args (TempQV varid1) (TempQV varid2) common_defs_a type_heaps
			= (varid1==varid2,type_heaps)
		equal_constructor_args (TempQDV varid1) (TempQDV varid2) common_defs_a type_heaps
			= (varid1==varid2,type_heaps)
		equal_constructor_args (TLifted varid1) (TLifted varid2) common_defs_a type_heaps
			= (varid1==varid2,type_heaps)
		equal_constructor_args type1 type2 common_defs_a type_heaps
			= (True,type_heaps)

instance equal_context [t] | equal_context t where
	equal_context [e1:l1] [e2:l2] common_defs_a type_heaps
		# (equal,type_heaps) = equal_context e1 e2 common_defs_a type_heaps
		| equal
			= equal_context l1 l2 common_defs_a type_heaps
			= (False,type_heaps)
	equal_context [] [] common_defs_a type_heaps
		= (True,type_heaps)
	equal_context _ _ common_defs_a type_heaps
		= (False,type_heaps)

cSpecifiedType	:== True
cDerivedType	:== False

:: ErrorContexts = AmbiguousContext !TypeContext !ErrorContexts | MissingContext !TypeContext !ErrorContexts | NoErrorContexts

cleanUpSymbolType :: !Bool !TempSymbolType ![TypeContext] ![ExprInfoPtr] !{!CoercionTree} !AttributePartition !{#CommonDefs}
																   !*VarEnv !*AttributeEnv !*TypeHeaps !*VarHeap !*ExpressionHeap !*ErrorAdmin
				  -> (!SymbolType,![AttrInequality],!ErrorContexts,!*VarEnv,!*AttributeEnv,!*TypeHeaps,!*VarHeap,!*ExpressionHeap,!*ErrorAdmin)
cleanUpSymbolType spec_type {tst_arity,tst_args,tst_result,tst_context,tst_lifted} derived_context case_and_let_exprs
		coercions attr_part defs var_env attr_var_env heaps var_heap expr_heap error
	#! nr_of_temp_vars = size var_env
	#! max_attr_nr = size attr_var_env
	# cus = { cus_var_env = var_env, cus_attr_env = attr_var_env, cus_appears_in_lifted_part = bitvectCreate max_attr_nr,
				cus_heaps = heaps, cus_var_store = 0, cus_attr_store = 0, cus_error = error, cus_exis_vars = [] }
	  cui = { cui_coercions = coercions, cui_attr_part = attr_part, cui_is_lifted_part = True }
	  (lifted_args, cus=:{cus_var_env}) = clean_up cui (take tst_lifted tst_args) cus
	  cui & cui_is_lifted_part = False
	  (cus_var_env,cus_var_store,cus_heaps)
		= if (spec_type && not lifted_args=:[])
			(mark_dependent_type_vars_in_fun_dep_type_contexts derived_context defs True cus_var_env cus.cus_var_store cus.cus_heaps)
			(cus_var_env,cus.cus_var_store,cus.cus_heaps)
	  (lifted_vars, cus_var_env) = determine_lifted_type_vars nr_of_temp_vars cus_var_env
	  cus & cus_var_env=cus_var_env,cus_var_store=cus_var_store,cus_heaps=cus_heaps
	  (st_args, cus) = clean_up_arg_types cui tst_lifted tst_args cus
	  (st_result, cus) = clean_up_result_type cui tst_result cus
	  (cus_var_env,cus_var_store,cus_heaps)
		= if (not spec_type)
			(mark_dependent_type_vars_in_fun_dep_type_contexts derived_context defs False cus.cus_var_env cus.cus_var_store cus.cus_heaps)
			(cus.cus_var_env,cus.cus_var_store,cus.cus_heaps)
	  (st_context, ambiguous_or_missing_contexts, cus_var_env, cus_heaps, var_heap, cus_error)
		= clean_up_type_contexts spec_type tst_context derived_context [!!] defs cus_var_env cus_heaps var_heap cus.cus_error
	  (st_vars, cus_var_env) = determine_type_vars nr_of_temp_vars lifted_vars cus_var_env
	  (cus_attr_env, attr_vars, lifted_attr_vars, st_attr_env, lifted_attr_env, cus_error)
			= build_attribute_environment cus.cus_appears_in_lifted_part max_attr_nr coercions cus.cus_attr_env cus_error
	  st_attr_vars = lifted_attr_vars ++ attr_vars
	  (expr_heap, {cuets_var_env=cus_var_env,cuets_heaps=cus_heaps})
			= clean_up_expression_types case_and_let_exprs expr_heap
				  {cuets_var_env=cus_var_env,cuets_heaps=cus_heaps,cuets_var_store=cus_var_store}
	  st = {st_arity = tst_arity, st_vars = st_vars , st_args = lifted_args ++ st_args, st_args_strictness=NotStrict, st_result = st_result, st_context = st_context,
			st_attr_env = st_attr_env, st_attr_vars = st_attr_vars }
	  cus_var_env = {cus_var_env & [i] = TE \\ i <- [0..nr_of_temp_vars-1]}
	  cus_attr_env = {cus_attr_env & [i] = TA_None \\ i <- [0..max_attr_nr-1]}
	= (st,lifted_attr_env,ambiguous_or_missing_contexts,cus_var_env,cus_attr_env,cus_heaps,var_heap,expr_heap,cus_error)
where
	determine_lifted_type_vars to_index var_env
		= iFoldSt determine_lifted_type_var 0 to_index ([], var_env)
	where
		determine_lifted_type_var var_index (all_vars, var_env)
			# (type, var_env) = var_env![var_index]
			= case type of
				TV var
					-> ([var : all_vars], {var_env & [var_index] = TLifted var})
				_
					-> (all_vars, var_env)

check_type_of_start_rule :: !SymbolType !{#CommonDefs} !Bool !Ident !Position !*ErrorAdmin -> (!Bool,!*ErrorAdmin)
check_type_of_start_rule {st_context,st_arity,st_args} common_defs type_error fun_ident fun_pos cus_error
	| st_context=:[]
		| st_arity > 0
				= check_start_function_argument_types st_args [] common_defs type_error fun_ident fun_pos cus_error
			= (type_error,cus_error)
		= (True,startRuleError "Start function cannot be overloaded\n" fun_ident fun_pos cus_error)
where
	check_start_function_argument_types [{at_type}] previous_noncreatable_types common_defs type_error fun_ident fun_pos error
		| at_type=:(TB BT_World)
			= (type_error,error)
			= (True,startRuleError "last argument of Start function should have type World\n" fun_ident fun_pos error)
	check_start_function_argument_types [{at_type}:type_args] previous_noncreatable_types common_defs type_error fun_ident fun_pos error
		# (previous_noncreatable_types,type_error,error)
			= check_start_function_argument_type at_type previous_noncreatable_types common_defs type_error fun_ident fun_pos error
		= check_start_function_argument_types type_args previous_noncreatable_types common_defs type_error fun_ident fun_pos error

	check_start_function_argument_type (TA {type_index=type_index,type_ident} type_args) previous_noncreatable_types common_defs type_error fun_ident fun_pos error
		#! type_rhs = common_defs.[type_index.glob_module].com_type_defs.[type_index.glob_object].td_rhs
		= case type_rhs of
			RecordType {rt_fields}
				| size rt_fields==1 && rt_fields.[0].fs_ident.id_name=="_"
					| type_args=:[]
						| isMember type_index previous_noncreatable_types
							# error = startRuleError ("noncreatable type "+++toString type_ident+++" occurs more than once in Start function argument types\n") fun_ident fun_pos error
							-> (previous_noncreatable_types,True,error)
							-> ([type_index:previous_noncreatable_types],type_error,error)
						-> check_start_function_argument_type (last type_args).at_type previous_noncreatable_types common_defs type_error fun_ident fun_pos error
			_
				-> (previous_noncreatable_types,True,startRuleError "Start function argument type should be noncreatable\n" fun_ident fun_pos error)
	check_start_function_argument_type _ previous_noncreatable_types common_defs type_error fun_ident fun_pos error
		= (previous_noncreatable_types,True,startRuleError "Start function argument type should be noncreatable\n" fun_ident fun_pos error)

cleanUpLocalSymbolType :: !TempSymbolType ![!P TypeVar Type!] ![!P AttributeVar TypeAttribute!] ![TypeContext] ![ExprInfoPtr] !{!CoercionTree} !AttributePartition !{#CommonDefs}
							!*VarEnv !*AttributeEnv !*TypeHeaps !*VarHeap !*ExpressionHeap !*ErrorAdmin
						-> (!SymbolType,![AttrInequality],!ErrorContexts,![!P TypeVarInfoPtr TypeVarInfoPtr!],![!P AttrVarInfoPtr AttrVarInfoPtr!],
							!*VarEnv,!*AttributeEnv,!*TypeHeaps,!*VarHeap,!*ExpressionHeap,!*ErrorAdmin)
cleanUpLocalSymbolType {tst_arity,tst_args,tst_result,tst_context,tst_lifted} external_type_vars external_attr_vars derived_context
		case_and_let_exprs coercions attr_part common_defs var_env attr_var_env heaps var_heap expr_heap error
	#! nr_of_temp_vars = size var_env
	#! max_attr_nr = size attr_var_env
	# cus = { cus_var_env = var_env, cus_attr_env = attr_var_env, cus_appears_in_lifted_part = bitvectCreate max_attr_nr,
				cus_heaps = heaps, cus_var_store = 0, cus_attr_store = 0, cus_error = error, cus_exis_vars = [] }
	  cui = { cui_coercions = coercions, cui_attr_part = attr_part, cui_is_lifted_part = True }

	  (lifted_args, cus=:{cus_var_env,cus_error,cus_appears_in_lifted_part}) = clean_up cui (take tst_lifted tst_args) cus
	  cui & cui_is_lifted_part = False
	  (cus_var_env,cus_var_store,cus_heaps)
		= if (not lifted_args=:[])
			(mark_dependent_type_vars_in_fun_dep_type_contexts derived_context common_defs False cus_var_env cus.cus_var_store cus.cus_heaps)
			(cus_var_env,cus.cus_var_store,cus.cus_heaps)
	  (new_and_old_external_type_vars,cus_var_env,cus_error) = prevent_lift_of_external_type_vars external_type_vars cus_var_env cus_error
	  (lifted_vars, cus_var_env) = determine_type_vars_and_restore_lifted_vars nr_of_temp_vars cus_var_env
	  external_vars = bitvectCreate max_attr_nr
	  (new_and_old_external_attr_vars,cus_appears_in_lifted_part,external_vars,cus_attr_env,cus_error)
		= remove_external_attr_vars cui external_attr_vars cus_appears_in_lifted_part external_vars cus.cus_attr_env cus_error
	  cus & cus_appears_in_lifted_part=cus_appears_in_lifted_part, cus_var_env=cus_var_env, cus_attr_env=cus_attr_env, cus_error=cus_error,
			cus_var_store=cus_var_store, cus_heaps=cus_heaps
	  (st_args, cus) = clean_up_arg_types cui tst_lifted tst_args cus
	  (st_result, cus) = clean_up_result_type cui tst_result cus
	  (st_context, ambiguous_or_missing_contexts, cus_var_env, type_heaps, var_heap, cus_error)
		= clean_up_type_contexts cSpecifiedType tst_context derived_context external_type_vars common_defs cus.cus_var_env cus.cus_heaps var_heap cus.cus_error
	  (st_vars, cus_var_env) = determine_type_vars nr_of_temp_vars lifted_vars cus_var_env
	  (cus_attr_env, attr_vars, lifted_attr_vars, st_attr_env, lifted_attr_env, cus_error)
		= build_attribute_environment_with_external_vars cus.cus_appears_in_lifted_part external_vars max_attr_nr coercions cus.cus_attr_env cus_error
	  st_attr_vars = lifted_attr_vars ++ attr_vars
	  (expr_heap, {cuets_var_env=cus_var_env,cuets_heaps=cus_heaps})
			= clean_up_expression_types case_and_let_exprs expr_heap
					 {cuets_var_env=cus_var_env,cuets_heaps=type_heaps,cuets_var_store=cus.cus_var_store}
	  st = {st_arity = tst_arity, st_vars = st_vars , st_args = lifted_args ++ st_args, st_args_strictness=NotStrict, st_result = st_result, st_context = st_context,
			st_attr_env = st_attr_env, st_attr_vars = st_attr_vars }
	  cus_var_env = {cus_var_env & [i] = TE \\ i <- [0..nr_of_temp_vars-1]}
	  cus_attr_env = {cus_attr_env & [i] = TA_None \\ i <- [0..max_attr_nr-1]}
	= (st,lifted_attr_env,ambiguous_or_missing_contexts,new_and_old_external_type_vars,new_and_old_external_attr_vars,cus_var_env,cus_attr_env,cus_heaps,var_heap,expr_heap,cus_error)
where
	prevent_lift_of_external_type_vars [!P {tv_ident,tv_info_ptr} (TempV var_index):external_type_vars!] var_env error
		# (type, var_env) = var_env![var_index]
		= case type of
			TV var
				# var_env & [var_index] = TLifted var // restored in determine_type_vars_and_restore_lifted_vars
				# (new_and_old_external_type_vars,cus_var_env,cus_error) = prevent_lift_of_external_type_vars external_type_vars var_env error
				-> ([!P var.tv_info_ptr tv_info_ptr:new_and_old_external_type_vars!],cus_var_env,cus_error)
			_
				# error = liftedTypeVarMissingError tv_ident error
				-> prevent_lift_of_external_type_vars external_type_vars var_env error
	prevent_lift_of_external_type_vars [!P {tv_ident} _:external_type_vars!] var_env error
		# error = liftedTypeVarMissingError tv_ident error
		= prevent_lift_of_external_type_vars external_type_vars var_env error
	prevent_lift_of_external_type_vars [!!] var_env error
		= ([!!],var_env,error)

	determine_type_vars_and_restore_lifted_vars to_index var_env
		= iFoldSt determine_type_var 0 to_index ([], var_env)
	where
		determine_type_var var_index (all_vars, var_env)
			# (type, var_env) = var_env![var_index]
			= case type of
				TV var
					-> ([var : all_vars], {var_env & [var_index] = TLifted var})
				TLifted var
					-> (all_vars, {var_env & [var_index] = TV var})
				_
					-> (all_vars, var_env)

	remove_external_attr_vars cui [!P {av_ident,av_info_ptr} (TA_TempVar av_number):external_attr_vars!] appears_in_lifted_part external_vars attr_env error
		# av_group_nr = cui.cui_attr_part.[av_number]
		| bitvectSelect av_group_nr appears_in_lifted_part
			# appears_in_lifted_part = bitvectReset av_group_nr appears_in_lifted_part
			# external_vars = bitvectSet av_group_nr external_vars
			# (type_attribute,attr_env) = attr_env![av_group_nr]
			= case type_attribute of
				TA_Var av
					# (new_and_old_external_attr_vars,appears_in_lifted_part,external_vars,attr_env,error)
						= remove_external_attr_vars cui external_attr_vars appears_in_lifted_part external_vars attr_env error
					-> ([!P av.av_info_ptr av_info_ptr:new_and_old_external_attr_vars!],appears_in_lifted_part,external_vars,attr_env,error)
			# error = liftedAttributeVarMissingError av_ident error
			= remove_external_attr_vars cui external_attr_vars appears_in_lifted_part external_vars attr_env error
	remove_external_attr_vars cui [!!] appears_in_lifted_part external_vars attr_env error
		= ([!!],appears_in_lifted_part,external_vars,attr_env,error)

determine_type_vars to_index all_vars var_env
	= iFoldSt determine_type_var 0 to_index (all_vars, var_env)
where
	determine_type_var var_index (all_vars, var_env)
		# (type, var_env) = var_env![var_index]
		= case type of
			TV var
				-> ([var : all_vars], var_env)
			_
				-> (all_vars, var_env)


clean_up_arg_types cui tst_lifted tst_args cus
	# (st_args, (_, cus)) = mapSt (clean_up_arg_type cui) (drop tst_lifted tst_args) ([], cus)
	= (st_args,cus)
where
	clean_up_arg_type cui at=:{at_type = TFA avars type, at_attribute} (all_exi_vars, cus)
		# (at_attribute, cus) 	= cleanUpTypeAttribute False cui at_attribute cus
		  (type, cus)			= clean_up cui type cus
		| isEmpty cus.cus_exis_vars
			= ({ at & at_type = TFA avars type, at_attribute = at_attribute}, (all_exi_vars, cus))
			= ({ at & at_type = TFA avars type, at_attribute = at_attribute},
					(all_exi_vars, {cus & cus_error = existentialError cus.cus_error, cus_exis_vars = []}))
	clean_up_arg_type cui at=:{at_type = TFAC avars type contexts, at_attribute} (all_exi_vars, cus)
		# (at_attribute, cus) 	= cleanUpTypeAttribute False cui at_attribute cus
		  (type, cus)			= clean_up cui type cus
		| isEmpty cus.cus_exis_vars
			= ({ at & at_type = TFAC avars type contexts, at_attribute = at_attribute}, (all_exi_vars, cus))
			= ({ at & at_type = TFAC avars type contexts, at_attribute = at_attribute},
					(all_exi_vars, {cus & cus_error = existentialError cus.cus_error, cus_exis_vars = []}))
	clean_up_arg_type cui at (all_exi_vars, cus)
		# (at, cus) = clean_up cui at cus
		  (cus_exis_vars, cus) = cus!cus_exis_vars
		| isEmpty cus_exis_vars
			= (at, (all_exi_vars, cus))
			# (new_exi_vars, all_exi_vars, cus) = foldSt check_existential_var cus_exis_vars ([], all_exi_vars, cus)
			= ({ at & at_type = TFA new_exi_vars at.at_type }, (all_exi_vars, {cus & cus_exis_vars = []}))
	where
		check_existential_var (var_number,var_attr) (exi_vars, all_vars, cus)
			# (type, cus) = cus!cus_var_env.[var_number]
			| isMember var_number all_vars
				= case type of
					TE
						-> (exi_vars, all_vars, cus)
					TV var
						-> ([{atv_attribute = var_attr, atv_variable = var } : exi_vars ], all_vars,
							{cus & cus_var_env = {cus.cus_var_env & [var_number] = TE }, cus_error = existentialError cus.cus_error })
				# all_vars = [var_number : all_vars]
				= case type of
					TV var
						-> ([{atv_attribute=var_attr, atv_variable=var} : exi_vars], all_vars, {cus & cus_var_env.[var_number] = TE})
					TLifted var
						# cus = {cus & cus_error = liftedError var cus.cus_error, cus_var_env.[var_number] = TE}
						-> ([{atv_attribute=var_attr, atv_variable=var} : exi_vars], all_vars, cus)

clean_up_result_type cui at cus
	# (at, cus=:{cus_exis_vars}) = clean_up cui at cus
	| isEmpty cus_exis_vars
		= (at, cus)
		= (at, { cus & cus_error = existentialError cus.cus_error })

mark_dependent_type_vars_in_fun_dep_type_contexts :: ![TypeContext] !{#CommonDefs} !Bool !*{!Type} !Int !*TypeHeaps -> (!*{!Type},!Int,!*TypeHeaps)
mark_dependent_type_vars_in_fun_dep_type_contexts contexts defs require_defined_var env next_var_n type_heaps
	#! previous_next_var_n = next_var_n
	# (contexts, env, next_var_n, type_heaps)
		= mark_dependent_type_vars_in_fun_dep_type_contexts_pass contexts [] defs require_defined_var env next_var_n type_heaps
	| next_var_n==previous_next_var_n || contexts=:[]
		= (env, next_var_n, type_heaps)
		= mark_dependent_type_vars_in_fun_dep_type_contexts contexts defs require_defined_var env next_var_n type_heaps
where
	mark_dependent_type_vars_in_fun_dep_type_contexts_pass [tc=:{tc_class=TCClass {glob_object={ds_index,ds_ident},glob_module},tc_types}:tcs] contexts defs require_defined_var env next_var_n type_heaps
		# class_fun_dep_vars = defs.[glob_module].com_class_defs.[ds_index].class_fun_dep_vars
		| class_fun_dep_vars<>0
			| undefinedVarInNonFunDepTypes tc_types class_fun_dep_vars env
				= mark_dependent_type_vars_in_fun_dep_type_contexts_pass tcs [tc:contexts] defs require_defined_var env next_var_n type_heaps
			| not require_defined_var || definedVarInNonFunDepTypes tc_types class_fun_dep_vars env
				# (env,next_var_n,type_heaps) = defineVarsInFunDepTypes tc_types class_fun_dep_vars env next_var_n type_heaps
				= mark_dependent_type_vars_in_fun_dep_type_contexts_pass tcs contexts defs require_defined_var env next_var_n type_heaps
				= mark_dependent_type_vars_in_fun_dep_type_contexts_pass tcs contexts defs require_defined_var env next_var_n type_heaps
			= mark_dependent_type_vars_in_fun_dep_type_contexts_pass tcs contexts defs require_defined_var env next_var_n type_heaps
	mark_dependent_type_vars_in_fun_dep_type_contexts_pass [_:tcs] contexts defs require_defined_var env next_var_n type_heaps
		= mark_dependent_type_vars_in_fun_dep_type_contexts_pass tcs contexts defs require_defined_var env next_var_n type_heaps
	mark_dependent_type_vars_in_fun_dep_type_contexts_pass [] contexts defs require_defined_var env next_var_n type_heaps
		= (contexts,env,next_var_n,type_heaps)

clean_up_type_contexts spec_type spec_context derived_context external_type_vars common_defs env type_heaps var_heap error
	| spec_type
		# (type_heaps,var_heap) = foldSt (mark_specified_context derived_context) spec_context (type_heaps,var_heap)
		  (derived_context,var_heap) = remove_specified_contexts derived_context var_heap
		  (type_heaps,var_heap) = mark_TAll_contexts derived_context spec_context type_heaps var_heap
		  var_heap = if (derived_context=:[]) var_heap (mark_specified_polymorphic_contexts spec_context derived_context var_heap)
		  env = mark_external_type_vars external_type_vars env
		  (rev_contexts, ambiguous_or_missing_contexts, env, var_heap, error)
			= foldSt clean_up_lifted_type_context derived_context ([], NoErrorContexts, env, var_heap, error)
		  env = unmark_external_type_vars external_type_vars env
		  (rev_contexts, ambiguous_or_missing_contexts, env, var_heap, error)
			= foldSt clean_up_type_context spec_context (rev_contexts, ambiguous_or_missing_contexts, env, var_heap, error)
		= (reverse rev_contexts, ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
		# (rev_contexts, ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
			= foldSt clean_up_type_context2 derived_context ([], NoErrorContexts, env, type_heaps, var_heap, error)
		= (reverse rev_contexts, ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
where
	mark_specified_context :: ![TypeContext] !TypeContext !*(*TypeHeaps,!*VarHeap) -> (!*TypeHeaps,!*VarHeap)
	mark_specified_context [] spec_tc (type_heaps,var_heap)
		= (type_heaps,var_heap)
	mark_specified_context [tc=:{tc_var} : tcs] spec_tc (type_heaps,var_heap)
		# (contexts_equal,type_heaps) = equal_context spec_tc tc common_defs type_heaps
		| contexts_equal
			# (tc_var_info,var_heap) = readPtr tc_var var_heap
			# var_heap = if (tc_var_info=:VI_Empty) (writePtr tc_var VI_ContextSpecified var_heap) var_heap
			| spec_tc.tc_var == tc_var
				= (type_heaps,var_heap)
				# var_heap = writePtr spec_tc.tc_var (VI_ForwardClassVar tc_var) var_heap
				= (type_heaps,var_heap)
			= mark_specified_context tcs spec_tc (type_heaps,var_heap)

	mark_specified_contexts2 derived_tc=:{tc_var} spec_context (type_heaps,var_heap)
		# (context_found,equal_spec_context,type_heaps) = find_equal_context derived_tc spec_context type_heaps
		| not context_found
			= (type_heaps,var_heap)
		# (tc_var_info,var_heap) = readPtr tc_var var_heap
		# var_heap = if (tc_var_info=:VI_Empty) (writePtr tc_var VI_ContextSpecified var_heap) var_heap
		| equal_spec_context.tc_var == tc_var
			= (type_heaps,var_heap)
		# (equal_spec_context_var_info,var_heap) = readPtr equal_spec_context.tc_var var_heap
		= case equal_spec_context_var_info of
			VI_ForwardClassVar _
				# var_heap = writePtr equal_spec_context.tc_var (VI_ForwardClassVars tc_var equal_spec_context_var_info) var_heap
				-> (type_heaps,var_heap)
			VI_ForwardClassVars _ _
				# var_heap = writePtr equal_spec_context.tc_var (VI_ForwardClassVars tc_var equal_spec_context_var_info) var_heap
				-> (type_heaps,var_heap)
			_
				# var_heap = writePtr equal_spec_context.tc_var (VI_ForwardClassVar tc_var) var_heap
				-> (type_heaps,var_heap)

	find_equal_context :: !TypeContext ![TypeContext] !*TypeHeaps -> (!Bool,!TypeContext,!*TypeHeaps)
	find_equal_context tc [spec_tc:spec_tcs] type_heaps
		# (contexts_equal,type_heaps) = equal_context spec_tc tc common_defs type_heaps
		| contexts_equal
			= (True,spec_tc,type_heaps)
			= find_equal_context tc spec_tcs type_heaps
	find_equal_context tc [] type_heaps
		= (False,tc,type_heaps)

	remove_specified_contexts [derived_tc=:{tc_var}:derived_tcs] var_heap
		| (sreadPtr tc_var var_heap)=:VI_ContextSpecified
			# var_heap = writePtr tc_var VI_Empty var_heap
			= remove_specified_contexts derived_tcs var_heap
			# (derived_tcs,var_heap) = remove_specified_contexts derived_tcs var_heap
			= ([derived_tc:derived_tcs],var_heap)
	remove_specified_contexts [] var_heap
		= ([],var_heap)

	mark_TAll_contexts [derived_tc=:{tc_class=TCClass {glob_module,glob_object={ds_index}},tc_types,tc_var}:derived_tcs] spec_context type_heaps var_heap
		# class_args = common_defs.[glob_module].com_class_defs.[ds_index].class_args
		# (maybe_added_TAll,tc_types2) = replace_TempCV_with_TempQV_by_TAll class_args tc_types
		| maybe_added_TAll
			# derived_tc2 = {derived_tc & tc_types = tc_types2}
			# (type_heaps,var_heap) = mark_specified_contexts2 derived_tc2 spec_context (type_heaps,var_heap)
			= mark_TAll_contexts derived_tcs spec_context type_heaps var_heap
			= mark_TAll_contexts derived_tcs spec_context type_heaps var_heap
	mark_TAll_contexts [derived_tc=:{tc_class=TCGeneric {gtc_class={glob_module,glob_object={ds_index}}},tc_types,tc_var}:derived_tcs] spec_context type_heaps var_heap
		# class_args = common_defs.[glob_module].com_class_defs.[ds_index].class_args
		# (maybe_added_TAll,tc_types2) = replace_TempCV_with_TempQV_by_TAll class_args tc_types
		| maybe_added_TAll
			# derived_tc2 = {derived_tc & tc_types = tc_types2}
			# (type_heaps,var_heap) = mark_specified_contexts2 derived_tc2 spec_context (type_heaps,var_heap)
			= mark_TAll_contexts derived_tcs spec_context type_heaps var_heap
			= mark_TAll_contexts derived_tcs spec_context type_heaps var_heap
	mark_TAll_contexts [_:derived_tcs] spec_context type_heaps var_heap
		= mark_TAll_contexts derived_tcs spec_context type_heaps var_heap
	mark_TAll_contexts [] spec_context type_heaps var_heap
		= (type_heaps,var_heap)

	replace_TempCV_with_TempQV_by_TAll (ClassArgPattern _ class_arg_vars class_args) [TempCV type_var_n:@:cv_arg_types:tc_types]
		| length class_arg_vars==length cv_arg_types
			# cv_type = TempCV type_var_n :@: replace_TempQV_by_TAll cv_arg_types
			# (_,tc_types) = replace_TempCV_with_TempQV_by_TAll class_args tc_types
			= (True,[cv_type:tc_types])
	replace_TempCV_with_TempQV_by_TAll (ClassArgPatternSameTypeVar class_arg_vars class_args) [TempCV type_var_n:@:cv_arg_types:tc_types]
		| length class_arg_vars==length cv_arg_types
			# cv_type = TempCV type_var_n :@: replace_TempQV_by_TAll cv_arg_types
			# (_,tc_types) = replace_TempCV_with_TempQV_by_TAll class_args tc_types
			= (True,[cv_type:tc_types])
	replace_TempCV_with_TempQV_by_TAll _ tc_types
		= (False,tc_types)

	mark_specified_polymorphic_contexts [spec_context=:{tc_class=TCGeneric {gtc_class={glob_module,glob_object={ds_index}}},tc_types}:spec_contexts] derived_contexts var_heap
		| is_polymorpic_context tc_types
			# var_heap = mark_polymorphic_context derived_contexts spec_context var_heap
			= mark_specified_polymorphic_contexts spec_contexts derived_contexts var_heap
			= mark_specified_polymorphic_contexts spec_contexts derived_contexts var_heap
	where
		is_polymorpic_context [TempCV _:@:cv_arg_types:types] = is_polymorphic_cv_args cv_arg_types && is_polymorpic_context types
		is_polymorpic_context types = types=:[]

		is_polymorphic_cv_args [{at_type=TAll}:types] = is_polymorphic_cv_args types
		is_polymorphic_cv_args types = types=:[]

		mark_polymorphic_context [tc=:{tc_class,tc_var,tc_types} : tcs] spec_tc var_heap
			| tc_class==spec_tc.tc_class && equal_polymorpic_context tc_types spec_tc.tc_types
				# (tc_var_info,var_heap) = readPtr tc_var var_heap
				# var_heap = if (tc_var_info=:VI_Empty) (writePtr tc_var VI_ContextSpecified var_heap) var_heap
				| spec_tc.tc_var == tc_var
					= mark_polymorphic_context tcs spec_tc var_heap
					# (spec_tc_var_info,var_heap) = readPtr spec_tc.tc_var var_heap
					# spec_tc_var_info
						= case spec_tc_var_info of
							VI_ForwardClassVar _
								-> VI_ForwardClassVars tc_var spec_tc_var_info
							VI_ForwardClassVars _ _
								-> VI_ForwardClassVars tc_var spec_tc_var_info
							_
								-> VI_ForwardClassVar tc_var
					# var_heap = writePtr spec_tc.tc_var spec_tc_var_info var_heap
					= mark_polymorphic_context tcs spec_tc var_heap
				= mark_polymorphic_context tcs spec_tc var_heap
		where
			equal_polymorpic_context [TempCV type_var_n:@:cv_arg_types:tc_types] [TempCV spec_type_var_n:@:spec_cv_arg_types:spec_tc_types]
				= type_var_n==spec_type_var_n && length cv_arg_types==length spec_cv_arg_types && equal_polymorpic_context tc_types spec_tc_types
			equal_polymorpic_context [] []
				= True
			equal_polymorpic_context _ _
				= False
		mark_polymorphic_context [] spec_tc var_heap
			= var_heap
	mark_specified_polymorphic_contexts [_:spec_contexts] derived_contexts var_heap
		= mark_specified_polymorphic_contexts spec_contexts derived_contexts var_heap
	mark_specified_polymorphic_contexts [] derived_contexts var_heap
		= var_heap

	mark_external_type_vars [!P {tv_ident,tv_info_ptr} (TempV var_index):external_type_vars!] var_env
		# (type, var_env) = var_env![var_index]
		= case type of
			TV var
				# var_env & [var_index] = TExternal var
				-> mark_external_type_vars external_type_vars var_env
			_
				-> mark_external_type_vars external_type_vars var_env
	mark_external_type_vars [!_:external_type_vars!] var_env
		= mark_external_type_vars external_type_vars var_env
	mark_external_type_vars [!!] var_env
		= var_env

	clean_up_lifted_type_context tc=:{tc_var,tc_types} (collected_contexts,ambiguous_or_missing_contexts,env,var_heap,error)
		| (sreadPtr tc_var var_heap)=:VI_ContextSpecified
			# var_heap = writePtr tc_var VI_Empty var_heap
			= (collected_contexts,ambiguous_or_missing_contexts,env,var_heap,error)
		# (cur, tc_types, env) = cleanUpClosed tc.tc_types env
		| checkCleanUpResult cur cLiftedVar
			| checkCleanUpResult cur cDefinedVar
				# error = liftedContextError (toString tc.tc_class) error
				= (collected_contexts,ambiguous_or_missing_contexts,env,var_heap,error)
			| checkCleanUpResult cur cUndefinedVar
				# ambiguous_or_missing_contexts = AmbiguousContext {tc & tc_types=tc_types} ambiguous_or_missing_contexts
				= (collected_contexts,ambiguous_or_missing_contexts,env,var_heap,error)
				# collected_contexts = [{tc & tc_types = tc_types}:collected_contexts]
				= (collected_contexts,ambiguous_or_missing_contexts,env,var_heap,error)
		| checkCleanUpResult cur cUndefinedVar
			# ambiguous_or_missing_contexts = AmbiguousContext {tc & tc_types=tc_types} ambiguous_or_missing_contexts
			= (collected_contexts,ambiguous_or_missing_contexts,env,var_heap,error)
			# ambiguous_or_missing_contexts = MissingContext {tc & tc_types=tc_types} ambiguous_or_missing_contexts
			= (collected_contexts,ambiguous_or_missing_contexts,env,var_heap,error)

	unmark_external_type_vars [!P _ (TempV var_index):external_type_vars!] var_env
		# (type, var_env) = var_env![var_index]
		= case type of
			TExternal var
				# var_env & [var_index] = TV var
				-> unmark_external_type_vars external_type_vars var_env
			_
				-> unmark_external_type_vars external_type_vars var_env
	unmark_external_type_vars [!_:external_type_vars!] var_env
		= unmark_external_type_vars external_type_vars var_env
	unmark_external_type_vars [!!] var_env
		= var_env

	clean_up_type_context tc=:{tc_types,tc_class,tc_var} (collected_contexts, ambiguous_or_missing_contexts, env, var_heap, error)
		| (sreadPtr tc_var var_heap)=:VI_EmptyConstructorClassVar
			= (collected_contexts, ambiguous_or_missing_contexts, env, var_heap, error)
		# (cur, tc_types, env) = cleanUpClosed tc_types env
		| checkCleanUpResult cur cUndefinedVar
			# ambiguous_or_missing_contexts = AmbiguousContext {tc & tc_types = tc_types} ambiguous_or_missing_contexts
			= (collected_contexts, ambiguous_or_missing_contexts, env, var_heap, error)
		| checkCleanUpResult cur cLiftedVar
			= ([{tc & tc_types = tc_types} : collected_contexts], ambiguous_or_missing_contexts, env, var_heap, liftedContextError (toString tc_class) error)
		| checkCleanUpResult cur cQVar
			= case tc_class of
				TCClass {glob_module,glob_object={ds_index}}
					# class_args = common_defs.[glob_module].com_class_defs.[ds_index].class_args
					# (maybe_added_TAll,tc_types2) = replace_CV_with_TempQV_by_TAll class_args tc_types
					| maybe_added_TAll
						# (cur, tc_types2, env) = cleanUpClosed tc_types2 env
						| cur==0
							-> ([{tc & tc_types = tc_types2} : collected_contexts], ambiguous_or_missing_contexts, env, var_heap, error)
							-> (collected_contexts, ambiguous_or_missing_contexts, env, var_heap, error)
						-> (collected_contexts, ambiguous_or_missing_contexts, env, var_heap, error)
				TCGeneric {gtc_class={glob_module,glob_object={ds_index}}}
					# class_args = common_defs.[glob_module].com_class_defs.[ds_index].class_args
					# (maybe_added_TAll,tc_types2) = replace_CV_with_TempQV_by_TAll class_args tc_types
					| maybe_added_TAll
						# (cur, tc_types2, env) = cleanUpClosed tc_types2 env
						| cur==0
							-> ([{tc & tc_types = tc_types2} : collected_contexts], ambiguous_or_missing_contexts, env, var_heap, error)
							-> (collected_contexts, ambiguous_or_missing_contexts, env, var_heap, error)
						-> (collected_contexts, ambiguous_or_missing_contexts, env, var_heap, error)
				_
					-> (collected_contexts, ambiguous_or_missing_contexts, env, var_heap, error)
			= ([{tc & tc_types = tc_types} : collected_contexts], ambiguous_or_missing_contexts, env, var_heap, error)

	clean_up_type_context2 tc=:{tc_types,tc_class,tc_var} (collected_contexts, ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
		| (sreadPtr tc_var var_heap)=:VI_EmptyConstructorClassVar
			= (collected_contexts, ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
		# (cur, tc_types, env) = cleanUpClosed tc_types env
		| cur bitand (bitnot cDefinedVar)==0
			= ([{tc & tc_types = tc_types} : collected_contexts], ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
		| checkCleanUpResult cur cUndefinedVar
			# ambiguous_or_missing_contexts = AmbiguousContext {tc & tc_types = tc_types} ambiguous_or_missing_contexts
			= (collected_contexts, ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
		| checkCleanUpResult cur cLiftedVar
			# error = liftedContextError (toString tc_class) error
			= ([{tc & tc_types = tc_types} : collected_contexts], ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
		| checkCleanUpResult cur cQVar
			= case tc_class of
				TCClass {glob_module,glob_object={ds_index}}
					# class_args = common_defs.[glob_module].com_class_defs.[ds_index].class_args
					# (maybe_added_TAll,tc_types2) = replace_CV_with_TempQV_by_TAll class_args tc_types
					| maybe_added_TAll
						# (cur, tc_types2, env) = cleanUpClosed tc_types2 env
						| cur==0
							# tc & tc_types = tc_types2
							# (context_found,equal_collected_context,type_heaps)
								= find_equal_context tc collected_contexts type_heaps
							| not context_found
								-> ([tc : collected_contexts], ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
								# var_heap = writePtr tc.tc_var (VI_ForwardTypeContextVar equal_collected_context.tc_var) var_heap
								-> (collected_contexts, ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
							-> (collected_contexts, ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
						-> (collected_contexts, ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
				TCGeneric {gtc_class={glob_module,glob_object={ds_index}}}
					# class_args = common_defs.[glob_module].com_class_defs.[ds_index].class_args
					# (maybe_added_TAll,tc_types2) = replace_CV_with_TempQV_by_TAll class_args tc_types
					| maybe_added_TAll
						# (cur, tc_types2, env) = cleanUpClosed tc_types2 env
						| cur==0
							# tc & tc_types = tc_types2
							# (context_found,equal_collected_context,type_heaps)
								= find_equal_context tc collected_contexts type_heaps
							| not context_found
								-> ([tc : collected_contexts], ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
								# var_heap = writePtr tc.tc_var (VI_ForwardTypeContextVar equal_collected_context.tc_var) var_heap
								-> (collected_contexts, ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
							-> (collected_contexts, ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
						-> (collected_contexts, ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
				_
					-> (collected_contexts, ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)
			= ([{tc & tc_types = tc_types} : collected_contexts], ambiguous_or_missing_contexts, env, type_heaps, var_heap, error)

	replace_CV_with_TempQV_by_TAll (ClassArgPattern _ class_arg_vars class_args) [CV type_var:@:cv_arg_types:tc_types]
		| length class_arg_vars==length cv_arg_types
			# cv_type = CV type_var :@: replace_TempQV_by_TAll cv_arg_types
			# (_,tc_types) = replace_CV_with_TempQV_by_TAll class_args tc_types
			= (True,[cv_type:tc_types])
	replace_CV_with_TempQV_by_TAll (ClassArgPatternSameTypeVar class_arg_vars class_args) [CV type_var:@:cv_arg_types:tc_types]
		| length class_arg_vars==length cv_arg_types
			# cv_type = CV type_var :@: replace_TempQV_by_TAll cv_arg_types
			# (_,tc_types) = replace_CV_with_TempQV_by_TAll class_args tc_types
			= (True,[cv_type:tc_types])
	replace_CV_with_TempQV_by_TAll _ tc_types
		= (False,tc_types)

	replace_TempQV_by_TAll cv_arg_types
		= [if type.at_type=:TempQV _ {type & at_type=TAll} type \\ type<-cv_arg_types]

build_attribute_environment :: !LargeBitvect !Index !{!CoercionTree} !*AttributeEnv !*ErrorAdmin
	-> (!*AttributeEnv,![AttributeVar],![AttributeVar],![AttrInequality],![AttrInequality],!*ErrorAdmin)
build_attribute_environment appears_in_lifted_part max_attr_nr coercions attr_env error
	= build_attribute_environment appears_in_lifted_part 0 max_attr_nr coercions (bitvectCreate max_attr_nr) attr_env [] [] [] [] error
where
	build_attribute_environment :: !LargeBitvect !Index !Index !{!CoercionTree} !*LargeBitvect
										!*AttributeEnv ![AttributeVar] ![AttributeVar] ![AttrInequality] ![AttrInequality] !*ErrorAdmin
									-> (!*AttributeEnv,![AttributeVar],![AttributeVar],![AttrInequality],![AttrInequality],!*ErrorAdmin)
	build_attribute_environment appears_in_lifted_part attr_group_index max_attr_nr coercions already_build_inequalities attr_env
			attr_vars lifted_attr_vars inequalities lifted_inequalities error
		| attr_group_index == max_attr_nr
			= (attr_env,attr_vars,lifted_attr_vars,inequalities,lifted_inequalities,error)
		# (attr, attr_env) = attr_env![attr_group_index]
		= case attr of
			TA_Var attr_var
				# already_build_inequalities = bitvectResetAll already_build_inequalities
				  attr_appears_in_lifted_part = bitvectSelect attr_group_index appears_in_lifted_part
				  (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
						= build_inequalities attr_appears_in_lifted_part attr_var coercions.[attr_group_index]
							coercions appears_in_lifted_part True attr_env inequalities lifted_inequalities already_build_inequalities
				  error = case ok of
				  			True
				  				-> error
				  			_
				  				-> checkError "attribute variable of lifted argument appears in derived attribute inequality"
				  					"" error
				| attr_appears_in_lifted_part
					# lifted_attr_vars = [attr_var : lifted_attr_vars]
					-> build_attribute_environment appears_in_lifted_part (inc attr_group_index) max_attr_nr coercions already_build_inequalities
						attr_env attr_vars lifted_attr_vars inequalities lifted_inequalities error
					# attr_vars = [attr_var : attr_vars]
					-> build_attribute_environment appears_in_lifted_part (inc attr_group_index) max_attr_nr coercions already_build_inequalities
						attr_env attr_vars lifted_attr_vars inequalities lifted_inequalities error
			TA_None
				-> build_attribute_environment appears_in_lifted_part (inc attr_group_index) max_attr_nr coercions already_build_inequalities
					attr_env attr_vars lifted_attr_vars inequalities lifted_inequalities error

	build_inequalities :: Bool AttributeVar !CoercionTree {!CoercionTree} LargeBitvect !Bool !*{!TypeAttribute}  [AttrInequality]  [AttrInequality] !*LargeBitvect
																				   -> (!Bool,!*{!TypeAttribute},![AttrInequality],![AttrInequality],!*LargeBitvect)
	build_inequalities off_appears_in_lifted_part off_var (CT_Node dem_attr left right)
			coercions appears_in_lifted_part ok attr_env inequalities lifted_inequalities already_build_inequalities
		# (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
				= build_inequalities off_appears_in_lifted_part off_var left
					coercions appears_in_lifted_part ok attr_env inequalities lifted_inequalities already_build_inequalities
		  (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
				= build_inequalities off_appears_in_lifted_part off_var right
					coercions appears_in_lifted_part ok attr_env inequalities lifted_inequalities already_build_inequalities
		  (attr, attr_env) = attr_env![dem_attr]
		= case attr of
			TA_Var attr_var
				#! dem_appears_in_lifted_part = bitvectSelect dem_attr appears_in_lifted_part
				| off_appears_in_lifted_part && dem_appears_in_lifted_part
					| is_new_inequality attr_var off_var lifted_inequalities
						# lifted_inequalities = [{ai_demanded = attr_var, ai_offered = off_var} : lifted_inequalities]
						-> (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)	
						-> (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
				| is_new_inequality attr_var off_var inequalities
					# inequalities = [{ai_demanded = attr_var, ai_offered = off_var} : inequalities]
					| off_appears_in_lifted_part==dem_appears_in_lifted_part
						-> (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
						-> (False,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
					-> (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
			TA_None
				# (already_build_inequality,already_build_inequalities) = bitvectTestAndSet dem_attr already_build_inequalities
				| already_build_inequality
					-> (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
				-> build_inequalities off_appears_in_lifted_part off_var coercions.[dem_attr]
						coercions appears_in_lifted_part ok attr_env inequalities lifted_inequalities already_build_inequalities
	build_inequalities _ off_var tree coercions _ ok attr_env inequalities lifted_inequalities already_build_inequalities
		= (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)

build_attribute_environment_with_external_vars :: !LargeBitvect !LargeBitvect !Index !{!CoercionTree} !*AttributeEnv !*ErrorAdmin
	-> (!*AttributeEnv,![AttributeVar],![AttributeVar],![AttrInequality],![AttrInequality],!*ErrorAdmin)
build_attribute_environment_with_external_vars appears_in_lifted_part external_vars max_attr_nr coercions attr_env error
	= build_attribute_environment 0 appears_in_lifted_part external_vars max_attr_nr coercions (bitvectCreate max_attr_nr) attr_env [] [] [] [] error
where
	build_attribute_environment :: !Index !LargeBitvect  !LargeBitvect  !Index !{!CoercionTree} !*LargeBitvect
										!*AttributeEnv ![AttributeVar] ![AttributeVar] ![AttrInequality] ![AttrInequality] !*ErrorAdmin
									-> (!*AttributeEnv,![AttributeVar],![AttributeVar],![AttrInequality],![AttrInequality],!*ErrorAdmin)
	build_attribute_environment attr_group_index appears_in_lifted_part external_vars max_attr_nr coercions already_build_inequalities attr_env
			attr_vars lifted_attr_vars inequalities lifted_inequalities error
		| attr_group_index == max_attr_nr
			= (attr_env,attr_vars,lifted_attr_vars,inequalities,lifted_inequalities,error)
		# (attr, attr_env) = attr_env![attr_group_index]
		= case attr of
			TA_Var attr_var
				# already_build_inequalities = bitvectResetAll already_build_inequalities
				| bitvectSelect attr_group_index external_vars
					# (attr_env,inequalities,lifted_inequalities,already_build_inequalities)
							= build_inequalities_for_external_attr attr_var coercions.[attr_group_index]
								coercions appears_in_lifted_part attr_env inequalities lifted_inequalities already_build_inequalities
					  attr_vars = [attr_var : attr_vars]
					-> build_attribute_environment (inc attr_group_index) appears_in_lifted_part external_vars max_attr_nr coercions already_build_inequalities
							attr_env attr_vars lifted_attr_vars inequalities lifted_inequalities error
					# attr_appears_in_lifted_part = bitvectSelect attr_group_index appears_in_lifted_part
					  (ok, attr_env,inequalities,lifted_inequalities,already_build_inequalities)
							= build_inequalities attr_appears_in_lifted_part attr_var coercions.[attr_group_index] coercions
								appears_in_lifted_part external_vars True attr_env inequalities lifted_inequalities already_build_inequalities
					  error = case ok of
								True
									-> error
								_
									-> checkError "attribute variable of lifted argument appears in derived attribute inequality"
										"" error
					| attr_appears_in_lifted_part
						# lifted_attr_vars = [attr_var : lifted_attr_vars]
						-> build_attribute_environment (inc attr_group_index) appears_in_lifted_part external_vars max_attr_nr coercions already_build_inequalities
							attr_env attr_vars lifted_attr_vars inequalities lifted_inequalities error
						# attr_vars = [attr_var : attr_vars]
						-> build_attribute_environment (inc attr_group_index) appears_in_lifted_part external_vars max_attr_nr coercions already_build_inequalities
							attr_env attr_vars lifted_attr_vars inequalities lifted_inequalities error
			TA_None
				-> build_attribute_environment (inc attr_group_index) appears_in_lifted_part external_vars max_attr_nr coercions already_build_inequalities
					attr_env attr_vars lifted_attr_vars inequalities lifted_inequalities error

	build_inequalities_for_external_attr :: AttributeVar !CoercionTree {!CoercionTree} !LargeBitvect
												!*{!TypeAttribute} ![AttrInequality] ![AttrInequality] !*LargeBitvect
											-> (!*{!TypeAttribute},![AttrInequality],![AttrInequality],!*LargeBitvect)
	build_inequalities_for_external_attr off_var (CT_Node dem_attr left right)
			coercions appears_in_lifted_part attr_env inequalities lifted_inequalities already_build_inequalities
		# (attr_env,inequalities,lifted_inequalities,already_build_inequalities)
				= build_inequalities_for_external_attr off_var left
					coercions appears_in_lifted_part attr_env inequalities lifted_inequalities already_build_inequalities
		  (attr_env,inequalities,lifted_inequalities,already_build_inequalities)
				= build_inequalities_for_external_attr off_var right
					coercions appears_in_lifted_part attr_env inequalities lifted_inequalities already_build_inequalities
		# (attr, attr_env) = attr_env![dem_attr]
		= case attr of
			TA_Var attr_var
				| bitvectSelect dem_attr appears_in_lifted_part
					| is_new_inequality attr_var off_var lifted_inequalities
						# lifted_inequalities = [{ai_demanded = attr_var, ai_offered = off_var} : lifted_inequalities]
						-> (attr_env,inequalities,lifted_inequalities,already_build_inequalities)
						-> (attr_env,inequalities,lifted_inequalities,already_build_inequalities)
					| is_new_inequality attr_var off_var inequalities
						# inequalities = [{ai_demanded = attr_var, ai_offered = off_var} : inequalities]
						-> (attr_env,inequalities,lifted_inequalities,already_build_inequalities)
						-> (attr_env,inequalities,lifted_inequalities,already_build_inequalities)
			TA_None
				# (already_build_inequality,already_build_inequalities) = bitvectTestAndSet dem_attr already_build_inequalities
				| already_build_inequality
					-> (attr_env,inequalities,lifted_inequalities,already_build_inequalities)
				-> build_inequalities_for_external_attr off_var coercions.[dem_attr]
					coercions appears_in_lifted_part attr_env inequalities lifted_inequalities already_build_inequalities
	build_inequalities_for_external_attr off_var tree
			coercions appears_in_lifted_part attr_env inequalities lifted_inequalities already_build_inequalities
		= (attr_env,inequalities,lifted_inequalities,already_build_inequalities)

	build_inequalities :: Bool AttributeVar !CoercionTree {!CoercionTree} LargeBitvect LargeBitvect
								!Bool !*{!TypeAttribute} ![AttrInequality] ![AttrInequality] !*LargeBitvect
							-> (!Bool,!*{!TypeAttribute},![AttrInequality],![AttrInequality],!*LargeBitvect)
	build_inequalities off_appears_in_lifted_part off_var (CT_Node dem_attr left right)
			coercions appears_in_lifted_part external_vars ok attr_env inequalities lifted_inequalities already_build_inequalities
		# (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
				= build_inequalities off_appears_in_lifted_part off_var left
					coercions appears_in_lifted_part external_vars ok attr_env inequalities lifted_inequalities already_build_inequalities
		  (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
				= build_inequalities off_appears_in_lifted_part off_var right
					coercions appears_in_lifted_part external_vars ok attr_env inequalities lifted_inequalities already_build_inequalities
		# (attr, attr_env) = attr_env![dem_attr]
		= case attr of
			TA_Var attr_var
				| off_appears_in_lifted_part
					| bitvectSelect dem_attr appears_in_lifted_part || bitvectSelect dem_attr external_vars
						| is_new_inequality attr_var off_var lifted_inequalities
							# lifted_inequalities = [{ai_demanded = attr_var, ai_offered = off_var} : lifted_inequalities]
							-> (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
							-> (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
						| is_new_inequality attr_var off_var inequalities
							# inequalities = [{ai_demanded = attr_var, ai_offered = off_var} : inequalities]
							-> (False,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
							-> (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
					| is_new_inequality attr_var off_var inequalities
						| not (bitvectSelect dem_attr appears_in_lifted_part) || bitvectSelect dem_attr external_vars
							# inequalities = [{ai_demanded = attr_var, ai_offered = off_var} : inequalities]
							-> (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
							# inequalities = [{ai_demanded = attr_var, ai_offered = off_var} : inequalities]
							-> (False,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
						-> (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
			TA_None
				# (already_build_inequality,already_build_inequalities) = bitvectTestAndSet dem_attr already_build_inequalities
				| already_build_inequality
					-> (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)
				-> build_inequalities off_appears_in_lifted_part off_var coercions.[dem_attr]
					coercions appears_in_lifted_part external_vars ok attr_env inequalities lifted_inequalities already_build_inequalities
	build_inequalities _ off_var tree coercions appears_in_lifted_part external_vars ok attr_env inequalities lifted_inequalities already_build_inequalities
		= (ok,attr_env,inequalities,lifted_inequalities,already_build_inequalities)

is_new_inequality dem_var off_var []
	= True
is_new_inequality dem_var off_var [{ ai_demanded, ai_offered } : inequalities]
	= (dem_var <> ai_demanded || off_var <> ai_offered) && is_new_inequality dem_var off_var inequalities

clean_up_expression_types :: ![ExprInfoPtr] !*ExpressionHeap !*CleanUpExprTypeState -> (!*ExpressionHeap,!*CleanUpExprTypeState)
clean_up_expression_types expr_ptrs expr_heap cuets
	= foldSt clean_up_expression_type expr_ptrs (expr_heap, cuets)
where
	clean_up_expression_type expr_ptr (expr_heap, cuets)
		# (info, expr_heap) = readPtr expr_ptr expr_heap
		= case info of
			EI_CaseType case_type
				# (case_type, cuets) = clean_up_expr_type case_type cuets
				-> (expr_heap <:= (expr_ptr, EI_CaseType case_type), cuets)
			EI_LetType let_type
				# (let_type, cuets) = clean_up_expr_type let_type cuets
				-> (expr_heap <:= (expr_ptr, EI_LetType let_type), cuets)
			EI_DictionaryType dict_type
				# (dict_type, cuets) = clean_up_expr_type dict_type cuets
				-> (expr_heap <:= (expr_ptr, EI_DictionaryType dict_type), cuets)
			EI_ContextWithVarContexts class_expressions var_contexts
				# (var_contexts,cuets) = clean_up_var_contexts var_contexts cuets
				-> (writePtr expr_ptr (EI_ContextWithVarContexts class_expressions var_contexts) expr_heap,cuets)
			where
				clean_up_var_contexts (VarContext arg_n type_contexts arg_atype var_contexts) cuets
					# (type_contexts,cuets) = clean_up_expr_type type_contexts cuets
					  (arg_atype,cuets) = clean_up_expr_type arg_atype cuets
					  (var_contexts,cuets) = clean_up_var_contexts var_contexts cuets
					= (VarContext arg_n type_contexts arg_atype var_contexts,cuets)
				clean_up_var_contexts NoVarContexts cuets
					= (NoVarContexts,cuets)
			EI_CaseTypeWithContexts case_type constructor_contexts
				# (case_type, cuets) = clean_up_expr_type case_type cuets
				  (constructor_contexts, cuets) = clean_up_constructor_contexts constructor_contexts cuets
				-> (expr_heap <:= (expr_ptr, EI_CaseTypeWithContexts case_type constructor_contexts), cuets)
			where
				clean_up_constructor_contexts [(ds,type_contexts):constructor_contexts] cuets
					# (type_contexts,cuets) = clean_up_type_contexts type_contexts cuets
					  (constructor_contexts,cuets) = clean_up_constructor_contexts constructor_contexts cuets
					= ([(ds,type_contexts):constructor_contexts],cuets)
				clean_up_constructor_contexts [] cuets
					= ([],cuets)

				clean_up_type_contexts [type_contexts=:{tc_types}:constructor_contexts] cuets
					# (tc_types,cuets) = clean_up_expr_type tc_types cuets
					  (constructor_contexts,cuets) = clean_up_type_contexts constructor_contexts cuets
					= ([{type_contexts & tc_types=tc_types}:constructor_contexts],cuets)
				clean_up_type_contexts [] cuets
					= ([],cuets)

/*
	In 'bindInstances t1 t2' type variables of t1 are bound to the corresponding subtypes of t2, provided that
	t2 is a substitution instance of t1. Binding is done by setting the 'tv_info_ptr' of the variables of t1
	to 'TVI_Type t' were t is the subtype to which the type variable is matched.
	Be careful with calling 'bindInstances': all the 'tv_info_ptr'-info's should be cleaned first, unless one 
	is sure that t1 does not contain any 'tv_info_ptr' with value  'TVI_Type ...'.

	instance bindInstances AType, Type, [a] | bindInstances a
*/ 

updateExpressionTypes :: !SymbolType !SymbolType ![ExprInfoPtr] !*TypeHeaps !*ExpressionHeap -> (!*TypeHeaps, !*ExpressionHeap)
updateExpressionTypes {st_args,st_vars,st_result,st_attr_vars} st_copy type_ptrs heaps=:{th_vars,th_attrs} expr_heap
	# th_vars = foldSt (\{tv_info_ptr} var_heap -> var_heap <:= (tv_info_ptr, TVI_Empty)) st_vars th_vars
	  th_attrs = foldSt (\{av_info_ptr} attr_heap -> attr_heap <:= (av_info_ptr, AVI_Empty)) st_attr_vars th_attrs
	  heaps = fold2St bind_instances_in_arg_type st_args st_copy.st_args {heaps & th_vars = th_vars, th_attrs = th_attrs}
	  th_vars = bindInstances st_result st_copy.st_result heaps.th_vars
	= foldSt update_expression_type type_ptrs ({heaps & th_vars = th_vars}, expr_heap)
where
	bind_instances_in_arg_type {at_type = TFA vars type1} {at_type = TFA _ type2} heaps
		# heaps = clear_atype_vars vars heaps
		= {heaps & th_vars = bindInstances type1 type2 heaps.th_vars}
	bind_instances_in_arg_type {at_type = TFAC vars type1 _} {at_type = TFAC _ type2 _} heaps
		# heaps = clear_atype_vars vars heaps
		= {heaps & th_vars = bindInstances type1 type2 heaps.th_vars}
	bind_instances_in_arg_type { at_type } atype2 heaps=:{th_vars}
		= { heaps & th_vars = bindInstances at_type atype2.at_type th_vars }

	clear_atype_vars vars heaps
		= foldSt clear_atype_var vars heaps
	where
		clear_atype_var {atv_variable={tv_info_ptr},atv_attribute} heaps=:{th_vars,th_attrs}
			= {heaps & th_vars = th_vars  <:= (tv_info_ptr, TVI_Empty), th_attrs = clear_attribute atv_attribute th_attrs}

		clear_attribute (TA_Var {av_info_ptr}) attr_heap
			= attr_heap <:= (av_info_ptr, AVI_Empty)
		clear_attribute _ attr_heap
			= attr_heap

	update_expression_type expr_ptr (type_heaps, expr_heap)
		# (info, expr_heap) = readPtr expr_ptr expr_heap
		= case info of
			EI_CaseType case_type
				# (changed, case_type_r, type_heaps) = substitute case_type type_heaps
				| changed
					-> (type_heaps, expr_heap <:= (expr_ptr, EI_CaseType case_type_r))
					-> (type_heaps, expr_heap)
			EI_LetType let_type
				# (changed, let_type_r, type_heaps) = substitute let_type type_heaps
				| changed
					-> (type_heaps, expr_heap <:= (expr_ptr, EI_LetType let_type_r))
					-> (type_heaps, expr_heap)
			EI_DictionaryType dict_type
				# (changed, dict_type_r, type_heaps) = substitute dict_type type_heaps
				| changed
					-> (type_heaps, expr_heap <:= (expr_ptr, EI_DictionaryType dict_type_r))
					-> (type_heaps, expr_heap)
			EI_ContextWithVarContexts class_expressions var_contexts
				# (var_contexts,type_heaps) = substitute_var_contexts var_contexts type_heaps
				-> (type_heaps,writePtr expr_ptr (EI_ContextWithVarContexts class_expressions var_contexts) expr_heap)
			where
				substitute_var_contexts (VarContext arg_n type_contexts arg_atype var_contexts) type_heaps
					# (_, type_contexts,type_heaps) = substitute type_contexts type_heaps
					  (_, arg_atype,type_heaps) = substitute arg_atype type_heaps
					  (var_contexts,type_heaps) = substitute_var_contexts var_contexts type_heaps
					= (VarContext arg_n type_contexts arg_atype var_contexts,type_heaps)
				substitute_var_contexts NoVarContexts type_heaps
					= (NoVarContexts,type_heaps)
			EI_CaseTypeWithContexts case_type constructor_contexts
				# (_,case_type, type_heaps) = substitute case_type type_heaps
				  (constructor_contexts, type_heaps) = substitute_constructor_contexts constructor_contexts type_heaps
				-> (type_heaps, expr_heap <:= (expr_ptr, EI_CaseTypeWithContexts case_type constructor_contexts))
		where
			substitute_constructor_contexts [(cons_symbol,context):constructor_contexts] type_heaps
				# (_, context, type_heaps) = substitute context type_heaps
				  (constructor_contexts, type_heaps) = substitute_constructor_contexts constructor_contexts type_heaps
				= ([(cons_symbol,context):constructor_contexts],type_heaps)
			substitute_constructor_contexts [] type_heaps
				= ([],type_heaps)

instance substitute DictionaryAndClassType where
	substitute {dc_var,dc_class_type} type_heaps
		# (changed,dc_class_type_r,type_heaps) = substitute dc_class_type type_heaps
		| changed
			= (True, {dc_var=dc_var,dc_class_type=dc_class_type_r},type_heaps)
			= (False, {dc_var=dc_var,dc_class_type=dc_class_type},type_heaps)

class bindInstances a :: !a !a !*TypeVarHeap -> *TypeVarHeap

instance bindInstances Type
  where
	bindInstances (TV {tv_info_ptr}) type type_var_heap
		# (tv_info, type_var_heap) = readPtr tv_info_ptr type_var_heap
		= case tv_info of
			TVI_Type ind_type
				-> type_var_heap
			_
				-> type_var_heap <:= (tv_info_ptr, TVI_Type type)
	bindInstances (TA _ arg_types1) (TA _ arg_types2) type_var_heap
		= bindInstances arg_types1 arg_types2 type_var_heap
	bindInstances (TA _ arg_types1) (TAS _ arg_types2 _) type_var_heap
		= bindInstances arg_types1 arg_types2 type_var_heap
	bindInstances (TAS _ arg_types1 _) (TA _ arg_types2) type_var_heap
		= bindInstances arg_types1 arg_types2 type_var_heap
	bindInstances (TAS _ arg_types1 _) (TAS _ arg_types2 _) type_var_heap
		= bindInstances arg_types1 arg_types2 type_var_heap
	bindInstances (l1 --> r1) (l2 --> r2) type_var_heap
		= bindInstances r1 r2 (bindInstances l1 l2 type_var_heap)
	bindInstances (TB _) (TB _) type_var_heap
		= type_var_heap
	bindInstances TArrow TArrow type_var_heap
		= type_var_heap
	bindInstances (TArrow1 x1) (TArrow1 x2) type_var_heap
		= bindInstances x1 x2 type_var_heap
	bindInstances (TFA _ type1) (TFA _ type2) type_var_heap
		= bindInstances type1 type2 type_var_heap
	bindInstances (CV l1 :@: r1) (CV l2 :@: r2) type_var_heap
		= bindInstances r1 r2 (bindInstances (TV l1) (TV l2) type_var_heap)

instance bindInstances [a] | bindInstances a
  where
	bindInstances [] [] type_var_heap
		= type_var_heap
	bindInstances [x:xs] [y:ys] type_var_heap
		= bindInstances xs ys (bindInstances x y type_var_heap)
	
instance bindInstances AType
  where
	bindInstances {at_type=t1} {at_type=t2} type_var_heap
			= bindInstances t1 t2 type_var_heap

tryToExpand :: !Type !TypeAttribute !{# CommonDefs} !*TypeHeaps -> (!Bool, !Type, !*TypeHeaps)
tryToExpand type=:(TA {type_index={glob_object,glob_module}} type_args) type_attr ti_common_defs type_heaps
	#! type_def = ti_common_defs.[glob_module].com_type_defs.[glob_object]
	= case type_def.td_rhs of
		SynType {at_type}
			# (expanded_type, type_heaps) = substituteType type_def.td_attribute type_attr type_def.td_args type_args at_type type_heaps
			-> (True, expanded_type, type_heaps)
		_
			-> (False, type, type_heaps)
tryToExpand type=:(TAS {type_index={glob_object,glob_module}} type_args _) type_attr ti_common_defs type_heaps
	#! type_def = ti_common_defs.[glob_module].com_type_defs.[glob_object]
	= case type_def.td_rhs of
		SynType {at_type}
			# (expanded_type, type_heaps) = substituteType type_def.td_attribute type_attr type_def.td_args type_args at_type type_heaps
			-> (True, expanded_type, type_heaps)
		_
			-> (False, type, type_heaps)
tryToExpand type type_attr modules type_heaps
	= (False, type, type_heaps)

substituteType :: !TypeAttribute !TypeAttribute ![ATypeVar] ![AType] !Type !*TypeHeaps -> (!Type, !*TypeHeaps)
substituteType form_root_attribute act_root_attribute form_type_args act_type_args orig_type type_heaps
	# type_heaps = bindTypeVarsAndAttributes form_root_attribute act_root_attribute form_type_args act_type_args type_heaps
	  (_, expanded_type, type_heaps) = substitute orig_type type_heaps
	= (expanded_type, clearBindingsOfTypeVarsAndAttributes form_root_attribute form_type_args type_heaps)

bindTypeVarsAndAttributes :: !TypeAttribute !TypeAttribute ![ATypeVar] ![AType] !*TypeHeaps -> *TypeHeaps
bindTypeVarsAndAttributes form_root_attribute act_root_attribute form_type_args act_type_args type_heaps
	# th_attrs = bind_attribute form_root_attribute act_root_attribute type_heaps.th_attrs	
	= fold2St bind_type_and_attr form_type_args act_type_args { type_heaps & th_attrs = th_attrs }
where
	bind_type_and_attr {atv_attribute, atv_variable={tv_info_ptr}} {at_type,at_attribute} type_heaps=:{th_vars,th_attrs}
		= { type_heaps &	th_vars = th_vars <:= (tv_info_ptr, TVI_Type at_type),
							th_attrs = bind_attribute atv_attribute at_attribute th_attrs }

	bind_attribute (TA_Var {av_info_ptr}) attr th_attrs
		= th_attrs <:= (av_info_ptr, AVI_Attr attr)
	bind_attribute _ _ th_attrs
		= th_attrs

clearBindingsOfTypeVarsAndAttributes :: !TypeAttribute ![ATypeVar] !*TypeHeaps -> *TypeHeaps
clearBindingsOfTypeVarsAndAttributes form_root_attribute form_type_args type_heaps
	# th_attrs = clear_attribute form_root_attribute type_heaps.th_attrs
	= foldSt clear_type_and_attr form_type_args { type_heaps & th_attrs = th_attrs }
where
	clear_type_and_attr {atv_attribute, atv_variable={tv_info_ptr}} type_heaps=:{th_vars,th_attrs}
		= { type_heaps & th_vars = th_vars <:= (tv_info_ptr, TVI_Empty), th_attrs = clear_attribute atv_attribute th_attrs }
		
	clear_attribute (TA_Var {av_info_ptr}) th_attrs
		= th_attrs <:= (av_info_ptr, AVI_Empty)
	clear_attribute _ th_attrs
		= th_attrs

VarIdTable :: {# String}
VarIdTable =: { "a", "b", "c", "d", "e", "f", "g", "h", "i", "j" }

newIdent id_name
	:== { id_name = id_name, id_info = nilPtr }
	
NewVarId var_store
	| var_store < size VarIdTable
		= newIdent VarIdTable.[var_store]
		= newIdent ("v" +++ toString var_store)
 
AttrVarIdTable :: {!Ident}
AttrVarIdTable =: {newIdent  i \\ i<-: {# "u", "v", "w", "x", "y", "z" }}

AttrVarIdTables :: [#{!Ident}]
AttrVarIdTables
	=: [# let first_i=12*(1<<p) in {!newIdent ("u" +++ toString (i-6)) \\ i<-[first_i..first_i+first_i-1]} \\ p<-[0..] ]

NewAttrVar :: !Int !*AttrVarHeap -> (!AttributeVar,!*AttrVarHeap)
NewAttrVar attr_var_store th_attrs
	| attr_var_store < size AttrVarIdTable
		# (av_info_ptr, th_attrs) = newPtr AVI_Empty th_attrs
 		= ({av_ident=AttrVarIdTable.[attr_var_store],av_info_ptr=av_info_ptr},th_attrs)
 		= getAttrVarId AttrVarIdTables (attr_var_store-6) 12 th_attrs
where
	getAttrVarId [#attrVarIds_array:attrVarId_list] i p th_attrs
		| i<p
			# (av_info_ptr, th_attrs) = newPtr AVI_Empty th_attrs
			= ({av_ident=attrVarIds_array.[i],av_info_ptr=av_info_ptr},th_attrs)
			= getAttrVarId attrVarId_list (i-p) (p+p) th_attrs

class equiv a :: !a !a !*TypeHeaps -> (!Bool, !*TypeHeaps)

instance equiv AType
where
	equiv atype1 atype2 heaps=:{th_attrs}
		# (ok, th_attrs) = equi_attrs atype1.at_attribute atype2.at_attribute th_attrs
		| ok
			= equiv atype1.at_type atype2.at_type { heaps & th_attrs = th_attrs }
			= (False, { heaps & th_attrs = th_attrs })
	where
		equi_attrs attr=:(TA_Var {av_info_ptr}) (TA_TempVar av_number) attr_var_heap
			# (av_info, attr_var_heap) = readPtr av_info_ptr attr_var_heap
			= case av_info of
				AVI_Forward forw_var_number
					-> (forw_var_number == av_number, attr_var_heap)
				_
					-> (True, writePtr av_info_ptr (AVI_Forward av_number) attr_var_heap)
		equi_attrs (TA_Var _) (TA_Var _) attr_var_heap
			= (True, attr_var_heap)
		equi_attrs attr1 attr2 attr_var_heap
			= (attr1 == attr2, attr_var_heap)

equivTypeVars :: !TypeVar !TempVarId !*TypeVarHeap -> (!Bool, !*TypeVarHeap)
equivTypeVars {tv_info_ptr} var_number type_var_heap
	# (tv_info, type_var_heap) = readPtr tv_info_ptr type_var_heap
	= case tv_info of
		TVI_Forward forw_var_number
			-> (forw_var_number == var_number, type_var_heap)
		_
			-> (True, type_var_heap <:= (tv_info_ptr, TVI_Forward var_number))

instance equiv Type
where
	equiv (TV tv) (TempV var_number) heaps=:{th_vars}
		# (equiv, th_vars) = equivTypeVars tv var_number th_vars
		= (equiv, { heaps & th_vars = th_vars })
	equiv (TV tv1) (TV tv2) heaps
		= (True, heaps)
	equiv (arg_type1 --> restype1) (arg_type2 --> restype2) heaps
		= equiv (arg_type1,restype1) (arg_type2,restype2) heaps
	equiv (TArrow1 arg_type1) (TArrow1 arg_type2) heaps
		= equiv arg_type1 arg_type2 heaps
	equiv TArrow TArrow heaps
		= (True, heaps)
	equiv (TA tc1 types1) (TA tc2 types2) heaps
		| tc1 == tc2
			= equiv types1 types2 heaps
			= (False, heaps)
	equiv (TA tc1 types1) (TAS tc2 types2 _) heaps
		| tc1 == tc2
			= equiv types1 types2 heaps
			= (False, heaps)
	equiv (TAS tc1 types1 _) (TA tc2 types2) heaps
		| tc1 == tc2
			= equiv types1 types2 heaps
			= (False, heaps)
	equiv (TAS tc1 types1 _) (TAS tc2 types2 _) heaps
		| tc1 == tc2
			= equiv types1 types2 heaps
			= (False, heaps)
	equiv (TB basic1) (TB basic2) heaps
		= (basic1 == basic2, heaps)
	equiv (CV tv :@: types1) (TempCV var_number :@: types2) heaps=:{th_vars}
		# (equi_vars, th_vars) =  equivTypeVars tv var_number th_vars
		| equi_vars
			= equiv types1 types2 { heaps & th_vars = th_vars }
			= (False, { heaps & th_vars = th_vars })
	equiv (CV tv1 :@: types1) (CV tv2 :@: types2) heaps
		// should occur only for A. type variables
		= equiv types1 types2 heaps
	equiv TAll TAll heaps
		= (True, heaps)
	equiv (TFA vars1 type1) (TFA vars2 type2) heaps
		= equiv type1 type2 heaps
	equiv (TFAC vars1 type1 _) (TFAC vars2 type2 _) heaps
		= equiv type1 type2 heaps
	equiv type1 type2 heaps
		= (False, heaps)

instance equiv (a,b) | equiv a & equiv b
where
	equiv (x1,y1) (x2,y2) heaps
		# (equi_x, heaps) =  equiv x1 x2 heaps
		| equi_x
			= equiv y1 y2 heaps
			= (False, heaps)

instance equiv [a] | equiv a
where
	equiv [x:xs] [y:ys] heaps
		# (equi, heaps) = equiv x y heaps
		| equi
		  	= equiv xs ys heaps
			= (False, heaps)
	equiv [] [] heaps
		= (True, heaps)
	equiv _ _ heaps
		= (False, heaps)

set_class_args_types :: !ClassArgs ![Type] !*TypeVarHeap -> *TypeVarHeap
set_class_args_types (ClassArg {tv_info_ptr} class_args) [type:types] type_var_heap
	= set_class_args_types class_args types (writePtr tv_info_ptr (TVI_Type type) type_var_heap)
set_class_args_types (ClassArgPattern bind_dst pattern_vars type_vars) [type=:TA type_cons=:{type_arity} a_types:types] type_var_heap
	#! n_pattern_vars = length pattern_vars
	| type_arity==n_pattern_vars
		# type = TA {type_cons & type_arity=0} []
		# type_var_heap = set_class_arg_pattern pattern_vars a_types type_var_heap
		# type_var_heap = writePtr bind_dst.tv_info_ptr (TVI_Type type) type_var_heap
		= set_class_args_types type_vars types type_var_heap
	| type_arity>n_pattern_vars
		# n_extra_types = type_arity-n_pattern_vars
		# type = TA {type_cons & type_arity=n_extra_types} (take n_extra_types a_types)
		# type_var_heap = set_class_arg_pattern pattern_vars (drop n_extra_types a_types) type_var_heap
		# type_var_heap = writePtr bind_dst.tv_info_ptr (TVI_Type type) type_var_heap
		= set_class_args_types type_vars types type_var_heap
set_class_args_types (ClassArgPattern bind_dst pattern_vars type_vars) [type=:TAS type_cons=:{type_arity} a_types strictness:types] type_var_heap
	#! n_pattern_vars = length pattern_vars
	| type_arity==n_pattern_vars
		# type = TAS {type_cons & type_arity=0} [] NotStrict
		# type_var_heap = set_class_arg_pattern pattern_vars a_types type_var_heap
		# type_var_heap = writePtr bind_dst.tv_info_ptr (TVI_Type type) type_var_heap
		= set_class_args_types type_vars types type_var_heap
	| type_arity>n_pattern_vars
		# n_extra_types = type_arity-n_pattern_vars
		# type = TAS {type_cons & type_arity=n_extra_types} (take n_extra_types a_types) (remove_after_n n_extra_types strictness)
		# type_var_heap = set_class_arg_pattern pattern_vars (drop n_extra_types a_types) type_var_heap
		# type_var_heap = writePtr bind_dst.tv_info_ptr (TVI_Type type) type_var_heap
		= set_class_args_types type_vars types type_var_heap
set_class_args_types (ClassArgPattern bind_dst pattern_vars type_vars) [type=:atype1 --> atype2:types] type_var_heap
	#! n_pattern_vars = length pattern_vars
	| n_pattern_vars==2
		# type = TArrow
		# type_var_heap = set_class_arg_pattern pattern_vars [atype1,atype2] type_var_heap
		# type_var_heap = writePtr bind_dst.tv_info_ptr (TVI_Type type) type_var_heap
		= set_class_args_types type_vars types type_var_heap
	| n_pattern_vars==1
		# type = TArrow1 atype1
		# type_var_heap = set_class_arg_pattern pattern_vars [atype2] type_var_heap
		# type_var_heap = writePtr bind_dst.tv_info_ptr (TVI_Type type) type_var_heap
		= set_class_args_types type_vars types type_var_heap
set_class_args_types (ClassArgPattern bind_dst pattern_vars type_vars) [type=:TArrow1 atype:types] type_var_heap
	#! n_pattern_vars = length pattern_vars
	| n_pattern_vars==1
		# type = TArrow
		# type_var_heap = set_class_arg_pattern pattern_vars [atype] type_var_heap
		# type_var_heap = writePtr bind_dst.tv_info_ptr (TVI_Type type) type_var_heap
		= set_class_args_types type_vars types type_var_heap
set_class_args_types (ClassArgPattern bind_dst pattern_vars type_vars) [TempCV tv_number:@: atypes:types] type_var_heap
	#! n_pattern_vars = length pattern_vars
	| n_pattern_vars==length atypes
		# type_var_heap = set_class_arg_pattern pattern_vars atypes type_var_heap
		# type_var_heap = writePtr bind_dst.tv_info_ptr (TVI_Type (TempV tv_number)) type_var_heap
		= set_class_args_types type_vars types type_var_heap
set_class_args_types (ClassArgPatternSameTypeVar pattern_vars type_vars) [type=:TA type_cons=:{type_arity} a_types:types] type_var_heap
	#! n_pattern_vars = length pattern_vars
	| type_arity==n_pattern_vars
		# type_var_heap = set_class_arg_pattern pattern_vars a_types type_var_heap
		= set_class_args_types type_vars types type_var_heap
	| type_arity>n_pattern_vars
		# n_extra_types = type_arity-n_pattern_vars
		# type_var_heap = set_class_arg_pattern pattern_vars (drop n_extra_types a_types) type_var_heap
		= set_class_args_types type_vars types type_var_heap
set_class_args_types (ClassArgPatternSameTypeVar pattern_vars type_vars) [type=:TAS type_cons=:{type_arity} a_types strictness:types] type_var_heap
	#! n_pattern_vars = length pattern_vars
	| type_arity==n_pattern_vars
		# type_var_heap = set_class_arg_pattern pattern_vars a_types type_var_heap
		= set_class_args_types type_vars types type_var_heap
	| type_arity>n_pattern_vars
		# n_extra_types = type_arity-n_pattern_vars
		# type_var_heap = set_class_arg_pattern pattern_vars (drop n_extra_types a_types) type_var_heap
		= set_class_args_types type_vars types type_var_heap
set_class_args_types (ClassArgPatternSameTypeVar pattern_vars type_vars) [type=:atype1 --> atype2:types] type_var_heap
	#! n_pattern_vars = length pattern_vars
	| n_pattern_vars==2
		# type_var_heap = set_class_arg_pattern pattern_vars [atype1,atype2] type_var_heap
		= set_class_args_types type_vars types type_var_heap
	| n_pattern_vars==1
		# type_var_heap = set_class_arg_pattern pattern_vars [atype2] type_var_heap
		= set_class_args_types type_vars types type_var_heap
set_class_args_types (ClassArgPatternSameTypeVar pattern_vars type_vars) [type=:TArrow1 atype:types] type_var_heap
	#! n_pattern_vars = length pattern_vars
	| n_pattern_vars==1
		# type_var_heap = set_class_arg_pattern pattern_vars [atype] type_var_heap
		= set_class_args_types type_vars types type_var_heap
set_class_args_types (ClassArgPatternSameTypeVar pattern_vars type_vars) [TempCV tv_number:@: atypes:types] type_var_heap
	#! n_pattern_vars = length pattern_vars
	| n_pattern_vars==length atypes
		# type_var_heap = set_class_arg_pattern pattern_vars atypes type_var_heap
		= set_class_args_types type_vars types type_var_heap
set_class_args_types NoClassArgs _ type_var_heap
	= type_var_heap

set_class_arg_pattern :: ![ATypeVar] ![AType] !*TypeVarHeap -> *TypeVarHeap
set_class_arg_pattern [{atv_variable={tv_info_ptr}}:pattern_vars] [{at_type}:a_types] type_var_heap
	# type_var_heap = writePtr tv_info_ptr (TVI_Type at_type) type_var_heap
	= set_class_arg_pattern pattern_vars a_types type_var_heap
set_class_arg_pattern [] [] type_var_heap
	= type_var_heap

equivalent :: !SymbolType !TempSymbolType !{#CommonDefs} !*AttributeEnv !*TypeHeaps -> (!Bool, !*AttributeEnv, !*TypeHeaps)
equivalent {st_args,st_result,st_context,st_attr_env} {tst_args,tst_result,tst_context,tst_attr_env,tst_lifted} defs attr_env heaps
	# nr_of_lifted_contexts = length st_context - length tst_context
	# (ok, heaps) = equiv (drop tst_lifted st_args,st_result) (drop tst_lifted tst_args,tst_result) heaps
	| ok
		# (ok, heaps) = equivalent_list_of_contexts (drop nr_of_lifted_contexts st_context) tst_context defs heaps
		| ok
			# (ok, attr_env, attr_var_heap) = equivalent_environments st_attr_env (fill_environment tst_attr_env attr_env) heaps.th_attrs
			= (ok, clear_environment tst_attr_env attr_env, { heaps & th_attrs = attr_var_heap })
			= (False, attr_env, heaps)
		= (False, attr_env, heaps)
where
	equivalent_list_of_contexts [] contexts defs heaps
		= (True, heaps)
	equivalent_list_of_contexts [tc : tcs] contexts defs heaps 
		# (ok, heaps) = contains_context tc contexts defs heaps
		| ok
			= equivalent_list_of_contexts tcs contexts defs heaps 
			= (False, heaps)

	contains_context tc1 [tc2 : tcs] defs heaps
		# (ok, heaps) = equivalent_contexts tc1 tc2 defs heaps
		| ok
			= (True, heaps)
			= contains_context tc1 tcs defs heaps
	contains_context tc1 [] defs heaps
		= (False, heaps)
	
	equivalent_contexts tc1=:{tc_class=TCClass class1, tc_types=types1} {tc_class=TCClass class2, tc_types=types2} defs heaps
		| class1 == class2
			= equiv types1 types2 heaps
		# {glob_object={ds_index},glob_module} = class2
		#! class_def = defs.[glob_module].com_class_defs.[ds_index]
		# {class_context,class_args} = class_def
		| class_context=:[]
			= (False, heaps)
		# th_vars = set_class_args_types class_args types2 heaps.th_vars
		= equivalent_superclasses class_context tc1 defs { heaps & th_vars = th_vars }
	where	
		equivalent_superclasses [] tc defs heaps
			= (False, heaps)
		equivalent_superclasses [super_tc=:{tc_types} : tcs] tc defs heaps=:{th_vars}
			# (tc_types, th_vars) = retrieve_types tc_types th_vars
			  (ok, heaps) = equivalent_contexts { super_tc & tc_types = tc_types } tc defs { heaps & th_vars = th_vars }
			| ok
				= (True, heaps)
				= equivalent_superclasses tcs tc defs heaps
		where
			retrieve_types [TV {tv_info_ptr} : types] type_var_heap
				#! (tv_info, type_var_heap) = readPtr tv_info_ptr type_var_heap
				#  (TVI_Type type) = tv_info
				#! (types, type_var_heap) = retrieve_types types type_var_heap
				= ([type : types], type_var_heap)
			retrieve_types [type : types] type_var_heap
				#! (types, type_var_heap) = retrieve_types types type_var_heap
				= ([type : types], type_var_heap)
			retrieve_types [] type_var_heap
				= ([], type_var_heap)
	equivalent_contexts tc1=:{tc_class=TCGeneric {gtc_class=class1}} tc2=:{tc_class=TCGeneric {gtc_class=class2}} defs heaps
		= equivalent_contexts {tc1 & tc_class = TCClass class1} {tc2 & tc_class = TCClass class2} defs heaps
	equivalent_contexts tc1=:{tc_class=TCGeneric {gtc_class=class1}} tc2 defs heaps
		= equivalent_contexts {tc1 & tc_class = TCClass class1} tc2 defs heaps
	equivalent_contexts tc1 tc2=:{tc_class=TCGeneric {gtc_class=class2}} defs heaps
		= equivalent_contexts tc1 {tc2 & tc_class = TCClass class2} defs heaps

	fill_environment :: ![AttrCoercion] !*{! TypeAttribute} -> *{! TypeAttribute}
	fill_environment [] attr_env
		= attr_env
	fill_environment [{ac_demanded,ac_offered} : coercions ] attr_env
		#  (offered, attr_env) = attr_env![ac_demanded]
		=  fill_environment coercions { attr_env & [ac_demanded] = TA_List ac_offered offered }

	clear_environment :: ![AttrCoercion] !*{! TypeAttribute} -> *{! TypeAttribute}
	clear_environment [] attr_env
		= attr_env
	clear_environment [{ac_demanded,ac_offered} : coercions ] attr_env
		= clear_environment coercions { attr_env & [ac_demanded] = TA_None }
	
	equivalent_environments inequalities attr_env attr_heap
		= foldSt equivalent_inequality inequalities (True, attr_env, attr_heap)
/*
	equivalent_environments [] attr_env attr_heap
		= (True, attr_env, attr_heap)
	equivalent_environments [{ai_demanded,ai_offered} : coercions ] attr_env attr_heap
		# (AVI_Forward demanded_var_number, attr_heap) = readPtr ai_demanded.av_info_ptr attr_heap
		  (AVI_Forward offered_var_number, attr_heap) = readPtr ai_offered.av_info_ptr attr_heap
		# (offered_of_demanded, attr_env) = attr_env![demanded_var_number]
		  attr_env = { attr_env & [demanded_var_number] = TA_Locked offered_of_demanded }
		# (succ, locked_attributes, attr_env) = contains_coercion offered_var_number offered_of_demanded [demanded_var_number] attr_env
		  attr_env = foldSt unlock_attribute locked_attributes attr_env
		| succ
			= equivalent_environments coercions attr_env attr_heap
			= (False, attr_env, attr_heap)
*/
	equivalent_inequality {ai_demanded,ai_offered} (equiv, attr_env, attr_heap)
		| equiv
			# (dem_forward, attr_heap) = readPtr ai_demanded.av_info_ptr attr_heap
			= case dem_forward of
				AVI_Forward demanded_var_number
					# (off_forward, attr_heap) = readPtr ai_offered.av_info_ptr attr_heap
					-> case off_forward of
						AVI_Forward offered_var_number
							# (offered_of_demanded, attr_env) = attr_env![demanded_var_number]
							  attr_env & [demanded_var_number] = TA_Locked offered_of_demanded
							  (succ, locked_attributes, attr_env) = contains_coercion offered_var_number offered_of_demanded [demanded_var_number] attr_env
							  attr_env = foldSt unlock_attribute locked_attributes attr_env
							-> (succ, attr_env, attr_heap)
						_
							-> (True, attr_env, attr_heap)
				_
					-> (True, attr_env, attr_heap)
			= (False, attr_env, attr_heap)			

//	contains_coercion :: !Int !TypeAttribute ![Int] !u:{! TypeAttribute} -> (!Bool, ![Int], !u:{!TypeAttribute})
	contains_coercion offered TA_None locked_attributes attr_env
		= (False, locked_attributes, attr_env)
	contains_coercion offered (TA_List this_offered next_offered) locked_attributes attr_env
		| offered == this_offered
			= (True, locked_attributes, attr_env)
		# (succ, locked_attributes, attr_env) = contains_coercion offered next_offered locked_attributes attr_env
		| succ
			= (True, locked_attributes, attr_env)
		# (offered_of_offered, attr_env) = attr_env![this_offered]
		| is_locked offered_of_offered
			= (False, locked_attributes, attr_env)
			= contains_coercion offered offered_of_offered [this_offered : locked_attributes] { attr_env & [this_offered] = TA_Locked offered_of_offered }
	contains_coercion offered (TA_Locked _) locked_attributes attr_env
		= (False, locked_attributes, attr_env)
	
	unlock_attribute attr_number attr_env
		# (TA_Locked attr, attr_env) = attr_env![attr_number]
		= { attr_env & [attr_number] = attr }
	
	is_locked (TA_Locked _) = True
	is_locked _ 			= False
	
:: Format =
	{	form_properties 	:: !BITVECT
	,	form_attr_position	:: Optional ([#Int!], Coercions)
	}

cNoProperties		:== 0
cAttributed			:== 1
cAnnotated			:== 2
cMarkAttribute		:== 4
cWriteUnderscoreforTE :== 128

cBrackets			:== 8
cCommaSeparator		:== 16
cArrowSeparator		:== 32
cAndSeparator		:== 64

checkProperty	form property	:== not (form.form_properties bitand property == 0)
setProperty		form property	:== {form & form_properties = form.form_properties bitor property}
clearProperty	form property	:== {form & form_properties = form.form_properties bitand (bitnot property)}

(<::) infixl :: !*File !(!Format, !a, !Optional TypeVarBeautifulizer) -> *File | writeType a
(<::) file (format, a, opt_beautifulizer)
	# (file, _) = writeType file opt_beautifulizer (format, a)
	= file
	
class writeType a :: !*File !(Optional TypeVarBeautifulizer) !(!Format, !a) -> (!*File, !Optional TypeVarBeautifulizer)

instance writeType AttributeVar
where
	writeType file No (_, av)
		= (file <<< av, No)
	writeType file (Yes beautifulizer) (_, av)
		= writeBeautifulAttrVar file beautifulizer (TA_Var av)

:: SAType = {s_annotation::!Annotation,s_type::!AType}

add_strictness_annotations :: [AType] Int StrictnessList -> [SAType]
add_strictness_annotations [arg:args] strictness_index strictness
	# annotation=arg_strictness_annotation strictness_index strictness
	# args=add_strictness_annotations args (strictness_index+1) strictness
	= [{s_annotation=annotation,s_type=arg}:args]
add_strictness_annotations [] strictness_index strictness
	= []

instance writeType SymbolType
where
	writeType file opt_beautifulizer (form, {st_args, st_args_strictness,st_arity, st_result, st_context, st_attr_env})
		# file_opt_beautifulizer
				= case st_arity of
					0
						-> writeType file opt_beautifulizer (bracket_arrow_type st_result.at_type form, st_result)
							with
								bracket_arrow_type (_ --> _) form
									=	setProperty form cBrackets
								bracket_arrow_type _ form
									=	form
					_
 						# (file, opt_beautifulizer)
//								= writeType file opt_beautifulizer (form, st_args)
								= write_arguments file opt_beautifulizer form st_args
							with
								write_arguments file opt_beautifulizer form st_args
									| checkProperty form cAnnotated
										= writeType file opt_beautifulizer (form, add_strictness_annotations st_args 0 st_args_strictness)
										= writeType file opt_beautifulizer (form, st_args)								
						-> writeType (file <<< " -> ") opt_beautifulizer (form, st_result)
		  (file, opt_beautifulizer)
				= show_context form st_context file_opt_beautifulizer
		= case isEmpty st_attr_env || not (checkProperty form cAttributed) of
			True
				-> (file, opt_beautifulizer)
			False
				# (file, opt_beautifulizer)
					= writeType (file <<< ", [") opt_beautifulizer 
									(setProperty form cCommaSeparator, grouped (hd st_attr_env).ai_demanded [] st_attr_env)
				-> (file <<< ']', opt_beautifulizer)
	where
		// grouped takes care that inequalities like [a<=c, b<=c] are printed like [a b <= c]
		grouped group_var accu []
			= [{ ig_offered = accu, ig_demanded = group_var}]
		grouped group_var accu [{ai_offered, ai_demanded}:ineqs]
			| group_var==ai_demanded
				= grouped group_var [ai_offered:accu] ineqs
			=[{ ig_offered = accu, ig_demanded = group_var}: grouped ai_demanded [ai_offered] ineqs]

show_context form [] file_opt_beautifulizer
	= file_opt_beautifulizer
show_context form contexts (file, opt_beautifulizer)
	= writeType (file <<< " | ") opt_beautifulizer (setProperty form cAndSeparator, contexts)
			
:: InequalityGroup =
	{	ig_offered	:: ![AttributeVar] 
	,	ig_demanded	:: !AttributeVar
	}

instance writeType InequalityGroup
where
	writeType file opt_beautifulizer (form, {ig_offered,ig_demanded})
		# (file, opt_beautifulizer)
				= writeType file opt_beautifulizer (form, ig_offered)
		= writeType (file <<< " <= ") opt_beautifulizer (form, ig_demanded)

instance writeType TypeContext
where
	//writeType file opt_beautifulizer (form, {tc_class={glob_object={ds_ident}}, tc_types})
	//	= writeType (file <<< ds_ident <<< ' ') opt_beautifulizer (form, tc_types)
	writeType file opt_beautifulizer (form, {tc_class, tc_types})
		# file = write_tc_class tc_class file
		= writeType (file <<< ' ') opt_beautifulizer (form, tc_types)
	where
		write_tc_class (TCClass {glob_object={ds_ident}}) file
			= file <<< ds_ident
		write_tc_class (TCGeneric {gtc_class={glob_object={ds_ident={id_name}}},gtc_kind}) file
			= write_generic_class (size id_name-1) id_name gtc_kind
		where
			write_generic_class i class_name kind
				| i>0
					| class_name.[i]<>'_'
						= write_generic_class (i-1) class_name kind
						= file <<< (class_name % (0,i-1)) <<< "{|" <<< gtc_kind <<< "|}"
					= file <<< class_name

instance writeType SAType
where
	writeType file opt_beautifulizer (form, {s_annotation, s_type})
		= writeType (file <<< s_annotation) opt_beautifulizer (form,s_type)

instance writeType AType
where
	writeType file opt_beautifulizer (form, {at_attribute, at_type})
			= show_attributed_type file opt_beautifulizer form at_attribute at_type
	where
		show_attributed_type file opt_beautifulizer form TA_Multi type
			| checkProperty form cMarkAttribute
				# (file, opt_beautifulizer)
					= show_marked_attribute file opt_beautifulizer (form, TA_Multi)
				= writeType file opt_beautifulizer (form, type)
				= writeType file opt_beautifulizer (form, type)
		show_attributed_type file opt_beautifulizer form TA_None type
			| checkProperty form cMarkAttribute
				# (file, opt_beautifulizer)
					= show_marked_attribute file opt_beautifulizer (form, TA_None)
				= writeType file opt_beautifulizer (form, type)
				= writeType file opt_beautifulizer (form, type)
		show_attributed_type file opt_beautifulizer form attr type
			| checkProperty form cAttributed
				# (file, opt_beautifulizer)
					= writeType file opt_beautifulizer (form, attr)
				= writeType file opt_beautifulizer (setProperty form cBrackets, type)
			| checkProperty form cMarkAttribute
				# (file, opt_beautifulizer)
					= show_marked_attribute file opt_beautifulizer (form, attr)
				= writeType file opt_beautifulizer (setProperty form cBrackets, type)
				= writeType file opt_beautifulizer (form, type)

		show_marked_attribute file opt_beautifulizer (form=:{form_attr_position = Yes (positions, coercions)}, attr)
			| positions=:[#!]
				= show_attribute coercions (file <<< "^ ") opt_beautifulizer (form, attr)
				= show_attribute coercions file opt_beautifulizer (form, attr)

		show_attribute coercions file opt_beautifulizer (form, ta=:(TA_TempVar av_number)) 
			| isUniqueAttribute av_number coercions
				= writeType file opt_beautifulizer (form, TA_Unique)
			| isNonUniqueAttribute av_number coercions
				= writeType file opt_beautifulizer (form, TA_Multi)
			= writeType file opt_beautifulizer (form, ta)
		show_attribute coercions file opt_beautifulizer (form, ta)
			= writeType file opt_beautifulizer (form, ta)

instance writeType TypeAttribute
  where
	writeType file (Yes beautifulizer) (form, ta=:TA_Var _)
		= writeBeautifulAttrVarAndColon file beautifulizer ta
	writeType file (Yes beautifulizer) (form, TA_RootVar av)
		= writeBeautifulAttrVarAndColon file beautifulizer (TA_Var av)
	writeType file (Yes beautifulizer) (form, ta=:TA_TempVar _)
		= writeBeautifulAttrVarAndColon file beautifulizer ta
	writeType file yes_beautifulizer=:(Yes _) (form, TA_Multi)
		= (file, yes_beautifulizer)
	writeType file opt_beautifulizer (_, ta)
		= (file <<< ta, opt_beautifulizer)

writeBeautifulAttrVarAndColon file beautifulizer ta
	# (file, yes_beautifulizer)
			= writeBeautifulAttrVar file beautifulizer ta
	= (file <<< ':', yes_beautifulizer)

instance writeType Type
where
	writeType file No (form, TV varid)
		= (file <<< varid, No)
	writeType file No (form, TempV tv_number)
		= (file  <<< 'v' <<< tv_number, No)
	writeType file opt_beautifulizer (form, TA type_symb types)
		= writeTypeTA file opt_beautifulizer form type_symb types
	writeType file opt_beautifulizer (form, TAS type_symb types strictness)
		| checkProperty form cAnnotated
			= writeTypeTA file opt_beautifulizer form type_symb (add_strictness_annotations types 0 strictness)
			= writeTypeTA file opt_beautifulizer form type_symb types
	writeType file opt_beautifulizer (form, arg_type --> res_type)
		| checkProperty form cBrackets
			= writeWithinBrackets "(" ")" file opt_beautifulizer
									(setProperty form cArrowSeparator, [arg_type, res_type])
			= writeType file opt_beautifulizer (setProperty form (cBrackets bitor cArrowSeparator), [arg_type, res_type])
	writeType file opt_beautifulizer (form, type :@: types)
		| checkProperty form cBrackets
			# (file, opt_beautifulizer)
					= writeType (file <<< '(') opt_beautifulizer (form, type)
			  (file, opt_beautifulizer)
					= writeType (file <<< ' ') opt_beautifulizer (form, types)
			= (file <<< ')', opt_beautifulizer)
			# (file, opt_beautifulizer)
					= writeType file opt_beautifulizer (form, type)
			  (file, opt_beautifulizer)
					= writeType (file <<< ' ') opt_beautifulizer (setProperty form cBrackets, types)
			= (file, opt_beautifulizer)
	writeType file opt_beautifulizer (form, TB tb)
		= (file <<< tb, opt_beautifulizer)
	writeType file (Yes beautifulizer) (_, type_var=:TV _)
		= writeBeautifulTypeVar file beautifulizer type_var
	writeType file (Yes beautifulizer) (_, GTV tv)
		= writeBeautifulTypeVar file beautifulizer (TV tv)
	writeType file (Yes beautifulizer) (_, type_var=:TempV _)
		= writeBeautifulTypeVar file beautifulizer type_var
	writeType file opt_beautifulizer (form, TArrow)
		= (file <<< "(->)", opt_beautifulizer)	
	writeType file opt_beautifulizer (form, TArrow1 t)
		# file = file <<< "((->)" 
		# (file, opt_opt_beautifulizer) = writeType file opt_beautifulizer (form, t)
		# file = file <<< ")" 
		= (file, opt_beautifulizer)	
	writeType file opt_beautifulizer (form, TFA vars type)
		 # (file, opt_beautifulizer) = writeType (file <<< "(A.") opt_beautifulizer (form, vars)
		 # (file, opt_beautifulizer) = writeType (file <<< ":") opt_beautifulizer (clearProperty form cBrackets, type)
		 = (file <<< ")", opt_beautifulizer)
	writeType file opt_beautifulizer (form, TFAC vars type contexts)
		 # (file, opt_beautifulizer) = writeType (file <<< "(A.") opt_beautifulizer (form, vars)
		   (file, opt_beautifulizer) = writeType (file <<< ":") opt_beautifulizer (clearProperty form cBrackets, type)
		   (file, opt_beautifulizer) = show_context form contexts (file,opt_beautifulizer)
		 = (file <<< ")", opt_beautifulizer)
	writeType file opt_beautifulizer (form, TempQV tv_number)
		= (file  <<< "E." <<< tv_number <<< ' ', opt_beautifulizer)
	writeType file opt_beautifulizer (form, TempQDV tv_number)
		= (file  <<< "E." <<< tv_number <<< ' ', opt_beautifulizer)
	writeType file opt_beautifulizer (form, TAll)
		= (file <<< "_", opt_beautifulizer)
	writeType file opt_beautifulizer (form=:{form_properties}, TE)
		| form_properties bitand cWriteUnderscoreforTE<>0
			= (file <<< "_", opt_beautifulizer)
			= (file <<< "__", opt_beautifulizer)
	writeType file _ (form, type)
		= abort ("<:: (Type) (typesupport.icl)" ---> type)

writeTypeTA :: !*File !(Optional TypeVarBeautifulizer) !Format !TypeSymbIdent !a -> (!*File, !Optional TypeVarBeautifulizer) | writeType a
writeTypeTA	file opt_beautifulizer form {type_ident,type_index={glob_module,glob_object},type_arity} types
	| glob_module == cPredefinedModuleIndex
		| type_arity == 0
			| glob_object==PD_StringTypeIndex
				= (file <<< "String", opt_beautifulizer)
			| glob_object==PD_UnitTypeIndex
				= (file <<< "()", opt_beautifulizer)
			| glob_object==PD_LazyArrayTypeIndex
				= (file <<< "{}", opt_beautifulizer)
			| glob_object==PD_StrictArrayTypeIndex
				= (file <<< "{!}", opt_beautifulizer)
			| glob_object==PD_UnboxedArrayTypeIndex
				= (file <<< "{#}", opt_beautifulizer)
			| glob_object==PD_PackedArrayTypeIndex
				= (file <<< "{32#}", opt_beautifulizer)
			| glob_object==PD_LazyArrayP2TypeIndex
				= (file <<< "{:}", opt_beautifulizer)
			| glob_object==PD_StrictArrayP2TypeIndex
				= (file <<< "{!:}", opt_beautifulizer)
			| glob_object==PD_UnboxedArrayP2TypeIndex
				= (file <<< "{#:}", opt_beautifulizer)
			| glob_object==PD_PackedArrayP2TypeIndex
				= (file <<< "{32#:}", opt_beautifulizer)
				= (file <<< type_ident, opt_beautifulizer)
		| glob_object==PD_ListTypeIndex
			= writeWithinBrackets "[" "]" file opt_beautifulizer (setProperty form cCommaSeparator, types)
		| glob_object==PD_StrictListTypeIndex
			= writeWithinBrackets "[!" "]" file opt_beautifulizer (setProperty form cCommaSeparator, types)
		| glob_object==PD_UnboxedListTypeIndex
			= writeWithinBrackets "[#" "]" file opt_beautifulizer (setProperty form cCommaSeparator, types)
		| glob_object==PD_TailStrictListTypeIndex
			= writeWithinBrackets "[" "!]" file opt_beautifulizer (setProperty form cCommaSeparator, types)
		| glob_object==PD_StrictTailStrictListTypeIndex
			= writeWithinBrackets "[!" "!]" file opt_beautifulizer (setProperty form cCommaSeparator, types)
		| glob_object==PD_UnboxedTailStrictListTypeIndex
			= writeWithinBrackets "[#" "!]" file opt_beautifulizer (setProperty form cCommaSeparator, types)
		| glob_object==PD_LazyArrayTypeIndex
			= writeWithinBrackets "{" "}" file opt_beautifulizer (setProperty form cCommaSeparator, types)
		| glob_object==PD_StrictArrayTypeIndex
			= writeWithinBrackets "{!" "}" file opt_beautifulizer (setProperty form cCommaSeparator, types)
		| glob_object==PD_UnboxedArrayTypeIndex
			= writeWithinBrackets "{#" "}" file opt_beautifulizer (setProperty form cCommaSeparator, types)
		| glob_object==PD_PackedArrayTypeIndex
			= writeWithinBrackets "{32#" "}" file opt_beautifulizer (setProperty form cCommaSeparator, types)
		| glob_object==PD_LazyArrayP2TypeIndex
			= writeWithinBrackets "{" ":}" file opt_beautifulizer (setProperty form cCommaSeparator, types)
		| glob_object==PD_StrictArrayP2TypeIndex
			= writeWithinBrackets "{!" ":}" file opt_beautifulizer (setProperty form cCommaSeparator, types)
		| glob_object==PD_UnboxedArrayP2TypeIndex
			= writeWithinBrackets "{#" ":}" file opt_beautifulizer (setProperty form cCommaSeparator, types)
		| glob_object==PD_PackedArrayP2TypeIndex
			= writeWithinBrackets "{32#" ":}" file opt_beautifulizer (setProperty form cCommaSeparator, types)
		| glob_object>=PD_Arity2TupleTypeIndex && glob_object<=PD_Arity32TupleTypeIndex
			= writeWithinBrackets "(" ")" file opt_beautifulizer (setProperty form cCommaSeparator, types)
		| glob_object==PD_MaybeTypeIndex
			| checkProperty form cBrackets
				# (file, opt_beautifulizer) = writeType (file <<< "(?^ ") opt_beautifulizer (form, types)
				= (file <<< ')', opt_beautifulizer)
				= writeType (file <<< "?^ ") opt_beautifulizer (setProperty form cBrackets, types)
		| glob_object==PD_StrictMaybeTypeIndex
			| checkProperty form cBrackets
				# (file, opt_beautifulizer) = writeType (file <<< "(? ") opt_beautifulizer (form, types)
				= (file <<< ')', opt_beautifulizer)
				= writeType (file <<< "? ") opt_beautifulizer (setProperty form cBrackets, types)
		| glob_object==PD_UnboxedMaybeTypeIndex
			| checkProperty form cBrackets
				# (file, opt_beautifulizer) = writeType (file <<< "(?# ") opt_beautifulizer (form, types)
				= (file <<< ')', opt_beautifulizer)
				= writeType (file <<< "?# ") opt_beautifulizer (setProperty form cBrackets, types)
		| checkProperty form cBrackets
			# (file, opt_beautifulizer)
					= writeType (file <<< '(' <<< type_ident <<< ' ') opt_beautifulizer (form, types)
			= (file <<< ')', opt_beautifulizer)
			= writeType (file <<< type_ident <<< ' ') opt_beautifulizer (setProperty form cBrackets, types)
	| type_arity == 0
		= (file <<< type_ident, opt_beautifulizer)
	| checkProperty form cBrackets
		# (file, opt_beautifulizer)
				= writeType (file <<< '(' <<< type_ident <<< ' ') opt_beautifulizer (form, types)
		= (file <<< ')', opt_beautifulizer)
		= writeType (file <<< type_ident <<< ' ') opt_beautifulizer (setProperty form cBrackets, types)

instance writeType ATypeVar
where
	writeType file beautifulizer (form, {atv_attribute,atv_variable})
		= writeType file beautifulizer (form, { at_attribute = atv_attribute, at_type = TV atv_variable })

writeWithinBrackets br_open br_close file opt_beautifulizer (form, types)
	# (file, opt_beautifulizer) 
		= writeType (file <<< br_open) opt_beautifulizer (clearProperty form cBrackets, types)
	= (file <<< br_close, opt_beautifulizer)

writeBeautifulTypeVar file beautifulizer=:{tvb_visited_type_vars, tvb_fresh_type_vars} type
	| sanity_check_failed type
		= abort "bug nr 12345 in module typesupport"
	= case assoc_list_lookup (==) type tvb_visited_type_vars of
		No
			-> (file <<< hd tvb_fresh_type_vars, 
				Yes { beautifulizer &
						tvb_visited_type_vars = [(type, hd tvb_fresh_type_vars):tvb_visited_type_vars],
						tvb_fresh_type_vars = tl tvb_fresh_type_vars })
		Yes (_, beautiful_var_name)
			-> (file <<< beautiful_var_name, Yes beautifulizer)
  where
	sanity_check_failed (TV _)		= False
	sanity_check_failed (TempV _)	= False
	sanity_check_failed _			= True
	
writeBeautifulAttrVar file beautifulizer=:{tvb_visited_attr_vars, tvb_fresh_attr_vars} attribute
	| sanity_check_failed attribute
		= abort "bug nr 123456 in module typesupport"
	= case assoc_list_lookup equal_attributes attribute tvb_visited_attr_vars of
		No
			-> (file <<< hd tvb_fresh_attr_vars, 
				Yes { beautifulizer &
						tvb_visited_attr_vars = [(attribute, hd tvb_fresh_attr_vars):tvb_visited_attr_vars],
						tvb_fresh_attr_vars = tl tvb_fresh_attr_vars })
		Yes (_, beautiful_var_name)
			-> (file <<< beautiful_var_name, Yes beautifulizer)
  where
	sanity_check_failed (TA_Var _)		= False
	sanity_check_failed (TA_TempVar _)	= False
	sanity_check_failed _				= True

	equal_attributes (TA_Var {av_info_ptr=p1}) (TA_Var {av_info_ptr=p2})
		= p1==p2
	equal_attributes (TA_TempVar i1) (TA_TempVar i2)
		= i1==i2
	equal_attributes _ _
		= False

instance writeType ConsVariable where
	writeType file No (_, cons_variable)
		= (file <<< cons_variable, No)
	writeType file yes_beautifulizer (_, cv=:(TempQCV _))
		= (file <<< cv, yes_beautifulizer)
	writeType file yes_beautifulizer (_, cv=:(TempQCDV _))
		= (file <<< cv, yes_beautifulizer)
	writeType file (Yes beautifulizer) (_, CV tv)
		= writeBeautifulTypeVar file beautifulizer (TV tv)
	writeType file (Yes beautifulizer) (_, TempCV i)
		= writeBeautifulTypeVar file beautifulizer (TempV i)
	writeType file yes_beautifulizer (_, CVE)
		= (file <<< '_', yes_beautifulizer)

assoc_list_lookup _ _ [] = No
assoc_list_lookup equal t1 [hd=:(t2, _):tl]
	| equal t1 t2
		= Yes hd
	= assoc_list_lookup equal t1 tl

cNoPosition :== -1

instance writeType [a] | writeType a
where
	writeType file opt_beautifulizer (form, types)
		= show_list 0 form types (file, opt_beautifulizer)
	where
		show_list :: !Int Format [a] !*(!*File,!Optional TypeVarBeautifulizer) -> (!*File,!Optional TypeVarBeautifulizer) | writeType a
		show_list elem_number form [type] file_opt_beautifulizer
			| checkProperty form cCommaSeparator
				= show_elem elem_number (clearProperty form cCommaSeparator) type file_opt_beautifulizer
			| checkProperty form cArrowSeparator
				= show_elem elem_number (clearProperty (clearProperty form cArrowSeparator) cBrackets) type file_opt_beautifulizer
			| checkProperty form cAndSeparator
				= show_elem elem_number (clearProperty form cAndSeparator) type file_opt_beautifulizer
				= show_elem elem_number (setProperty form cBrackets) type file_opt_beautifulizer
		show_list elem_number form [type : types] file_opt_beautifulizer
			# (elem_format, seperator)
					= if (checkProperty form cCommaSeparator) (clearProperty form cCommaSeparator, ",")
						(if (checkProperty form cArrowSeparator) (setProperty (clearProperty form cArrowSeparator) cBrackets, " -> ")
							(if (checkProperty form cAndSeparator) (clearProperty form cAndSeparator, " & ")
								(setProperty form cBrackets, " ")))
			  (file, opt_beautifulizer)
					= show_elem elem_number elem_format type file_opt_beautifulizer
			= show_list (inc elem_number) form types (file <<< seperator, opt_beautifulizer)
		show_list elem_number form [] file
			= file

		show_elem :: !Int Format a !*(!*File,!Optional TypeVarBeautifulizer) -> (!*File,!Optional TypeVarBeautifulizer) | writeType a
		show_elem elem_nr form=:{form_attr_position = No} type (file, opt_beautifulizer)
			= writeType file opt_beautifulizer (form, type)
		show_elem elem_nr form=:{form_attr_position = Yes ([#pos : positions!], coercions)} type (file, opt_beautifulizer)
			| elem_nr == pos
				= writeType file opt_beautifulizer ({form & form_attr_position = Yes (positions, coercions)}, type)
			| pos == cNoPosition
				= writeType file opt_beautifulizer (form, type)
				= writeType file opt_beautifulizer ({form & form_attr_position = Yes ([#cNoPosition!], coercions)}, type)
		show_elem elem_nr form=:{form_attr_position = Yes ([#!], coercions)} type (file, opt_beautifulizer)
			= writeType file opt_beautifulizer ({form & form_attr_position = Yes ([#cNoPosition!], coercions)}, type)

from compare_constructor import equal_constructor	

instance == Format
where
	(==) form1 form2 = equal_constructor form1 form2

instance <<< TypeContext
where
	(<<<) file co = file <<< co.tc_class <<< " <" <<< ptrToInt co.tc_var <<< '>' <<< " " <<< co.tc_types
	

instance <<< AttrCoercion
where
	(<<<) file {ac_demanded,ac_offered} = file <<< ac_demanded <<< " <= " <<< ac_offered
	
instance <<< TempSymbolType
where
	(<<<) file {tst_args, tst_result, tst_context, tst_attr_env }
		| isEmpty tst_args
			= file <<< tst_result <<< " | " <<< tst_context <<< " [" <<< tst_attr_env <<< ']'
			= file <<< tst_args <<< " -> " <<< tst_result <<< " | " <<< tst_context <<< " [" <<< tst_attr_env <<< ']'

:: TypeVarBeautifulizer =
	{	tvb_visited_type_vars 	:: ![(Type, String)]			// only TV and TempV
	,	tvb_fresh_type_vars		:: ![String]
	,	tvb_visited_attr_vars	:: ![(TypeAttribute, String)]	// only TA_Var and TA_TempVar
	,	tvb_fresh_attr_vars		:: ![String]
	}

initialTypeVarBeautifulizer :: TypeVarBeautifulizer
initialTypeVarBeautifulizer 
	= {	tvb_visited_type_vars = [], tvb_fresh_type_vars = fresh_vars 'a' 'i' 'a' (-1),
		tvb_visited_attr_vars = [], tvb_fresh_attr_vars = fresh_vars 'u' (inc 'z') 'u' (-1) }
  where
	fresh_vars min max1 ch i
		| ch==max1
			= fresh_vars min max1 min (i+1)
		= [if (i==(-1)) (toString ch) (toString ch+++toString i): fresh_vars min max1 (inc ch) i]

getImplicitAttrInequalities :: !SymbolType -> [AttrInequality]
	// retrieve those inequalities  that are implied by propagation
getImplicitAttrInequalities st=:{st_args, st_result}
	# ineqs1 = get_ineqs_of_atype_list st_args
	  ineqs2 = get_ineqs_of_atype st_result
	= uniqueBagToList (Pair ineqs1 ineqs2)
  where
	get_ineqs_of_atype :: !AType -> .Bag AttrInequality
	get_ineqs_of_atype {at_attribute=TA_Var outer_av, at_type=at_type=:TA type_symb_ident type_args}
		= get_ineqs_of_TA_with_TA_Var outer_av at_type type_symb_ident type_args
	get_ineqs_of_atype {at_attribute=TA_Var outer_av, at_type=at_type=:TAS type_symb_ident type_args _}
		= get_ineqs_of_TA_with_TA_Var outer_av at_type type_symb_ident type_args
	get_ineqs_of_atype {at_type}
		= get_ineqs_of_type at_type

	get_ineqs_of_TA_with_TA_Var outer_av at_type type_symb_ident type_args
		# ({tsp_propagation}) = type_symb_ident.type_prop
		  implicit_ineqs_1 = get_superflous_ineqs outer_av type_args tsp_propagation
		| isEmptyBag implicit_ineqs_1
			= get_ineqs_of_type at_type
		# implicit_ineqs_2 = get_ineqs_of_type at_type
		= Pair implicit_ineqs_1 implicit_ineqs_2
	  where
		get_superflous_ineqs :: !AttributeVar ![AType] !PropClassification -> .Bag AttrInequality
		get_superflous_ineqs outer_av [] tsp_propagation
			= Empty
		get_superflous_ineqs outer_av [{at_attribute}:type_args] tsp_propagation
			# other_ineqs = get_superflous_ineqs outer_av type_args (tsp_propagation>>1)
			| tsp_propagation bitand 1==0
				// the type doesn't propagate in this argument
				= other_ineqs
			= case at_attribute of
				TA_Var inner_av
					-> Pair (Single {ai_demanded=inner_av, ai_offered=outer_av}) other_ineqs
				_	-> other_ineqs

	get_ineqs_of_type (TA ts args)
		= get_ineqs_of_atype_list args
	get_ineqs_of_type (TAS ts args _)
		= get_ineqs_of_atype_list args
	get_ineqs_of_type (l --> r)
		= Pair (get_ineqs_of_atype l) (get_ineqs_of_atype r)
	get_ineqs_of_type (TArrow1 type)
		= get_ineqs_of_atype type
	get_ineqs_of_type (cv :@: args)
		= get_ineqs_of_atype_list args
	get_ineqs_of_type (TFA vars type)
		= get_ineqs_of_type type
	get_ineqs_of_type (TFAC vars type type_contexts)
		= get_ineqs_of_type type
	get_ineqs_of_type _
		= Empty

	get_ineqs_of_atype_list []
		= Empty
	get_ineqs_of_atype_list [a_type:a_types]
		= Pair (get_ineqs_of_atype a_type) (get_ineqs_of_atype_list a_types)

beautifulizeAttributes :: !SymbolType !*AttrVarHeap -> (!SymbolType, !.AttrVarHeap)
beautifulizeAttributes symbol_type th_attrs
	# (nr_of_attr_vars, rev_all_attr_vars, th_attrs)
	  		= assignNumbersToAttrVars symbol_type th_attrs
	  (attr_env_coercions, th_attrs)
	  		= addAttrEnvInequalities symbol_type.st_attr_env (emptyCoercions nr_of_attr_vars) th_attrs
	  (all_int_inequalities, th_attrs)
	  		= mapSt pointers_to_int symbol_type.st_attr_env th_attrs
	  (_, attr_env_coercions)
	  		= foldSt removeRedundancy all_int_inequalities
	  				(createArray nr_of_attr_vars False, attr_env_coercions)
	  implicit_inequalities = getImplicitAttrInequalities symbol_type
	  (implicit_int_inequalities, th_attrs)
	  		= mapSt pointers_to_int implicit_inequalities th_attrs
	  attr_env_coercions = foldSt remove_inequality implicit_int_inequalities attr_env_coercions
	  st_attr_env = coercionsToAttrEnv {el \\ el<-reverse rev_all_attr_vars } attr_env_coercions
	= anonymizeAttrVars { symbol_type & st_attr_env = st_attr_env } implicit_inequalities th_attrs
  where
	pointers_to_int {ai_offered, ai_demanded} th_attrs
		# (AVI_Attr (TA_TempVar offered), th_attrs) = readPtr ai_offered.av_info_ptr th_attrs
		  (AVI_Attr (TA_TempVar demanded), th_attrs) = readPtr ai_demanded.av_info_ptr th_attrs
  		= ({ ac_offered = offered, ac_demanded = demanded }, th_attrs)
	remove_inequality {ac_offered, ac_demanded} attr_env_coercions
		= removeInequality ac_offered ac_demanded attr_env_coercions

	coercionsToAttrEnv :: !{AttributeVar} !Coercions -> [AttrInequality]
	coercionsToAttrEnv attr_vars {coer_offered}
		= flatten [ [ {ai_offered = attr_vars.[offered], ai_demanded = attr_vars.[demanded] }
					\\ offered <- fst (flattenCoercionTree offered_tree) ]
				  \\ offered_tree<-:coer_offered & demanded<-[0..] ]

	removeRedundancy :: !AttrCoercion !(!*{#Bool}, !*Coercions) -> (!.{#Bool}, !.Coercions)
	removeRedundancy {ac_offered, ac_demanded} (visited, attr_env_coercions=:{coer_demanded})
		// all i:not visited.[i]
		# (descendants, coer_demanded)
				= accCoercionTree flattenCoercionTree ac_offered coer_demanded
		  (path_exists, (visited, coer_demanded))
		  		= searchPath (removeMember ac_demanded descendants) ac_demanded (visited, coer_demanded)
		#! size 
				= size visited
		# visited
				= { visited & [i] = False \\ i<-[0..size-1] }
		  attr_env_coercions
		  		 = { attr_env_coercions & coer_demanded = coer_demanded }
		| path_exists
			// the inequality was redundant (like the first one in [a<=c, a<=b, b<=c] 
			= (visited, removeInequality ac_offered ac_demanded attr_env_coercions)
		= (visited, attr_env_coercions)
	  where
		searchPath :: ![Int] Int !(!*{#Bool}, !{!*CoercionTree}) -> (!Bool, (!.{#Bool}, !{!.CoercionTree}))
		searchPath [] _ visited_coer_demanded
			= (False, visited_coer_demanded)
		searchPath [x:xs] goal (visited, coer_demanded)
			// not visited.[x]
			| x==goal
				= (True, (visited, coer_demanded))
			# visited
					= { visited & [x] = True }
		 	  (descendants, coer_demanded)
					= accCoercionTree flattenCoercionTree x coer_demanded
			  (xs, visited)
			 		= foldSt add_unvisited_node descendants (xs, visited)
			= searchPath xs goal (visited, coer_demanded)
			
		add_unvisited_node :: !Int !(![Int], !u:{#Bool}) -> (![Int], !u:{#Bool})
		add_unvisited_node candidate (accu, visited)
			| visited.[candidate]
				= (accu, visited)
			= ([candidate:accu], visited)

instance performOnAttrVars AttrInequality
where
	performOnAttrVars f {ai_demanded,ai_offered} st
		= f ai_demanded (f ai_offered st)

assignNumbersToAttrVars :: !SymbolType !*AttrVarHeap -> (!Int, ![AttributeVar], !.AttrVarHeap)
assignNumbersToAttrVars {st_attr_vars, st_args, st_result, st_attr_env} th_attrs
	# th_attrs = foldSt initializeToAVI_Empty st_attr_vars th_attrs
	  (nr_of_attr_vars, attr_vars, th_attrs)
			= performOnAttrVars assign_number_to_unencountered_attr_var (st_args, st_result)
	  				(0, [], th_attrs)
	| fst (foldSt hasnt_got_a_number st_attr_env (False, th_attrs))
		// to do: prevent free attributes in st_attr_env when expanding types
		= performOnAttrVars assign_number_to_unencountered_attr_var st_attr_env (nr_of_attr_vars, attr_vars, th_attrs)
	 	= (nr_of_attr_vars, attr_vars, th_attrs)
  where
	assign_number_to_unencountered_attr_var av=:{av_info_ptr} (next_number, attr_vars_accu, th_attrs)
		# (avi, th_attrs) = readPtr av_info_ptr th_attrs
		= case avi of
			AVI_Empty
				-> (next_number+1, [av:attr_vars_accu],
					writePtr av_info_ptr (AVI_Attr (TA_TempVar next_number)) th_attrs)
			_
				-> (next_number, attr_vars_accu, th_attrs)
	
	hasnt_got_a_number {ai_offered, ai_demanded} (or_of_all, th_attrs)
		# hnn1 = has_no_number ai_offered th_attrs
		  hnn2 = has_no_number ai_demanded th_attrs
		= (hnn1 || hnn2 || or_of_all, th_attrs)
		
	has_no_number {av_info_ptr} th_attrs
		= case sreadPtr av_info_ptr th_attrs of
			AVI_Empty
				-> True
			_
				-> False

//accCoercionTree :: !.(u:CoercionTree -> (.a,u:CoercionTree)) !Int !*{!u:CoercionTree} -> (!.a,!{!u:CoercionTree})
accCoercionTree f i coercion_trees
	:== acc_coercion_tree i coercion_trees
  where
	acc_coercion_tree i coercion_trees
		# (coercion_tree, coercion_trees) = coercion_trees![i]
		  (x, coercion_tree) = f coercion_tree
		= (x, {coercion_trees & [i]=coercion_tree})
	
appCoercionTree f i coercion_trees
	:== acc_coercion_tree i coercion_trees
  where
	acc_coercion_tree i coercion_trees
		# (coercion_tree, coercion_trees) = coercion_trees![i]
		= {coercion_trees & [i] = f coercion_tree}
	
flattenCoercionTree :: !u:CoercionTree -> (![Int], !u:CoercionTree)
flattenCoercionTree tree
	= flatten_ct ([], tree)
  where
	flatten_ct (accu, CT_Node i left right)
		# (accu, right) = flatten_ct (accu, right)
		  (accu, left) = flatten_ct ([i:accu], left)
		= (accu, CT_Node i left right)
	flatten_ct (accu, _)
		= (accu, CT_Empty)

anonymizeAttrVars :: !SymbolType ![AttrInequality] !*AttrVarHeap -> (!SymbolType, !.AttrVarHeap)
anonymizeAttrVars st=:{st_attr_vars, st_args, st_result, st_attr_env} implicit_inequalities th_attrs
	# th_attrs = countAttrVars st th_attrs
	  th_attrs = foldSt markUsedAttrVars st_attr_env th_attrs
	  th_attrs = foldSt mark_once_occurring_implicit_attr_var implicit_inequalities th_attrs
	  (st_args, th_attrs) = mapSt anonymize_atype st_args th_attrs
	  (st_result, th_attrs) = anonymize_atype st_result th_attrs
	= ({ st & st_args = st_args, st_result = st_result }, th_attrs)
  where
	anonymize_atype :: !AType !*AttrVarHeap -> (!AType,!*AttrVarHeap)
	anonymize_atype atype=:{at_attribute=TA_Var {av_info_ptr}, at_type} th_attrs
		# (at_type, th_attrs)	= anonymize_type at_type th_attrs
		  (avi, th_attrs)		= readPtr av_info_ptr th_attrs
		= case avi of
			AVI_CountMany
				-> ({ atype & at_type = at_type }, th_attrs)
			AVI_CountZero
				-> ({ atype & at_type = at_type, at_attribute = TA_Anonymous }, th_attrs)
			AVI_CountOne
				-> ({ atype & at_type = at_type, at_attribute = TA_Anonymous }, th_attrs)
			AVI_CountVar _
				-> ({ atype & at_type = at_type, at_attribute = TA_Anonymous }, th_attrs)
			AVI_Attr TA_None
				-> ({ atype & at_type = at_type, at_attribute = TA_None }, th_attrs)
			_
				-> ({ atype & at_type = at_type }, th_attrs)
	anonymize_atype atype=:{at_type} th_attrs
		# (at_type, th_attrs) = anonymize_type at_type th_attrs
		= ({ atype & at_type = at_type }, th_attrs)

	anonymize_type :: !Type !*AttrVarHeap -> (!Type,!*AttrVarHeap)
	anonymize_type (TA tsi args) th_attrs
		# (args, th_attrs) = mapSt anonymize_atype args th_attrs
		= (TA tsi args, th_attrs)
	anonymize_type (TAS tsi args strictness) th_attrs
		# (args, th_attrs) = mapSt anonymize_atype args th_attrs
		= (TAS tsi args strictness, th_attrs)
	anonymize_type (l --> r) th_attrs
		# (l, th_attrs) = anonymize_atype l th_attrs
		  (r, th_attrs) = anonymize_atype r th_attrs
		= (l --> r, th_attrs)
	anonymize_type (TArrow1 type) th_attrs
		# (type, th_attrs) = anonymize_atype type th_attrs
		= (TArrow1 type, th_attrs)
	anonymize_type (cv :@: args) th_attrs
		# (args, th_attrs) = mapSt anonymize_atype args th_attrs
		= (cv :@: args, th_attrs)
	anonymize_type (TFA vars type) th_attrs
		# (type, th_attrs) = anonymize_type type th_attrs
		= (TFA vars type, th_attrs)
	anonymize_type (TFAC vars type type_contexts) th_attrs
		# (type, th_attrs) = anonymize_type type th_attrs
		= (TFAC vars type type_contexts, th_attrs)
	anonymize_type x th_attrs
		= (x, th_attrs)

	countAttrVars :: !SymbolType !*AttrVarHeap -> .AttrVarHeap
	// for all attribute variables: set the attrVarInfo to (AVI_count c) where c is the number of
	// occurences in of that attribute variable in the SymbolType (excluding inequalities)
	countAttrVars {st_attr_vars, st_args, st_result} th_attrs
		# th_attrs = foldSt (\av=:{av_info_ptr} th_attrs -> writePtr av_info_ptr AVI_CountZero th_attrs)
						st_attr_vars th_attrs
		= foldSt count_attr_vars_of_atype st_args (count_attr_vars_of_atype st_result th_attrs)
	where
		count_attr_vars_of_atype :: !AType !*AttrVarHeap -> *AttrVarHeap
		count_attr_vars_of_atype {at_attribute=TA_Var {av_info_ptr}, at_type} th_attrs
			# (av_info,th_attrs) = readPtr av_info_ptr th_attrs
			= case av_info of
				AVI_CountZero
					-> case at_type of
						TV {tv_info_ptr}
							-> count_attr_vars_of_type at_type (writePtr av_info_ptr (AVI_CountVar tv_info_ptr) th_attrs)
						GTV {tv_info_ptr}
							-> count_attr_vars_of_type at_type (writePtr av_info_ptr (AVI_CountVar tv_info_ptr) th_attrs)
						_
							-> count_attr_vars_of_type at_type (writePtr av_info_ptr AVI_CountOne th_attrs)
				AVI_CountVar previous_tv_info_ptr
					-> case at_type of
						TV {tv_info_ptr}
							| tv_info_ptr==previous_tv_info_ptr
								-> count_attr_vars_of_type at_type (writePtr av_info_ptr (AVI_CountVar tv_info_ptr) th_attrs)
						GTV {tv_info_ptr}
							| tv_info_ptr==previous_tv_info_ptr
								-> count_attr_vars_of_type at_type (writePtr av_info_ptr (AVI_CountVar tv_info_ptr) th_attrs)
						_
							-> count_attr_vars_of_type at_type (writePtr av_info_ptr AVI_CountMany th_attrs)
				AVI_CountOne
					-> count_attr_vars_of_type at_type (writePtr av_info_ptr AVI_CountMany th_attrs)
				AVI_CountMany
					-> count_attr_vars_of_type at_type th_attrs
		count_attr_vars_of_atype {at_type} th_attrs
			= count_attr_vars_of_type at_type th_attrs

		count_attr_vars_of_type (TA _ args) th_attrs
			= foldSt count_attr_vars_of_atype args th_attrs
		count_attr_vars_of_type (TAS _ args _) th_attrs
			= foldSt count_attr_vars_of_atype args th_attrs
		count_attr_vars_of_type (l --> r) th_attrs
			= count_attr_vars_of_atype l (count_attr_vars_of_atype r th_attrs)
		count_attr_vars_of_type (TArrow1 t) th_attrs
			= count_attr_vars_of_atype t th_attrs
		count_attr_vars_of_type (_ :@: args) th_attrs
			= foldSt count_attr_vars_of_atype args th_attrs
		count_attr_vars_of_type (TFA _ type) th_attrs
			= count_attr_vars_of_type type th_attrs
		count_attr_vars_of_type (TFAC _ type _) th_attrs
			= count_attr_vars_of_type type th_attrs
		count_attr_vars_of_type _ th_attrs
			= th_attrs

	markUsedAttrVars {ai_offered, ai_demanded} th_attrs
		= writePtr ai_offered.av_info_ptr (AVI_Forward 0)
			(writePtr ai_demanded.av_info_ptr (AVI_Forward 0) th_attrs)
		// misuse AVI_Forward to indicate that this attribute variable is referenced in
		// the attribute inequalities

	mark_once_occurring_implicit_attr_var {ai_offered={av_info_ptr}} th_attrs
		# (avi, th_attrs) = readPtr av_info_ptr th_attrs
		= case avi of
			AVI_CountOne
				-> writePtr av_info_ptr (AVI_Attr TA_None) th_attrs
			_
				-> th_attrs
				
removeInequality :: !Int !Int !*Coercions -> .Coercions
removeInequality offered demanded attr_env_coercions=:{coer_offered, coer_demanded}
	# coer_offered = appCoercionTree (removeNode offered) demanded coer_offered
	  coer_demanded = appCoercionTree (removeNode demanded) offered coer_demanded
	= { attr_env_coercions & coer_demanded = coer_demanded, coer_offered = coer_offered }

removeNode :: !Int !*CoercionTree -> .CoercionTree
removeNode i1 (CT_Node i2 left right)
	| i1<i2
		= CT_Node i2 (removeNode i1 left) right
	| i1>i2
		= CT_Node i2 left (removeNode i1 right)
	= rightInsert left right
  where
	rightInsert :: !*CoercionTree !*CoercionTree -> .CoercionTree
	rightInsert CT_Empty right
		= right
	rightInsert (CT_Node i left right2) right1
		= CT_Node i left (rightInsert right2 right1)
removeNode i1 CT_Empty
	= CT_Empty

emptyCoercions :: !Int -> .Coercions
emptyCoercions nr_of_attr_vars
		= { coer_demanded = create_a_unique_array nr_of_attr_vars,
			coer_offered = create_a_unique_array nr_of_attr_vars }
	  where
		create_a_unique_array :: !Int -> .{!.CoercionTree}
		create_a_unique_array n
			= { CT_Empty \\ i <- [1..n] }

addAttrEnvInequalities :: ![AttrInequality] !*Coercions !u:AttrVarHeap -> (!.Coercions, !u:AttrVarHeap)
addAttrEnvInequalities st_attr_env coercions th_attrs
	= foldSt add_attr_env_inequality st_attr_env (coercions, th_attrs)
  where
	add_attr_env_inequality {ai_offered, ai_demanded} (coercions, th_attrs)
		# (AVI_Attr (TA_TempVar offered), th_attrs) = readPtr ai_offered.av_info_ptr th_attrs
		  (AVI_Attr (TA_TempVar demanded), th_attrs) = readPtr ai_demanded.av_info_ptr th_attrs
  		= (newInequality offered demanded coercions, th_attrs)

replace_external_variables :: ![AType] ![TypeContext] ![AttrInequality] ![!P TypeVarInfoPtr TypeVarInfoPtr!] ![!P AttrVarInfoPtr AttrVarInfoPtr!]
								![TypeVar] ![AttributeVar] !*TypeHeaps
						  -> (![AType],![TypeContext],![AttrInequality],!*TypeHeaps)
replace_external_variables lifted_args lifted_contexts lifted_attr_env new_and_old_external_type_vars new_and_old_external_attr_vars
		type_vars_in_lifted_args attr_vars_in_lifted_args {th_vars=type_var_heap,th_attrs=attr_var_heap}
	# type_var_heap = foldSt clear_binding_of_type_var type_vars_in_lifted_args type_var_heap
	  type_var_heap = foldStS set_external_type_var_forwarding new_and_old_external_type_vars type_var_heap
	  attr_var_heap = foldSt clear_binding_of_attr_var attr_vars_in_lifted_args attr_var_heap
	  attr_var_heap = foldStS set_external_attr_var_forwarding new_and_old_external_attr_vars attr_var_heap
	// new -> old
	  (lifted_args,type_heaps) = replace_external_vars lifted_args {th_vars=type_var_heap,th_attrs=attr_var_heap}
	  (lifted_contexts,type_heaps) = replace_external_vars lifted_contexts type_heaps
	  (lifted_attr_env,type_heaps) = replace_external_vars lifted_attr_env type_heaps
	=  (lifted_args,lifted_contexts,lifted_attr_env,type_heaps)
where
	clear_binding_of_type_var {tv_info_ptr} type_var_heap
		= writePtr tv_info_ptr TVI_Empty type_var_heap

	set_external_type_var_forwarding (P new_external_var old_external_var) type_var_heap
		= writePtr new_external_var (TVI_TypeVar old_external_var) type_var_heap

	clear_binding_of_attr_var {av_info_ptr} attr_var_heap
		= writePtr av_info_ptr AVI_Empty attr_var_heap

	set_external_attr_var_forwarding (P new_external_var old_external_var) attr_var_heap
		= writePtr new_external_var (AVI_AttrVar old_external_var) attr_var_heap

class replace_external_vars a :: !a !*TypeHeaps -> (!a,!*TypeHeaps)

instance replace_external_vars [a] | replace_external_vars a where
	replace_external_vars [e:l] type_heaps
		# (e,type_heaps) = replace_external_vars e type_heaps
		# (l,type_heaps) = replace_external_vars l type_heaps
		= ([e:l],type_heaps)
	replace_external_vars [] type_heaps
		= ([],type_heaps)

instance replace_external_vars AType where
	replace_external_vars {at_attribute=at_attribute=:TA_Var {av_ident,av_info_ptr},at_type} type_heaps
		# (at_type,type_heaps) = replace_external_vars at_type type_heaps
		  (av_info,attr_var_heap) = readPtr av_info_ptr type_heaps.th_attrs
		  type_heaps & th_attrs=attr_var_heap
		= case av_info of
			AVI_AttrVar old_external_var
				-> ({at_attribute=TA_Var {av_ident=av_ident,av_info_ptr=old_external_var},at_type=at_type},type_heaps)
			_
				-> ({at_attribute=at_attribute,at_type=at_type},type_heaps)
	replace_external_vars {at_attribute=at_attribute=:TA_RootVar {av_ident,av_info_ptr},at_type} type_heaps
		# (at_type,type_heaps) = replace_external_vars at_type type_heaps
		  (av_info,attr_var_heap) = readPtr av_info_ptr type_heaps.th_attrs
		  type_heaps & th_attrs=attr_var_heap
		= case av_info of
			AVI_AttrVar old_external_var
				-> ({at_attribute=TA_RootVar {av_ident=av_ident,av_info_ptr=old_external_var},at_type=at_type},type_heaps)
			_
				-> ({at_attribute=at_attribute,at_type=at_type},type_heaps)
	replace_external_vars {at_attribute,at_type} type_heaps
		# (at_type,type_heaps) = replace_external_vars at_type type_heaps
		= ({at_attribute=at_attribute,at_type=at_type},type_heaps)

instance replace_external_vars Type where
	replace_external_vars type=:(TV {tv_ident,tv_info_ptr}) type_heaps
		# (tv_info,type_var_heap) = readPtr tv_info_ptr type_heaps.th_vars
		  type_heaps & th_vars=type_var_heap
		= case tv_info of
			TVI_TypeVar old_external_var
				-> (TV {tv_ident=tv_ident,tv_info_ptr=old_external_var},type_heaps)
			_
				->  (type, type_heaps)
	replace_external_vars (arg_type-->restype) type_heaps
		# (arg_type,type_heaps) = replace_external_vars arg_type type_heaps
		# (restype,type_heaps) = replace_external_vars restype type_heaps
		= (arg_type-->restype,type_heaps)
	replace_external_vars (TA tc types) type_heaps
		# (types,type_heaps) = replace_external_vars types type_heaps
		= (TA tc types, type_heaps)
	replace_external_vars (TAS tc types strictness) type_heaps
		# (types,type_heaps) = replace_external_vars types type_heaps
		= (TAS tc types strictness, type_heaps)
	replace_external_vars (cv=:(CV {tv_ident,tv_info_ptr}) :@: types) type_heaps
		# (types,type_heaps) = replace_external_vars types type_heaps
		  (tv_info,type_var_heap) = readPtr tv_info_ptr type_heaps.th_vars
		  type_heaps & th_vars=type_var_heap
		= case tv_info of
			TVI_TypeVar old_external_var
				-> (CV {tv_ident=tv_ident,tv_info_ptr=old_external_var} :@: types,type_heaps)
			_
				-> (cv :@: types, type_heaps)
	replace_external_vars (TArrow1 type) type_heaps
		# (type,type_heaps) = replace_external_vars type type_heaps
		= (TArrow1 type,type_heaps)
	replace_external_vars (TFA vars type) type_heaps
		# (type,type_heaps) = replace_external_vars type type_heaps
		= (TFA vars type,type_heaps)
	replace_external_vars (TFAC vars type type_contexts) type_heaps
		# (type,type_heaps) = replace_external_vars type type_heaps
		# (type_contexts,type_heaps) = replace_external_vars type_contexts type_heaps
		= (TFAC vars type type_contexts,type_heaps)
	replace_external_vars type type_heaps
		= (type, type_heaps)

instance replace_external_vars TypeContext where
	replace_external_vars tc=:{tc_types} type_heaps
		# (tc_types,type_heaps) = replace_external_vars tc_types type_heaps
		= ({tc & tc_types=tc_types},type_heaps)

instance replace_external_vars AttrInequality where
	replace_external_vars {ai_demanded,ai_offered} type_heaps
		# (ai_demanded,type_heaps) = replace_external_vars ai_demanded type_heaps
		# (ai_offered,type_heaps) = replace_external_vars ai_offered type_heaps
		= ({ai_demanded=ai_demanded,ai_offered=ai_offered},type_heaps)

instance replace_external_vars AttributeVar where
	replace_external_vars av=:{av_ident,av_info_ptr} type_heaps
		# (av_info,attr_var_heap) = readPtr av_info_ptr type_heaps.th_attrs
		  type_heaps & th_attrs=attr_var_heap
		= case av_info of
			AVI_AttrVar old_external_var
				-> ({av_ident=av_ident,av_info_ptr=old_external_var},type_heaps)
			_
				-> (av,type_heaps)

optBeautifulizeIdent :: !String -> Optional (!String, !LineNr)
optBeautifulizeIdent id_name
	# fst_semicolon_index = searchlArrElt ((==) ';') id_name 0
	| fst_semicolon_index < size id_name
		# snd_semicolon_index = searchlArrElt ((==) ';') id_name (fst_semicolon_index+1)
		  prefix = id_name % (0, fst_semicolon_index-1)
		  line = toInt (id_name % (fst_semicolon_index+1, snd_semicolon_index-1))
		= Yes (prefix_to_readable_name prefix, line)
	= No
  where
	prefix_to_readable_name "_c"	= "case"
	prefix_to_readable_name "_g"	= "guard"
	prefix_to_readable_name "_f"	= "filter"
	prefix_to_readable_name "_if"	= "if"
	prefix_to_readable_name "\\"	= "lambda"
	prefix_to_readable_name prefix
		| prefix.[0] == 'c'
			= "comprehension"
		| prefix.[0] == 'g'
			= "generator"
	prefix_to_readable_name _		= abort "fatal error in optBeautifulizeIdent in typesupport"

// search for an element in an array
searchlArrElt p s i
	:== searchl s i
  where
	searchl s i
		| i>=size s
			= i
		| p s.[i]
			= i
		= searchl s (i+1)

removeUnusedAttrVars :: !{!CoercionTree} ![Int] -> Coercions
removeUnusedAttrVars demanded unused_attr_vars
	# nr_of_attr_vars
			= size demanded
	  coercions
			= emptyCoercions nr_of_attr_vars
	  coercions
	  		= iFoldSt (add_inequalities demanded) 0 nr_of_attr_vars coercions
	= foldSt redirect_inequalities_that_contain_unused_attr_var unused_attr_vars coercions
	  
  where
	add_inequalities :: !{!CoercionTree} !Int !*Coercions -> *Coercions
	add_inequalities demanded i coercions	
		= foldSt (\demanded coercions -> newInequality i demanded coercions)
				(fst (flattenCoercionTree demanded.[i])) coercions
	redirect_inequalities_that_contain_unused_attr_var :: !Int !*Coercions -> *Coercions
	redirect_inequalities_that_contain_unused_attr_var unused_attr_var 
				coercions=:{coer_offered, coer_demanded}
		# (offered_attr_vars, coer_offered)
				= accCoercionTree flattenCoercionTree unused_attr_var coer_offered
		  (demanded_attr_vars, coer_demanded)
				= accCoercionTree flattenCoercionTree unused_attr_var coer_demanded
		  coer_offered = { coer_offered & [unused_attr_var] = CT_Empty }
		  coer_offered = foldSt (appCoercionTree (removeNode unused_attr_var)) demanded_attr_vars coer_offered
		  coer_demanded = { coer_demanded & [unused_attr_var] = CT_Empty }
		  coer_demanded = foldSt (appCoercionTree (removeNode unused_attr_var)) offered_attr_vars coer_demanded
		= foldSt (\(offered, demanded) coercions -> newInequality offered demanded coercions)
				[(offered, demanded) \\ offered<-offered_attr_vars, demanded<-demanded_attr_vars]
				{ coercions & coer_offered = coer_offered, coer_demanded = coer_demanded }

getTypeVars :: !a !*TypeVarHeap -> (!.[TypeVar],!.TypeVarHeap) | performOnTypeVars a
getTypeVars type th_vars
	# th_vars = performOnTypeVars initializeToTVI_Empty type th_vars
	= performOnTypeVars accum_unencountered_type_var type ([], th_vars)
  where
	accum_unencountered_type_var _ tv=:{tv_info_ptr} (type_var_accu, th_vars)
		# (tvi, th_vars) = readPtr tv_info_ptr th_vars
		= case tvi of
			TVI_Empty
				-> ([tv:type_var_accu], writePtr tv_info_ptr TVI_Used th_vars)
			TVI_Used
				-> (type_var_accu, th_vars)

getAttrVars :: !a !*AttrVarHeap -> (!.[AttributeVar],!.AttrVarHeap) | performOnAttrVars a
getAttrVars type th_attrs
	# th_attrs = performOnAttrVars initializeToAVI_Empty type th_attrs
	= performOnAttrVars accum_unencountered_attr_var type ([], th_attrs)
  where
	accum_unencountered_attr_var av=:{av_info_ptr} (attr_var_accu, th_attrs)
		# (avi, th_attrs) = readPtr av_info_ptr th_attrs
		= case avi of
			AVI_Empty
				-> ([av:attr_var_accu], writePtr av_info_ptr AVI_Used th_attrs)
			AVI_Used
				-> (attr_var_accu, th_attrs)

class performOnTypeVars a :: !(TypeAttribute TypeVar .st -> .st) !a !.st -> .st
// run through a type and do something on each type variable

instance performOnTypeVars Type
  where
	performOnTypeVars f (TA _ args) st
		= performOnTypeVars f args st
	performOnTypeVars f (TAS _ args _) st
		= performOnTypeVars f args st
	performOnTypeVars f (at1 --> at2) st
		= performOnTypeVars f at2 (performOnTypeVars f at1 st)
	performOnTypeVars f (cv :@: at) st
		= performOnTypeVars f cv (performOnTypeVars f at st)
	performOnTypeVars f (TArrow1 at) st
		= performOnTypeVars f at st
	performOnTypeVars f (TFA vars type) st
		= performOnTypeVars f type st
	performOnTypeVars f _ st
		= st

instance performOnTypeVars AType
  where
	performOnTypeVars f {at_attribute, at_type=TV type_var} st
		= f at_attribute type_var st
	performOnTypeVars f {at_attribute, at_type=GTV type_var} st
		= f at_attribute type_var st
	performOnTypeVars f {at_attribute, at_type} st
		= performOnTypeVars f at_type st

instance performOnTypeVars ConsVariable
  where
	performOnTypeVars f (CV type_var) st
		= f TA_Multi type_var st

instance performOnTypeVars [a] | performOnTypeVars a
  where
	performOnTypeVars f [] st
		= st
	performOnTypeVars f [h:t] st
		= performOnTypeVars f t (performOnTypeVars f h st)

instance performOnTypeVars (a, b) | performOnTypeVars a & performOnTypeVars b
  where
	performOnTypeVars f (a, b) st
		= performOnTypeVars f b (performOnTypeVars f a st)

class performOnAttrVars a :: !(AttributeVar .st -> .st) !a !.st -> .st
// run through a type and do something on each attribute variable

instance performOnAttrVars Type
  where
	performOnAttrVars f (TA _ args) st
		= performOnAttrVars f args st
	performOnAttrVars f (TAS _ args _) st
		= performOnAttrVars f args st
	performOnAttrVars f (at1 --> at2) st
		= performOnAttrVars f at2 (performOnAttrVars f at1 st)
	performOnAttrVars f (_ :@: at) st
		= performOnAttrVars f at st
	performOnAttrVars f (TArrow1 at) st
		= performOnAttrVars f at st
	performOnAttrVars f (TFA vars type) st
		= performOnAttrVars f type st
	performOnAttrVars f (TFAC vars type type_contexts) st
		= performOnAttrVars f type st
	performOnAttrVars f _ st
		= st

instance performOnAttrVars AType
  where
	performOnAttrVars f {at_attribute=TA_Var attr_var, at_type} st
		= performOnAttrVars f at_type (f attr_var st)
	performOnAttrVars f {at_attribute=TA_RootVar attr_var, at_type} st
		= performOnAttrVars f at_type (f attr_var st)
	performOnAttrVars f {at_type} st
		= performOnAttrVars f at_type st

instance performOnAttrVars [a] | performOnAttrVars a
  where
	performOnAttrVars f [] st
		= st
	performOnAttrVars f [h:t] st
		= performOnAttrVars f t (performOnAttrVars f h st)

instance performOnAttrVars (a, b) | performOnAttrVars a & performOnAttrVars b
  where
	performOnAttrVars f (a, b) st
		= performOnAttrVars f b (performOnAttrVars f a st)


initializeToTVI_Empty :: a !TypeVar !*TypeVarHeap -> .TypeVarHeap
initializeToTVI_Empty _ {tv_info_ptr} th_vars
	= writePtr tv_info_ptr TVI_Empty th_vars

initializeToAVI_Empty :: !AttributeVar !*AttrVarHeap -> .AttrVarHeap
initializeToAVI_Empty {av_info_ptr} th_attrs
	= writePtr av_info_ptr AVI_Empty th_attrs

appTypeVarHeap f type_heaps :== let th_vars = f type_heaps.th_vars in { type_heaps & th_vars = th_vars }
accTypeVarHeap f type_heaps :== let (r, th_vars) = f type_heaps.th_vars in (r, { type_heaps & th_vars = th_vars })
accAttrVarHeap f type_heaps :== let (r, th_attrs) = f type_heaps.th_attrs in (r, { type_heaps & th_attrs = th_attrs })
	
foldATypeSt on_atype on_type type st :== fold_atype_st type st
  where
	fold_type_st type=:(TA type_symb_ident args) st
		#! st = fold_args args st
		= on_type type st
	fold_type_st type=:(TAS type_symb_ident args _) st
		#! st = fold_args args st
		= on_type type st
	fold_type_st type=:(l --> r) st
		#! st = fold_atype_st r (fold_atype_st l st)
		= on_type type st
	fold_type_st type=:(TArrow1 t) st
		#! st = fold_atype_st t st
		= on_type type st	
	fold_type_st type=:(_ :@: args) st
		#! st = fold_args args st
		= on_type type st
	fold_type_st type st
		= on_type type st

	fold_atype_st atype=:{at_type} st
		#! st = fold_type_st at_type st
		= on_atype atype st

	fold_args [a:x] st
		#! st = fold_atype_st a st
		= fold_args x st
	fold_args [] st
		= st
