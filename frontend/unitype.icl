implementation module unitype

import StdEnv

import syntax, analunitypes, type, utilities, checktypes, RWSDebug

import cheat

/* MW3 moved to syntax:
::	CoercionPosition =
	{	cp_expression	:: !Expression
	}
*/

AttrUni			:== 0
AttrMulti		:== 1
/*
FirstAttrVar	:== 2
*/
AttrExi			:== 2
FirstAttrVar	:== 3

::	CoercionTree	= CT_Node !Int !CoercionTree !CoercionTree | CT_Empty | CT_Unique | CT_NonUnique

::	Coercions		= { coer_demanded :: !.{! .CoercionTree}, coer_offered :: !.{! .CoercionTree }}

::	AttributePartition :== {# Int}

::	PartitioningInfo = 
	{	pi_marks :: 		!.AttributePartition
	,	pi_next_num ::		!Int
	,	pi_groups ::		![[Int]]
	,	pi_deps ::			![Int]
	}


uniquenessError :: !CoercionPosition !String !*ErrorAdmin -> *ErrorAdmin
uniquenessError position mess err=:{ea_file,ea_loc}
	# ea_file = ea_file <<< "Uniqueness error " <<< hd ea_loc <<< ": \"" <<<  position <<< '\"' <<< mess <<< '\n'
	= { err & ea_file = ea_file, ea_ok = False}


::	BOOLVECT :== Int

BITINDEX temp_var_id :== temp_var_id >> 5
BITNUMBER temp_var_id :== temp_var_id bitand 31

isPositive :: !TempVarId !{# BOOLVECT } -> Bool
isPositive var_id cons_vars
	= cons_vars.[BITINDEX var_id] bitand (1 << BITNUMBER var_id) <> 0

determineAttributeCoercions :: !AType !AType !Bool !CoercionPosition !u:{! Type} !*Coercions !{# CommonDefs } 
	!{# BOOLVECT } !*TypeDefInfos !*TypeHeaps !*ErrorAdmin
		-> (!u:{! Type}, !*Coercions, !*TypeDefInfos, !*TypeHeaps, !*ErrorAdmin) 
determineAttributeCoercions off_type dem_type coercible position subst coercions defs cons_vars td_infos type_heaps error
	# (exp_off_type, es) = expandType defs cons_vars off_type (subst, { es_type_heaps = type_heaps, es_td_infos = td_infos})
	  (exp_dem_type, (subst, {es_td_infos,es_type_heaps})) = expandType defs cons_vars dem_type es
	  (result, {crc_type_heaps, crc_coercions, crc_td_infos}) = coerce (if coercible PositiveSign TopSign) defs cons_vars [] exp_off_type exp_dem_type 
	  		 { crc_type_heaps = es_type_heaps, crc_coercions = coercions, crc_td_infos = es_td_infos}
	= case result of
		Yes positions
			# (error=:{ea_file}) = errorHeading "Uniqueness error" error
			  (crc_coercions, copy_crc_coercions) = uniqueCopy crc_coercions

			  format = { form_properties = cMarkAttribute, form_attr_position = Yes (reverse positions, copy_crc_coercions) }			
// MW3 was:			  ea_file = error.ea_file <<< " attribute at indicated position could not be coerced " <:: (format, exp_off_type) <<< '\n'
			  
			  ea_file = 
			  	case position of
			  		CP_FunArg _ _
			  			-> ea_file <<< "\"" <<< position <<< "\" "
			  		_
			  			-> ea_file
			  ea_file = ea_file	<<< "attribute at indicated position could not be coerced "
			  					 <:: (format, exp_off_type, Yes initialTypeVarBeautifulizer) <<< '\n'

			-> (subst, crc_coercions, crc_td_infos, crc_type_heaps, { error & ea_file = ea_file })
				
		No
			-> (subst, crc_coercions, crc_td_infos, crc_type_heaps, error)

/*
			# (crc_coercions, copy_crc_coercions) = uniqueCopy crc_coercions
			  format = { form_properties = cMarkAttribute, form_attr_position = Yes ([], copy_crc_coercions) }			
			| file_to_true (stderr <:: (format, exp_off_type) <:: (format, exp_dem_type) <<< '\n')
					---> ("determineAttributeCoercions", exp_off_type, exp_dem_type)
				-> (subst, crc_coercions, crc_td_infos, crc_type_heaps, error)
				-> undef
*/


NotChecked :== -1	
DummyAttrNumber :== -1
::	AttributeGroups	:== {! [Int]}

partitionateAttributes :: !{! CoercionTree} !{! *CoercionTree} -> (!AttributePartition, !{! CoercionTree})
partitionateAttributes coer_offered coer_demanded
	#! max_attr_nr = size coer_offered
	# partitioning_info = { pi_marks = createArray max_attr_nr NotChecked, pi_deps = [], pi_next_num = 0, pi_groups = [] }
	# {pi_marks,pi_groups} = partitionate_attributes FirstAttrVar max_attr_nr coer_offered partitioning_info
	  (nr_of_groups, groups) = reverse_and_length pi_groups 0 []
	  partition = build_partition 0 groups pi_marks
	# demanded = { CT_Empty \\ i <- [0 .. nr_of_groups - 1] }
	= (partition, adjust_coercions 0 groups partition coer_offered coer_demanded demanded)
where
	visit_attributes :: !CoercionTree !Int !Int !{! CoercionTree} !*PartitioningInfo -> *(!Int, !*PartitioningInfo)
	visit_attributes (CT_Node attr left right) max_attr_nr min_dep coer_offered pi=:{pi_marks}
		#! mark = pi_marks.[attr]
		| mark == NotChecked
			# (mark, pi) = partitionate_attribute attr max_attr_nr coer_offered pi
			  (min_dep, pi) = visit_attributes left max_attr_nr (min min_dep mark)  coer_offered pi
			= visit_attributes right max_attr_nr min_dep coer_offered pi
		# (min_dep, pi) = visit_attributes left max_attr_nr (min min_dep mark) coer_offered pi
		= visit_attributes right max_attr_nr min_dep coer_offered pi
	visit_attributes tree max_attr_nr min_dep coer_offered pi
		= (min_dep, pi)
	
	reverse_and_length :: ![a] !Int ![a] -> (!Int, ![a])
	reverse_and_length [] length list = (length, list)
	reverse_and_length [ x : xs ] length list = reverse_and_length xs (inc length) [x : list]
	
 	partitionate_attributes :: !Int !Int !{!CoercionTree} !*PartitioningInfo -> *PartitioningInfo
	partitionate_attributes from_index max_attr_nr coer_offered pi=:{pi_marks}
		| from_index == max_attr_nr
			= pi
		| pi_marks.[from_index] == NotChecked
			# (_, pi) = partitionate_attribute from_index max_attr_nr coer_offered pi
			= partitionate_attributes (inc from_index) max_attr_nr coer_offered pi
		= partitionate_attributes (inc from_index) max_attr_nr coer_offered pi

	partitionate_attribute :: !Int !Int !{!CoercionTree} !*PartitioningInfo -> *(!Int, !*PartitioningInfo)
	partitionate_attribute attr max_attr_nr coer_offered=:{ [attr] = off_attributes } pi=:{pi_next_num}
		# (min_dep, pi) = visit_attributes off_attributes max_attr_nr max_attr_nr coer_offered (push_on_dep_stack attr pi)
		= try_to_close_group attr pi_next_num min_dep max_attr_nr pi
	where		
		push_on_dep_stack attr pi=:{pi_deps,pi_marks,pi_next_num}
			= { pi & pi_deps = [attr : pi_deps], pi_marks = { pi_marks & [attr] = pi_next_num }, pi_next_num = inc pi_next_num}

		try_to_close_group attr attr_nr min_dep max_attr_nr pi=:{pi_marks, pi_deps, pi_groups}
			| attr_nr <= min_dep
				# (pi_deps, pi_marks, group) = close_group attr pi_deps pi_marks [] max_attr_nr
				= (max_attr_nr, { pi & pi_deps = pi_deps, pi_marks = pi_marks, pi_groups = [group : pi_groups] })
				= (min_dep, pi)
		where
			close_group attr [d:ds] marks group max_attr_nr
				# marks = { marks & [d] = max_attr_nr }
				| d == attr
					= (ds, marks, [d : group])
					= close_group attr ds marks [d : group] max_attr_nr

	build_partition group_nr [] partition
		= partition
	build_partition group_nr [group : groups] partition
		= build_partition (inc group_nr) groups (build_partition_of_group group_nr group partition)
	where
		build_partition_of_group group_nr [attr : attrs] partition
			= build_partition_of_group group_nr attrs { partition & [attr] = group_nr }
		build_partition_of_group group_nr [] partition
			= partition

	adjust_coercions group_index [group : groups] partition coer_offered coer_demanded demanded
		# (combined_tree, coer_demanded) = combine_coercion_trees group_index group partition CT_Empty coer_offered coer_demanded
		= adjust_coercions (inc group_index) groups partition coer_offered coer_demanded { demanded & [ group_index ] = combined_tree }
	adjust_coercions group_index [] partition coer_offered coer_demanded demanded
		= demanded

	combine_coercion_trees group_index [ attr : attrs ] partition merged_tree coer_offered coer_demanded
		| isNonUnique coer_offered.[attr]
			= (CT_NonUnique, coer_demanded)
		# (next_tree, coer_demanded) = replace coer_demanded attr CT_Empty
		| isUnique next_tree
			= (CT_Unique, coer_demanded)
			# merged_tree = rebuild_tree group_index partition next_tree merged_tree
			= combine_coercion_trees group_index attrs partition merged_tree coer_offered coer_demanded
	combine_coercion_trees group_index [ ] partition merged_tree coer_offered coer_demanded
		= (merged_tree, coer_demanded)
		

	rebuild_tree :: !Index !AttributePartition !*CoercionTree !*CoercionTree -> *CoercionTree
	rebuild_tree group_index partition (CT_Node attr left right) tree
		# tree = rebuild_tree group_index partition left tree
		  tree = rebuild_tree group_index partition right tree
		#! attr_nr = partition.[attr]
		| attr_nr == group_index
			= tree
		# { tree } = insert partition.[attr] tree
		= tree	
	where
		insert ::  !Int !*CoercionTree -> *CoercionTreeRecord
		insert new_attr CT_Empty
			=  { tree = CT_Node new_attr CT_Empty CT_Empty }
		insert new_attr (CT_Node this_attr ct_less ct_greater)
			| new_attr < this_attr
				# { tree } = insert new_attr ct_less
				= { tree = CT_Node this_attr tree ct_greater }
			| new_attr > this_attr
				# { tree } = insert new_attr ct_greater
				= { tree = CT_Node this_attr ct_less tree }
				= { tree = CT_Node this_attr ct_less ct_greater }
	rebuild_tree group_index partition empty_tree tree
		= tree

::	CoercionTreeRecord = { tree :: !.CoercionTree }


liftSubstitution :: !*{! Type} !{# CommonDefs } !{# BOOLVECT }  !Int !*TypeVarHeap !*TypeDefInfos -> (*{! Type}, !Int, !*TypeVarHeap, !*TypeDefInfos)
liftSubstitution subst modules cons_vars attr_store type_var_heap td_infos 
	# ls = { ls_next_attr = attr_store, ls_td_infos = td_infos, ls_type_var_heap = type_var_heap}
	= lift_substitution 0 modules cons_vars subst ls
where
	lift_substitution var_index modules cons_vars subst ls
		| var_index < size subst
			# (type, subst) = subst![var_index]
			# (type, subst, ls) = lift modules cons_vars type subst ls
			= lift_substitution (inc var_index) modules cons_vars { subst & [var_index] = type } ls
			= (subst, ls.ls_next_attr, ls.ls_type_var_heap, ls.ls_td_infos)

adjustSignClass :: !SignClassification !Int -> SignClassification
adjustSignClass {sc_pos_vect,sc_neg_vect} arity
	= { sc_pos_vect = sc_pos_vect >> arity, sc_neg_vect = sc_neg_vect >> arity }

//adjustPropClass :: !PropClassification !Int -> PropClassification
adjustPropClass prop_class arity :== prop_class >> arity

::	LiftState = 
	{	ls_next_attr		:: !Int
	,	ls_type_var_heap	:: !.TypeVarHeap
	,	ls_td_infos			:: !.TypeDefInfos
	}


liftTempTypeVariable :: !{# CommonDefs } !{# BOOLVECT } !TempVarId !*{! Type} !*LiftState
	-> (!Type, !*{! Type}, !*LiftState)
liftTempTypeVariable modules cons_vars tv_number subst ls
	#! type = subst.[tv_number]
	= case type of
		TE	-> (TempV tv_number, subst, ls)
		_	-> lift modules cons_vars type subst ls

class lift a :: !{# CommonDefs } !{# BOOLVECT } !a !*{! Type} !*LiftState
	-> (!a, !*{! Type}, !*LiftState)

instance lift Type
where
	lift modules cons_vars (TempV tv_number) subst ls
		= liftTempTypeVariable modules cons_vars tv_number subst ls
	lift modules cons_vars (arg_type --> res_type) subst ls
		# (arg_type, subst, ls) = lift modules cons_vars arg_type subst ls
		  (res_type, subst, ls) = lift modules cons_vars res_type subst ls
		= (arg_type --> res_type, subst, ls)
	lift modules cons_vars (TA cons_id=:{type_name,type_index={glob_object,glob_module},type_arity} cons_args) subst ls
		# ({tdi_kinds}, ls) = ls!ls_td_infos.[glob_module].[glob_object]
		  (cons_args, sign_classes, prop_classes, subst, ls) = lift_list modules cons_vars cons_args tdi_kinds subst ls
		  (type_prop, ls_type_var_heap, ls_td_infos) = typeProperties glob_object glob_module sign_classes prop_classes modules ls.ls_type_var_heap ls.ls_td_infos
		= (TA  { cons_id & type_prop = type_prop } cons_args, subst, { ls & ls_td_infos = ls_td_infos, ls_type_var_heap = ls_type_var_heap})
		where
			lift_list :: !{#CommonDefs} !{# BOOLVECT } ![AType] ![TypeKind] !*{!Type} !*LiftState
				-> (![AType], ![SignClassification], ![PropClassification], !*{!Type}, !*LiftState)
			lift_list modules cons_vars [] _ subst ls
				= ([], [], [], subst, ls)
			lift_list modules cons_vars [t:ts] [tk : tks] subst ls
				# (t, subst, ls) = lift modules cons_vars t subst ls
				  (ts, sign_classes, prop_classes, subst, ls) = lift_list modules cons_vars ts tks subst ls
				| IsArrowKind tk
					= case t.at_type of 
						TA {type_arity,type_prop} _
							-> ([t:ts], [adjustSignClass type_prop.tsp_sign type_arity : sign_classes],
										[adjustPropClass type_prop.tsp_propagation type_arity : prop_classes], subst, ls)
						TempV tmp_var_id
							| isPositive tmp_var_id cons_vars
								-> ([t:ts], [PostiveSignClass : sign_classes], [PropClass : prop_classes], subst, ls)
								-> ([t:ts], [TopSignClass : sign_classes], [NoPropClass : prop_classes], subst, ls)
						_
							-> ([t:ts], [TopSignClass : sign_classes], [PropClass : prop_classes], subst, ls)
					= ([t:ts], sign_classes, prop_classes, subst, ls)

	lift modules cons_vars (TempCV temp_var :@: types) subst ls
		# (type, subst, ls) = liftTempTypeVariable modules cons_vars temp_var subst ls
		  (types, subst, ls) = lift_list modules cons_vars types subst ls
		= case type of
			TA type_cons cons_args
				# nr_of_new_args = length types
				-> (TA { type_cons & type_arity = type_cons.type_arity + nr_of_new_args } (cons_args ++ types), subst, ls)
			TempV tv_number
				-> (TempCV tv_number :@: types, subst, ls)
			cons_var :@: cv_types
				-> (cons_var :@: (cv_types ++ types), subst, ls)
		where
			lift_list :: !{#CommonDefs} !{# BOOLVECT } ![a] !*{!Type} !*LiftState -> (![a], !*{!Type}, !*LiftState) | lift a
			lift_list modules cons_vars [] subst ls
				= ([], subst, ls)
			lift_list modules cons_vars [t:ts] subst ls
				# (t, subst, ls) = lift modules cons_vars t subst ls
				  (ts, subst, ls) = lift_list modules cons_vars ts subst ls
				= ([t:ts], subst, ls)
	lift modules cons_vars type subst ls
		= (type, subst, ls)
	
instance lift AType
where
	lift modules cons_vars attr_type=:{at_attribute,at_type} subst ls
		# (at_type, subst, ls) = lift modules cons_vars at_type subst ls
		| type_is_non_coercible at_type
			= ({attr_type & at_type = at_type },subst, ls)
			= ({attr_type & at_attribute = TA_TempVar ls.ls_next_attr, at_type = at_type}, subst, {ls & ls_next_attr = inc ls.ls_next_attr})
	where
		type_is_non_coercible (TempV _)
			= True
		type_is_non_coercible (TempQV _)
			= True
		type_is_non_coercible (_ --> _)
			= True
		type_is_non_coercible (_ :@: _)
			= True
		type_is_non_coercible _
			= False


::	ExpansionState = 
	{	es_type_heaps	:: !.TypeHeaps
	,	es_td_infos		:: !.TypeDefInfos
	}

class expandType a :: !{# CommonDefs } !{# BOOLVECT } !a !*(!u:{! Type}, !*ExpansionState) -> (!a, !*(!u:{! Type}, !*ExpansionState))

instance expandType AType
where
	expandType modules cons_vars attr_type=:{at_type, at_attribute} (subst, es=:{es_type_heaps})
		# (at_attribute, th_attrs) = expand_attribute at_attribute es_type_heaps.th_attrs
		  (at_type, subst_and_es) = expandType modules cons_vars at_type (subst, {es & es_type_heaps = { es_type_heaps & th_attrs = th_attrs }})
		= ({ attr_type & at_type = at_type, at_attribute = at_attribute }, subst_and_es)
	where
		expand_attribute (TA_Var {av_name,av_info_ptr}) attr_var_heap
			= case (readPtr av_info_ptr attr_var_heap) of
				(AVI_Attr attr, attr_var_heap)
					-> (attr, attr_var_heap)
				(info, attr_var_heap)
					-> abort ("expand_attribute (unitype.icl)" ---> (av_name <<- info ))
		expand_attribute attr attr_var_heap
			= (attr, attr_var_heap)
	
expandTempTypeVariable :: !TempVarId !*(!u:{! Type}, !*ExpansionState) -> (!Type, !*(!u:{! Type}, !*ExpansionState))
expandTempTypeVariable tv_number (subst, es)
	#! type = subst.[tv_number]
	= case type of
		TE	-> (TempV tv_number, (subst, es))
		_	-> (type, (subst, es))

IsArrowKind (KindArrow _) = True
IsArrowKind _ = False

instance expandType Type
where
	expandType modules cons_vars (TempV tv_number) es
		= expandTempTypeVariable tv_number es
	expandType modules cons_vars (TV {tv_info_ptr}) (subst, es=:{es_type_heaps})
		# (TVI_Type type, th_vars) = readPtr tv_info_ptr es_type_heaps.th_vars
		= (type, (subst, {es & es_type_heaps = { es_type_heaps & th_vars = th_vars }}))
	expandType modules cons_vars (arg_type --> res_type) es
		# (arg_type, es) = expandType modules cons_vars arg_type es
		  (res_type, es) = expandType modules cons_vars res_type es
		= (arg_type --> res_type, es)
	expandType modules cons_vars (TA cons_id=:{type_name, type_index={glob_object,glob_module}} cons_args) (subst, es)
		# ({tdi_kinds}, es) = es!es_td_infos.[glob_module].[glob_object]
		  (cons_args, hio_signs, hio_props, (subst,es=:{es_td_infos,es_type_heaps})) = expand_type_list modules cons_vars cons_args tdi_kinds (subst, es)
		  (type_prop, th_vars, es_td_infos)
		  			= typeProperties glob_object glob_module hio_signs hio_props modules es_type_heaps.th_vars es_td_infos
		= (TA { cons_id & type_prop = type_prop } cons_args,
				(subst, { es & es_td_infos = es_td_infos, es_type_heaps = { es_type_heaps & th_vars = th_vars }}))
//					 ---> ("expandType", type_name, type_prop.tsp_propagation)
	where
		expand_type_list ::  !{#CommonDefs} !{# BOOLVECT } ![AType] ![TypeKind] !(!u:{!Type}, !*ExpansionState)
			-> (![AType], ![SignClassification], ![PropClassification], !(!u:{!Type}, !*ExpansionState))
		expand_type_list modules cons_vars [] _ es
			= ([], [], [], es)
		expand_type_list modules cons_vars [t:ts] [tk : tks] es
			# (t, es) = expandType modules cons_vars t es
			  (ts, sign_classes, prop_classes, es) = expand_type_list modules cons_vars ts tks es
			| IsArrowKind tk
				= case t.at_type of 
					TA {type_arity,type_prop} _
						-> ([t:ts], [adjustSignClass type_prop.tsp_sign type_arity : sign_classes],
									[adjustPropClass type_prop.tsp_propagation type_arity : prop_classes], es)
					TempV tmp_var_id
						| isPositive tmp_var_id cons_vars
							-> ([t:ts], [PostiveSignClass : sign_classes], [PropClass : prop_classes], es)
							-> ([t:ts], [TopSignClass : sign_classes], [NoPropClass : prop_classes], es)
					_
						-> ([t:ts], [TopSignClass : sign_classes], [PropClass : prop_classes], es)
				= ([t:ts], sign_classes, prop_classes, es)
					
	expandType modules cons_vars (TempCV temp_var :@: types) es
		# (type, es) = expandTempTypeVariable temp_var es
		  (types, es) = expandType modules cons_vars types es
		= case type of
			TA type_cons=:{type_arity} cons_args
				# nr_of_new_args = length types
				-> (TA { type_cons & type_arity = type_arity + nr_of_new_args } (cons_args ++ types), es)
			TempV tv_number
				-> (TempCV tv_number :@: types, es)
			cons_var :@: cv_types
				-> (cons_var :@: (cv_types ++ types), es)
	expandType modules cons_vars type es
		= (type, es)

instance expandType [a] | expandType a
where
	expandType modules cons_vars l es = mapSt (expandType modules cons_vars) l es
	
instance toInt TypeAttribute
where
	 toInt TA_Unique 				= AttrUni
	 toInt (TA_TempVar av_number)	= av_number
	 toInt TA_Multi 				= AttrMulti
	 toInt TA_None 					= AttrMulti
	 toInt TA_TempExVar 			= PA_BUG AttrExi (abort "toInt TA_TempExVar")


::	CoercionState =
	{	crc_type_heaps	:: !.TypeHeaps
	,	crc_coercions	:: !.Coercions
	,	crc_td_infos	:: !.TypeDefInfos
	}

::	TypePosition :== [Int]

/*

'coerceAttributes offered_attribute offered_attribute sign coercions' coerce offered_attribute to
offered_attribute according to sign. Failure is indicated by returning False as a result.

*/

/* Just Temporary */

coerceAttributes TA_TempExVar dem_attr _ coercions
	= PA_BUG (True, coercions) (abort "coerceAttributes TA_TempExVar")
coerceAttributes _ TA_TempExVar _ coercions
	= PA_BUG (True, coercions) (abort "coerceAttributes TA_TempExVar")
/* ... remove this !!!! */

coerceAttributes TA_Unique dem_attr {neg_sign} coercions
	| not neg_sign
		= (True, coercions)
coerceAttributes off_attr TA_Unique {pos_sign} coercions
	| not pos_sign
		= (True, coercions)
coerceAttributes off_attr TA_Multi {neg_sign} coercions
	| not neg_sign
		= (True, coercions)
coerceAttributes TA_Multi dem_attr {pos_sign} coercions
	| not pos_sign
		= (True, coercions)
coerceAttributes (TA_TempVar av_number) dem_attr {neg_sign} coercions=:{coer_demanded}
	| not neg_sign && isUnique coer_demanded.[av_number]
		= (True, coercions)
coerceAttributes off_attr (TA_TempVar av_number) {pos_sign} coercions=:{coer_demanded}
	| not pos_sign && isUnique coer_demanded.[av_number]
		= (True, coercions)
coerceAttributes (TA_TempVar av_number1) (TA_TempVar av_number2) {pos_sign,neg_sign} coercions
	| av_number1 == av_number2
		= (True, coercions)
	| pos_sign
		| neg_sign
			# (ok, coercions) = new_inequality av_number1 av_number2 coercions
			| ok
				= new_inequality av_number2 av_number1 coercions
				= (False, coercions)
			= new_inequality av_number1 av_number2 coercions
	| neg_sign
		= new_inequality av_number2 av_number1 coercions
		= (True, coercions)
where
	new_inequality :: !Int !Int !*Coercions  -> (!Bool, !*Coercions)
	new_inequality off_attr dem_attr coercions=:{coer_demanded, coer_offered}
		| isNonUnique coer_offered.[off_attr]
			| isUnique coer_demanded.[dem_attr]
				= (False, coercions)
				= (True, makeNonUnique dem_attr coercions)
		| isUnique coer_demanded.[dem_attr]
			= (True, makeUnique off_attr coercions)
		| isNonUnique coer_offered.[dem_attr] || isUnique coer_demanded.[off_attr]
			= (True, coercions)
			= (True, newInequality off_attr dem_attr coercions)
					
coerceAttributes TA_Unique (TA_TempVar av_number) {neg_sign} coercions=:{coer_offered}
	| isNonUnique coer_offered.[av_number]
		= (False, coercions)
		= (True, makeUnique av_number coercions)// ---> "*** 1 ***"
coerceAttributes (TA_TempVar av_number) TA_Unique {pos_sign} coercions=:{coer_offered}
	| isNonUnique coer_offered.[av_number]
		= (False, coercions)
		= (True, makeUnique av_number coercions)// ---> "*** 2 ***"
coerceAttributes TA_Multi (TA_TempVar av_number) {pos_sign} coercions=:{coer_demanded}
	| isUnique coer_demanded.[av_number]
		= (False, coercions)
		= (True, makeNonUnique av_number coercions)
coerceAttributes (TA_TempVar av_number) TA_Multi {neg_sign} coercions=:{coer_demanded}
	| isUnique coer_demanded.[av_number]
		= (False, coercions)
		= (True, makeNonUnique av_number coercions)
coerceAttributes TA_Unique TA_Multi _ coercions
	= (False, coercions)
coerceAttributes TA_Multi TA_Unique _ coercions
	= (False, coercions)
coerceAttributes off_attr dem_attr _ coercions
	= (True, coercions)

newInequality :: !Int !Int !*Coercions -> *Coercions 
newInequality off_attr dem_attr coercions=:{coer_demanded, coer_offered}
	# (dem_coercions, coer_demanded) = replace coer_demanded off_attr CT_Empty
	  (succ, dem_coercions) = insert dem_attr dem_coercions
	  coer_demanded = { coer_demanded & [off_attr] = dem_coercions }
	| succ
		# (off_coercions, coer_offered) = replace coer_offered dem_attr CT_Empty
	  	  (succ, off_coercions) = insert off_attr off_coercions
	 	  coer_offered = { coer_offered & [dem_attr] = off_coercions }
		= {coer_demanded = coer_demanded, coer_offered = coer_offered}
		= {coer_demanded = coer_demanded, coer_offered = coer_offered}
where

	insert ::  !Int !*CoercionTree -> (!Bool, !*CoercionTree)
	insert new_attr CT_Empty
		=  (True, CT_Node new_attr CT_Empty CT_Empty)
	insert new_attr (CT_Node this_attr ct_less ct_greater)
		| new_attr < this_attr
			# (succ, ct_less) = insert new_attr ct_less
			= (succ, CT_Node this_attr ct_less ct_greater)
		| new_attr > this_attr
			# (succ, ct_greater) = insert new_attr ct_greater
			= (succ, CT_Node this_attr ct_less ct_greater)
			= (False, CT_Node this_attr ct_less ct_greater)
	
isNonUnique :: !CoercionTree -> Bool
isNonUnique CT_NonUnique	= True
isNonUnique _ 				= False

isUnique  :: !CoercionTree -> Bool
isUnique CT_Unique			= True
isUnique _					= False

isUniqueAttribute :: !Int !Coercions -> Bool
isUniqueAttribute attr_number {coer_demanded}
	= isUnique coer_demanded.[attr_number]

isNonUniqueAttribute :: !Int !Coercions -> Bool
isNonUniqueAttribute attr_number {coer_offered}
	= isNonUnique coer_offered.[attr_number]
		
makeUnique :: !Int !*Coercions -> *Coercions
makeUnique attr {coer_demanded, coer_offered}
	# (off_coercions, coer_offered) = replace coer_offered attr CT_Empty
	  coer_demanded = { coer_demanded & [attr] = CT_Unique }
	= make_unique off_coercions {coer_offered = coer_offered, coer_demanded = coer_demanded}// ---> ("makeUnique :", attr)
where
	// JVG added type:
	make_unique :: !CoercionTree !*Coercions -> *Coercions;
	make_unique (CT_Node this_attr ct_less ct_greater) coercions
		# coercions = makeUnique this_attr coercions
		  coercions = make_unique ct_less coercions
		  coercions = make_unique ct_greater coercions
		= coercions
	make_unique tree coercions
		= coercions

tryToMakeUnique :: !Int !*Coercions -> (!Bool, !*Coercions)
tryToMakeUnique attr coercions=:{coer_offered}
	| isNonUnique coer_offered.[attr]
		= (False, coercions)
		= (True, makeUnique attr coercions)

makeNonUnique :: !Int !*Coercions -> *Coercions
makeNonUnique attr {coer_demanded, coer_offered}
	# (dem_coercions, coer_demanded) = replace coer_demanded attr CT_Empty
	  coer_offered = { coer_offered & [attr] = CT_NonUnique }
	= make_non_unique dem_coercions {coer_offered = coer_offered, coer_demanded = coer_demanded}
//		---> ("makeNonUnique", attr)
where
	// JVG added type:
	make_non_unique :: !CoercionTree !*Coercions -> *Coercions;
	make_non_unique (CT_Node this_attr ct_less ct_greater) coercions
		# coercions = makeNonUnique this_attr coercions
		  coercions = make_non_unique ct_less coercions
		  coercions = make_non_unique ct_greater coercions
		= coercions
	make_non_unique tree coercions
		= coercions

tryToMakeNonUnique :: !Int !*Coercions -> (!Bool, !*Coercions)
tryToMakeNonUnique attr coercions=:{coer_demanded}
	#! s = size coer_demanded
	| isUnique coer_demanded.[attr]
//		-?-> (s <= attr, ("tryToMakeNonUnique", s, attr))]
		= (False, coercions)
		= (True, makeNonUnique attr coercions)
//				---> ("tryToMakeNonUnique", attr)

class coerce a ::  !Sign !{# CommonDefs} !{# BOOLVECT} !TypePosition !a !a !*CoercionState -> (!Optional TypePosition, !*CoercionState)

Success No		=  True
Success (Yes _)	=  False

instance coerce AType
where
	coerce sign defs cons_vars tpos at1=:{at_attribute=attr1, at_type = type1} at2=:{at_attribute=attr2}  cs=:{crc_coercions}
		// JVG: added !
		#!attr_sign = adjust_sign sign type1 cons_vars
//		# attr_sign = adjust_sign sign type1 cons_vars
		  (succ, crc_coercions) = coerceAttributes attr1 attr2 attr_sign crc_coercions
		| succ
			# (succ, cs) = coerceTypes sign defs cons_vars tpos at1 at2 { cs & crc_coercions = crc_coercions }
			| Success succ
				# (succ1, crc_coercions) = add_propagation_inequalities attr1 type1 cs.crc_coercions
				  (succ2, crc_coercions) = add_propagation_inequalities attr2 at2.at_type crc_coercions
				= (if (succ1 && succ2) No (Yes tpos), { cs & crc_coercions = crc_coercions })
				= (succ, cs)
			= (Yes tpos, { cs & crc_coercions = crc_coercions })
	where		
		adjust_sign :: !Sign !Type {# BOOLVECT} -> Sign
		adjust_sign sign (TempV _) cons_vars
			= TopSign
		adjust_sign sign (TempQV _) cons_vars
			= TopSign
		adjust_sign sign (_ --> _) cons_vars
			= TopSign
		adjust_sign sign (TempCV tmp_var_id :@: _) cons_vars
			| isPositive tmp_var_id cons_vars
				= sign
				= TopSign
		adjust_sign sign (_ :@: _) cons_vars
			= TopSign
		adjust_sign sign (TA {type_name, type_prop={tsp_coercible}} _) cons_vars
			| tsp_coercible
				= sign
				= TopSign
//					---> ("adjust_sign to top", type_name)
		adjust_sign sign _ cons_vars
			= sign

		add_propagation_inequalities attr (TA {type_name,type_prop={tsp_propagation}} cons_args) coercions
			= add_inequalities tsp_propagation attr cons_args coercions
		where
			add_inequalities prop_class attr [] coercions
				= (True, coercions)
			add_inequalities prop_class attr [{at_attribute} : args] coercions
				| (prop_class bitand 1) == 0
					= add_inequalities (prop_class >> 1) attr args coercions
				# (succ, coercions) = coerceAttributes attr at_attribute PositiveSign coercions
				| succ
					= add_inequalities (prop_class >> 1) attr args coercions
					= (False, coercions)
//							---> ("add_propagation_inequalities", attr, at_attribute)
		add_propagation_inequalities attr type coercions
			= (True, coercions)

tryToExpandTypeSyn :: !{#CommonDefs} !{#BOOLVECT} !TypeSymbIdent ![AType] !TypeAttribute !*TypeHeaps !*TypeDefInfos
	-> (!Bool, !Type, !*TypeHeaps, !*TypeDefInfos)
tryToExpandTypeSyn defs cons_vars cons_id=:{type_index={glob_object,glob_module}} type_args attribute type_heaps td_infos
	# {td_rhs,td_args,td_attribute,td_name} = defs.[glob_module].com_type_defs.[glob_object]
	= case td_rhs of
		SynType {at_type}
			# type_heaps = bindTypeVarsAndAttributes td_attribute attribute td_args type_args type_heaps
			  (expanded_type, (_, {es_type_heaps, es_td_infos})) = expandType defs cons_vars at_type
			  		({}, { es_type_heaps = type_heaps, es_td_infos = td_infos })
			-> (True, expanded_type, clearBindingsOfTypeVarsAndAttributes attribute td_args es_type_heaps, es_td_infos)
		_
			-> (False, TA cons_id type_args, type_heaps, td_infos)
		
coerceTypes :: !Sign !{# CommonDefs} !{# BOOLVECT} !TypePosition !AType !AType !*CoercionState -> (!Optional TypePosition, !*CoercionState)		
coerceTypes sign defs cons_vars tpos dem_type=:{at_type = TA dem_cons dem_args} off_type=:{at_type = TA off_cons off_args}  cs=:{crc_type_heaps, crc_td_infos}
	| dem_cons == off_cons
		= coercions_of_arg_types sign defs cons_vars tpos dem_args off_args dem_cons.type_prop.tsp_sign 0 cs
		# (_, exp_dem_type, crc_type_heaps, crc_td_infos) = tryToExpandTypeSyn defs cons_vars dem_cons dem_args dem_type.at_attribute crc_type_heaps crc_td_infos
		  (_, exp_off_type, crc_type_heaps, crc_td_infos) = tryToExpandTypeSyn defs cons_vars off_cons off_args off_type.at_attribute crc_type_heaps crc_td_infos
		= coerceTypes sign defs cons_vars tpos { dem_type & at_type = exp_dem_type } { off_type & at_type = exp_off_type }
							{ cs & crc_type_heaps = crc_type_heaps, crc_td_infos = crc_td_infos }
	where
		coercions_of_arg_types sign defs cons_vars tpos [t1 : ts1] [t2 : ts2] sign_class arg_number cs
			# arg_sign = sign * signClassToSign sign_class arg_number
			  (succ, cs) = coerce arg_sign defs cons_vars [arg_number : tpos] t1 t2 cs
			| Success succ 
				= coercions_of_arg_types sign defs cons_vars tpos ts1 ts2 sign_class (inc arg_number) cs
				= (succ, cs)
		coercions_of_arg_types sign defs cons_vars tpos [] [] _ _ cs
			= (No, cs)
coerceTypes sign defs cons_vars tpos dem_type=:{at_type = TA dem_cons dem_args} off_type cs=:{crc_type_heaps, crc_td_infos}
	# (succ, exp_dem_type, crc_type_heaps, crc_td_infos) = tryToExpandTypeSyn defs cons_vars dem_cons dem_args dem_type.at_attribute crc_type_heaps crc_td_infos
	| succ
		= coerceTypes sign defs cons_vars tpos { dem_type & at_type = exp_dem_type } off_type
					{ cs & crc_type_heaps = crc_type_heaps, crc_td_infos = crc_td_infos }
		= (No, { cs & crc_type_heaps = crc_type_heaps, crc_td_infos = crc_td_infos })
coerceTypes sign defs cons_vars tpos dem_type  off_type=:{at_type = TA off_cons off_args} cs=:{crc_type_heaps, crc_td_infos}
	# (succ, exp_off_type, crc_type_heaps, crc_td_infos) = tryToExpandTypeSyn defs cons_vars off_cons off_args off_type.at_attribute
			crc_type_heaps crc_td_infos
	| succ
		= coerceTypes sign defs cons_vars tpos dem_type { off_type & at_type = exp_off_type }
					{ cs & crc_type_heaps = crc_type_heaps, crc_td_infos = crc_td_infos }
		= (No, { cs & crc_type_heaps = crc_type_heaps, crc_td_infos = crc_td_infos })
coerceTypes sign defs cons_vars tpos {at_type = arg_type1 --> res_type1} {at_type = arg_type2 --> res_type2} cs
	# arg_sign = NegativeSign * sign
	# (succ, cs) = coerce arg_sign defs cons_vars [0 : tpos] arg_type1 arg_type2  cs
	| Success succ
		= coerce sign defs cons_vars [1 : tpos] res_type1 res_type2 cs
		= (succ, cs)
coerceTypes _ defs cons_vars tpos {at_type = cons_var :@: types1} {at_type = _ :@: types2}  cs
	# sign = determine_sign_of_arg_types cons_var cons_vars
	= coercions_of_type_list sign defs cons_vars tpos 0 types1 types2 cs
where
	determine_sign_of_arg_types (TempCV tmp_var_id) cons_vars
		| isPositive tmp_var_id cons_vars
			= PositiveSign
			= TopSign
	determine_sign_of_arg_types _ cons_vars
			= TopSign
		
	coercions_of_type_list sign defs cons_vars tpos arg_number [t1 : ts1] [t2 : ts2] cs
		# (succ, cs) = coerce sign defs cons_vars [arg_number : tpos] t1 t2 cs
		| Success succ
			= coercions_of_type_list sign defs cons_vars tpos (inc arg_number) ts1 ts2 cs
			= (succ, cs)
	coercions_of_type_list sign defs cons_vars tpos arg_number [] [] cs
		= (No, cs)
coerceTypes sign defs cons_vars tpos _ _  cs
	= (No, cs)

AttrRestricted :== 0

instance <<< CoercionTree
where
	(<<<) file (CT_Node attr left right) = file <<< left <<< ' ' <<< attr <<< ' ' <<< right
	(<<<) file CT_Unique = file <<< "CT_Unique"
	(<<<) file CT_NonUnique = file <<< "CT_NonUnique"
	(<<<) file CT_Empty = file <<< "##"

file_to_true :: !File -> Bool
file_to_true file = code {
  .inline file_to_true
          pop_b 2
          pushB TRUE
  .end
  }
			
