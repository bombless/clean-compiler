implementation module hashtable

import StdOverloadedList
import predef, syntax, compare_types, compare_constructor

::	HashTableEntry
		= HTE_Ident !BoxedIdent !IdentClass !Int !HashTableEntry !HashTableEntry
		| HTE_Empty 

::	HashTable =
	{	hte_symbol_heap	:: !.SymbolTable
	,	hte_entries		:: !.{! .HashTableEntry}
	,	hte_mark	:: !Int // 1 for .icl modules, otherwise 0
	}

::	IdentClass	= IC_Expression
				| IC_Type
				| IC_TypeAttr
				| IC_Class
				| IC_Module !QualifiedIdents
				| IC_Field !Ident
				| IC_Selector
				| IC_Instance ![Type]
				| IC_InstanceMember ![Type]
				| IC_Generic
				| IC_GenericCase !Type
				| IC_GenericDeriveClass !Type
				| IC_GenericDeriveClassExcept !Type ![!{#Char}!]
				| IC_TypeExtension !{#Char}/*module name*/
				| IC_Unknown

::	QualifiedIdents	= QualifiedIdents !Ident !IdentClass !QualifiedIdents
					| NoQualifiedIdents;

:: BoxedIdent = {boxed_ident::!Ident}

newHashTable :: !*SymbolTable -> *HashTable
newHashTable symbol_heap = { hte_symbol_heap = symbol_heap, hte_entries = {HTE_Empty \\ i <- [0 .. dec HashTableArraySize]},hte_mark=0}

set_hte_mark :: !Int !*HashTable -> *HashTable
set_hte_mark hte_mark ht = {ht & hte_mark=hte_mark}

instance =< IdentClass
where
	(=<) ic1 ic2
		| not (equal_constructor ic1 ic2)
			| less_constructor ic1 ic2
				= Smaller
				= Greater
	(=<) (IC_Instance types1) (IC_Instance types2)
		= compareInstances types1 types2
	(=<) (IC_InstanceMember types1) (IC_InstanceMember types2)
		= compare_types types1 types2
	(=<) (IC_GenericCase type1) (IC_GenericCase type2)
		# cmp = type1 =< type2
		| cmp == Equal
			= compare_unboxed_array_element_type type1 type2
			= cmp
	(=<) (IC_Field typ_id1) (IC_Field typ_id2)
		= typ_id1 =< typ_id2
	(=<) (IC_GenericDeriveClass type1) (IC_GenericDeriveClass type2)
		# cmp = type1 =< type2
		| cmp == Equal
			= compare_unboxed_array_element_type type1 type2
			= cmp
	(=<) (IC_GenericDeriveClassExcept type1 except_class_names1) (IC_GenericDeriveClassExcept type2 except_class_names2)
		# cmp = type1 =< type2
		| cmp == Equal
			# cmp = compare_unboxed_array_element_type type1 type2
			| cmp == Equal
				| except_class_names1==except_class_names2
					= Equal
				| except_class_names1<except_class_names2
					= Smaller
					= Greater
				= cmp
			= cmp
	(=<) (IC_TypeExtension module_name1) (IC_TypeExtension module_name2)
		= module_name1=<module_name2
	(=<) ic1 ic2
		= Equal

compare_types [t1 : t1s] [t2 : t2s]
	# cmp = t1 =< t2
	| cmp == Equal
		= t1s =< t2s
		= cmp
compare_types [] []
	= Equal
compare_types [] _
	= Smaller
compare_types _ []
	= Greater

compare_unboxed_array_element_type (TA {type_ident={id_name=PD_UnboxedArray_String}} [{at_type=element_type1}]) (TA {type_ident={id_name=PD_UnboxedArray_String}} [{at_type=element_type2}])
	= compare_unboxed_array_element_type` element_type1 element_type2
where
	compare_unboxed_array_element_type` (TA {type_ident={id_name=PD_UnboxedArray_String}} [{at_type=element_type1}]) (TA {type_ident={id_name=PD_UnboxedArray_String}} [{at_type=element_type2}])
		= compare_unboxed_array_element_type` element_type1 element_type2
	compare_unboxed_array_element_type` t1 t2
		= t1 =< t2
compare_unboxed_array_element_type t1 t2
	= Equal

instance =< (!a,!b) |  =< a &  =< b
where
	(=<) (x1,y1) (x2,y2)
		# cmp = x1 =< x2
		| cmp == Equal
			= y1 =< y2
			= cmp

cHashTableSize :== 1023
// the hte_entries array has an additional entry to store the modules with qualified indents
HashTableArraySize :== 1024
ModulesWithQualifiedIdentsHashTableIndex :== 1023

hashValue :: !String -> Int
hashValue name
	# hash_val = hash_value name (size name) 0 rem cHashTableSize
	| hash_val < 0
		= hash_val + cHashTableSize
		= hash_val
where
	hash_value :: !String !Int !Int -> Int
	hash_value name index val
		| index == 0
			= val
		# index = dec index
		  char = name.[index]
		= hash_value name index (val << 2 + toInt char)

putIdentInHashTable :: !String !IdentClass !*HashTable -> (!BoxedIdent, !*HashTable)
putIdentInHashTable name ident_class {hte_symbol_heap,hte_entries,hte_mark}
	# hash_val = hashValue name
	  (entries,hte_entries) = hte_entries![hash_val]
	  (ident, hte_symbol_heap, entries) = insert name ident_class hte_mark hte_symbol_heap entries
	  hte_entries = {hte_entries & [hash_val]=entries}
	= (ident, { hte_symbol_heap = hte_symbol_heap, hte_entries = hte_entries,hte_mark=hte_mark })
where
	insert ::  !String !IdentClass !Int !*SymbolTable *HashTableEntry -> (!BoxedIdent, !*SymbolTable, !*HashTableEntry)
	insert name ident_class hte_mark0 hte_symbol_heap HTE_Empty
		# (hte_symbol_ptr, hte_symbol_heap) = newPtr EmptySymbolTableEntry hte_symbol_heap
		# ident = { id_name = name, id_info = hte_symbol_ptr}
		# boxed_ident={boxed_ident=ident}
		= (boxed_ident, hte_symbol_heap, HTE_Ident boxed_ident ident_class hte_mark0 HTE_Empty HTE_Empty)
	insert name ident_class hte_mark0 hte_symbol_heap (HTE_Ident hte_ident=:{boxed_ident={id_name}} hte_class hte_mark hte_left hte_right)
		# cmp = (name,ident_class) =< (id_name,hte_class)
		| cmp == Equal
			= (hte_ident, hte_symbol_heap, HTE_Ident hte_ident hte_class (hte_mark bitand hte_mark0) hte_left hte_right)
		| cmp == Smaller
			#! (boxed_ident, hte_symbol_heap, hte_left) = insert name ident_class hte_mark0 hte_symbol_heap hte_left
			= (boxed_ident, hte_symbol_heap, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)
			#! (boxed_ident, hte_symbol_heap, hte_right) = insert name ident_class hte_mark0 hte_symbol_heap hte_right
			= (boxed_ident, hte_symbol_heap, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)

putQualifiedIdentInHashTable :: !String !BoxedIdent !IdentClass !*HashTable -> (!BoxedIdent, !*HashTable)
putQualifiedIdentInHashTable module_name ident ident_class {hte_symbol_heap,hte_entries,hte_mark}
	# hash_val = hashValue module_name
	  (entries,hte_entries) = hte_entries![hash_val]
	  (ident, old_qualified_idents, hte_symbol_heap, entries) = insert module_name ident ident_class (IC_Module NoQualifiedIdents) hte_mark hte_symbol_heap entries
	  hte_entries = {hte_entries & [hash_val]=entries}
	| old_qualified_idents=:NoQualifiedIdents
		# (entries,hte_entries) = hte_entries![ModulesWithQualifiedIdentsHashTableIndex]
		  (hte_symbol_heap, entries) = insert_module_with_qualified_idents module_name (IC_Module NoQualifiedIdents) hte_symbol_heap entries
		  hte_entries & [ModulesWithQualifiedIdentsHashTableIndex] = entries
		= (ident, {hte_symbol_heap = hte_symbol_heap, hte_entries = hte_entries,hte_mark=hte_mark})
		= (ident, {hte_symbol_heap = hte_symbol_heap, hte_entries = hte_entries,hte_mark=hte_mark})
where
	insert :: !String !BoxedIdent !IdentClass !IdentClass !Int !*SymbolTable *HashTableEntry
		-> (!BoxedIdent, !QualifiedIdents, !*SymbolTable, !*HashTableEntry)
	insert module_name ident ident_class module_ident_class hte_mark0 hte_symbol_heap HTE_Empty
		# (hte_symbol_ptr, hte_symbol_heap) = newPtr EmptySymbolTableEntry hte_symbol_heap
		  module_ident = { id_name = module_name, id_info = hte_symbol_ptr}
		  boxed_module_ident={boxed_ident=module_ident}
		  old_qualified_idents = NoQualifiedIdents
		  ident_class = IC_Module (QualifiedIdents ident.boxed_ident ident_class old_qualified_idents)
		= (boxed_module_ident, old_qualified_idents, hte_symbol_heap, HTE_Ident boxed_module_ident ident_class hte_mark0 HTE_Empty HTE_Empty)
	insert module_name ident ident_class module_ident_class hte_mark0 hte_symbol_heap (HTE_Ident hte_ident=:{boxed_ident={id_name}} hte_class hte_mark hte_left hte_right)
		# cmp = (module_name,module_ident_class) =< (id_name,hte_class)
		| cmp == Equal
			# (IC_Module old_qualified_idents) = hte_class
			  ident_class = IC_Module (QualifiedIdents ident.boxed_ident ident_class old_qualified_idents)
			= (hte_ident, old_qualified_idents, hte_symbol_heap, HTE_Ident hte_ident ident_class (hte_mark bitand hte_mark0) hte_left hte_right)
		| cmp == Smaller
			#! (boxed_ident, qualified_idents, hte_symbol_heap, hte_left) = insert module_name ident ident_class module_ident_class hte_mark0 hte_symbol_heap hte_left
			= (boxed_ident, qualified_idents, hte_symbol_heap, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)
			#! (boxed_ident, qualified_idents, hte_symbol_heap, hte_right) = insert module_name ident ident_class module_ident_class hte_mark0 hte_symbol_heap hte_right
			= (boxed_ident, qualified_idents, hte_symbol_heap, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)

	insert_module_with_qualified_idents :: !String !IdentClass !*SymbolTable *HashTableEntry -> (!*SymbolTable, !*HashTableEntry)
	insert_module_with_qualified_idents name ident_class hte_symbol_heap HTE_Empty
		# (hte_symbol_ptr, hte_symbol_heap) = newPtr EmptySymbolTableEntry hte_symbol_heap
		  ident = { id_name = name, id_info = hte_symbol_ptr}
		  boxed_ident={boxed_ident=ident}
		= (hte_symbol_heap, HTE_Ident boxed_ident ident_class 0 HTE_Empty HTE_Empty)
	insert_module_with_qualified_idents name ident_class hte_symbol_heap hte=:(HTE_Ident hte_ident=:{boxed_ident={id_name}} hte_class hte_mark hte_left hte_right)
		# cmp = (name,ident_class) =< (id_name,hte_class)
		| cmp == Equal
			= (hte_symbol_heap, hte)
		| cmp == Smaller
			#! (hte_symbol_heap, hte_left) = insert_module_with_qualified_idents name ident_class hte_symbol_heap hte_left
			= (hte_symbol_heap, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)
			#! (hte_symbol_heap, hte_right) = insert_module_with_qualified_idents name ident_class hte_symbol_heap hte_right
			= (hte_symbol_heap, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)

putPredefinedIdentInHashTable :: !Ident !IdentClass !*HashTable -> *HashTable
putPredefinedIdentInHashTable predefined_ident=:{id_name} ident_class {hte_symbol_heap,hte_entries,hte_mark}
	# hash_val = hashValue id_name
	  (entries,hte_entries) = hte_entries![hash_val]
	  (hte_symbol_heap, entries) = insert id_name ident_class hte_mark hte_symbol_heap entries
	  hte_entries = {hte_entries & [hash_val]=entries}
	= { hte_symbol_heap = hte_symbol_heap, hte_entries = hte_entries,hte_mark=hte_mark }
where
	insert ::  !String !IdentClass !Int !*SymbolTable *HashTableEntry -> (!*SymbolTable, !*HashTableEntry)
	insert name ident_class hte_mark0 hte_symbol_heap HTE_Empty
		# hte_symbol_heap = writePtr predefined_ident.id_info EmptySymbolTableEntry hte_symbol_heap
		# boxed_ident={boxed_ident=predefined_ident}
		= (hte_symbol_heap, HTE_Ident boxed_ident ident_class hte_mark0 HTE_Empty HTE_Empty)
	insert name ident_class hte_mark0 hte_symbol_heap (HTE_Ident hte_ident=:{boxed_ident={id_name,id_info}} hte_class hte_mark hte_left hte_right)
		# cmp = (name,ident_class) =< (id_name,hte_class)
		| cmp == Equal
			= (hte_symbol_heap, HTE_Ident hte_ident hte_class (hte_mark bitand hte_mark0) hte_left hte_right)
		| cmp == Smaller
			#! (hte_symbol_heap, hte_left) = insert name ident_class hte_mark0 hte_symbol_heap hte_left
			= (hte_symbol_heap, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)
			#! (hte_symbol_heap, hte_right) = insert name ident_class hte_mark0 hte_symbol_heap hte_right
			= (hte_symbol_heap, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)

get_qualified_idents_from_hash_table :: !Ident !*HashTable -> (!QualifiedIdents,!*HashTable)
get_qualified_idents_from_hash_table module_ident=:{id_name} hash_table=:{hte_entries}
	# hash_val = hashValue id_name
	  (entries,hte_entries) = hte_entries![hash_val]
	  (qualified_idents, entries) = find_qualified_idents id_name (IC_Module NoQualifiedIdents) entries
	  hte_entries = {hte_entries & [hash_val] = entries}
	= (qualified_idents, {hash_table & hte_entries = hte_entries})
where
	find_qualified_idents :: !String !IdentClass *HashTableEntry -> (!QualifiedIdents, !*HashTableEntry)
	find_qualified_idents module_name module_ident_class hte=:(HTE_Ident hte_ident=:{boxed_ident={id_name}} hte_class hte_mark hte_left hte_right)
		# cmp = (module_name,module_ident_class) =< (id_name,hte_class)
		| cmp == Equal
			# (IC_Module qualified_idents) = hte_class
			= (qualified_idents, hte)
		| cmp == Smaller
			#! (qualified_idents, hte_left) = find_qualified_idents module_name module_ident_class hte_left
			= (qualified_idents, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)
			#! (qualified_idents, hte_right) = find_qualified_idents module_name module_ident_class hte_right
			= (qualified_idents, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)

remove_qualified_idents_from_hash_table :: !*HashTable -> *HashTable
remove_qualified_idents_from_hash_table hash_table=:{hte_entries}
	# (modules_with_qualified_idents,hte_entries) = hte_entries![ModulesWithQualifiedIdentsHashTableIndex]
	  (modules_with_qualified_idents,module_names) = get_module_names modules_with_qualified_idents [#!]
	  hte_entries & [ModulesWithQualifiedIdentsHashTableIndex] = modules_with_qualified_idents
	  hte_entries = remove_qualified_idents_from_modules module_names (IC_Module NoQualifiedIdents) hte_entries
	= {hash_table & hte_entries = hte_entries}
	where
		get_module_names :: !*HashTableEntry ![#{#Char}!] -> (!*HashTableEntry,![#{#Char}!]);
		get_module_names (HTE_Ident hte_ident=:{boxed_ident={id_name}} hte_class=:(IC_Module NoQualifiedIdents) hte_mark hte_left hte_right) module_names
			# module_names = [#id_name:module_names!]
			  (hte_left,module_names) = get_module_names hte_left module_names
			  (hte_right,module_names) = get_module_names hte_right module_names
			= (HTE_Ident hte_ident hte_class hte_mark hte_left hte_right,module_names)
		get_module_names HTE_Empty module_names
			= (HTE_Empty,module_names)

		remove_qualified_idents_from_modules :: [#{#Char}!] IdentClass !*{!*HashTableEntry} -> *{!*HashTableEntry};
		remove_qualified_idents_from_modules [#id_name:module_name!] hte_class hte_entries
			# hash_val = hashValue id_name
			  (entries,hte_entries) = hte_entries![hash_val]
			  (_,entries) = remove_qualified_idents_from_module id_name hte_class entries
			  hte_entries & [hash_val] = entries
			= remove_qualified_idents_from_modules module_name hte_class hte_entries
		remove_qualified_idents_from_modules [#!] hte_class hte_entries
			= hte_entries

		remove_qualified_idents_from_module :: !String !IdentClass *HashTableEntry -> (!Bool, !*HashTableEntry)
		remove_qualified_idents_from_module module_name module_ident_class (HTE_Ident hte_ident=:{boxed_ident={id_name}} hte_class hte_mark hte_left hte_right)
			# cmp = (module_name,module_ident_class) =< (id_name,hte_class)
			| cmp == Equal
				= (True, HTE_Ident hte_ident (IC_Module NoQualifiedIdents) hte_mark hte_left hte_right)
			| cmp == Smaller
				#! (found, hte_left) = remove_qualified_idents_from_module module_name module_ident_class hte_left
				= (found, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)
				#! (found, hte_right) = remove_qualified_idents_from_module module_name module_ident_class hte_right
				= (found, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)
		remove_qualified_idents_from_module module_name module_ident_class HTE_Empty
			= (False, HTE_Empty)

remove_icl_symbols_from_hash_table :: !*HashTable -> *HashTable
remove_icl_symbols_from_hash_table hash_table=:{hte_entries}
	# hte_entries=remove_icl_symbols_from_array 0 hte_entries
	= {hash_table & hte_entries=hte_entries}
	where
		remove_icl_symbols_from_array i hte_entries
			 | i<cHashTableSize
			 	# (entries,hte_entries) = hte_entries![i]
				# (_,entries) = remove_icl_entries_from_tree entries
				# hte_entries = {hte_entries & [i] = entries}
				= remove_icl_symbols_from_array (i+1) hte_entries
				= hte_entries

		// a tuple with a dummy value is used to change the calling convention to improve reuse of nodes
		remove_icl_entries_from_tree :: !*HashTableEntry -> (!Int,!.HashTableEntry);
		remove_icl_entries_from_tree HTE_Empty
			= (0,HTE_Empty)
		remove_icl_entries_from_tree (HTE_Ident hte_ident hte_class 0 hte_left hte_right)
			# (_,hte_left) = remove_icl_entries_from_tree hte_left
			# (_,hte_right) = remove_icl_entries_from_tree hte_right
			= (0,HTE_Ident hte_ident hte_class 0 hte_left hte_right)
		remove_icl_entries_from_tree (HTE_Ident hte_ident hte_class _ hte_left hte_right)
			# (depth_left,hte_left) = remove_icl_entries_from_tree_and_compute_depth hte_left
			# (depth_right,hte_right) = remove_icl_entries_from_tree_and_compute_depth hte_right
			= merge_trees hte_left hte_right depth_left depth_right

		remove_icl_entries_from_tree_and_compute_depth :: !*HashTableEntry -> (!Int,!.HashTableEntry);
		remove_icl_entries_from_tree_and_compute_depth HTE_Empty
			= (0,HTE_Empty)
		remove_icl_entries_from_tree_and_compute_depth (HTE_Ident hte_ident hte_class 0 hte_left hte_right)
			# (depth_left,hte_left) = remove_icl_entries_from_tree_and_compute_depth hte_left
			# (depth_right,hte_right) = remove_icl_entries_from_tree_and_compute_depth hte_right
			= (if (depth_left>=depth_right) depth_left depth_right,HTE_Ident hte_ident hte_class 0 hte_left hte_right)
		remove_icl_entries_from_tree_and_compute_depth (HTE_Ident hte_ident hte_class _ hte_left hte_right)
			# (depth_left,hte_left) = remove_icl_entries_from_tree_and_compute_depth hte_left
			# (depth_right,hte_right) = remove_icl_entries_from_tree_and_compute_depth hte_right
			= merge_trees hte_left hte_right depth_left depth_right
		
		// the returned depth is an estimate
		merge_trees :: !*HashTableEntry !*HashTableEntry !Int !Int -> (!Int,!.HashTableEntry)
		merge_trees HTE_Empty hte_right depth_left depth_right
			= (depth_right,hte_right)
		merge_trees hte_left HTE_Empty depth_left depth_right
			= (depth_left,hte_left)
		merge_trees hte_left hte_right depth_left depth_right
			| depth_left>=depth_right
				= merge_trees_left hte_left hte_right depth_left depth_right
				= merge_trees_right hte_left hte_right depth_left depth_right
		where
				merge_trees_left :: !*HashTableEntry !*HashTableEntry !Int !Int -> (!Int,!.HashTableEntry)
				merge_trees_left (HTE_Ident hte_ident hte_class hte_mark hte_left_left hte_left_right) hte_right depth_left depth_right
					# (depth_right,hte_right)=merge_trees hte_left_right hte_right (depth_left-1) depth_right
					# depth_right=depth_right+1
					= (if (depth_left>=depth_right) depth_left depth_right,HTE_Ident hte_ident hte_class hte_mark hte_left_left hte_right)

				merge_trees_right :: !*HashTableEntry !*HashTableEntry !Int !Int -> (!Int,!.HashTableEntry)
				merge_trees_right hte_left (HTE_Ident hte_ident hte_class hte_mark hte_right_left hte_right_right) depth_left depth_right
					# (depth_left,hte_left)=merge_trees hte_left hte_right_left depth_left (depth_right-1)
					# depth_left=depth_left+1
					= (if (depth_left>=depth_right) depth_left depth_right,HTE_Ident hte_ident hte_class hte_mark hte_left hte_right_right)
