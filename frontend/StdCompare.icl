implementation module StdCompare

import StdEnv, compare_constructor
import syntax

instance == TypeVar
where
	(==) varid1 varid2 = varid1.tv_name == varid2.tv_name

instance == FunKind
where
	(==) fk1 fk2 = equal_constructor fk1 fk2

instance == Global a | == a
where
	(==) g1 g2
		= g1.glob_module == g2.glob_module && g1.glob_object == g2.glob_object


instance == TypeSymbIdent
where
	(==) tsymb_id1 tsymb_id2
		= tsymb_id1.type_index == tsymb_id2.type_index


instance == AType
where
	(==) atype1 atype2 = atype1.at_type == atype2.at_type

instance == ConsVariable
where
	(==) (CV tv1) (CV tv2)			= tv1 == tv2
	(==) (TempCV tv1) (TempCV tv2)	= tv1 == tv2
	(==) cv1 cv2					= False


instance == TypeContext
where
 (==) tc1 tc2 = tc1.tc_class == tc2.tc_class && tc1.tc_types == tc2.tc_types

instance == BasicType
where
	(==) bt1 bt2 = equal_constructor bt1 bt2

instance == BasicValue
where
	(==) (BVI int1) (BVI int2)			= int1 == int2
	(==) (BVC char1) (BVC char2)		= char1 == char2
	(==) (BVB bool1) (BVB bool2)		= bool1 == bool2
	(==) (BVR real1) (BVR real2)		= real1 == real2
	(==) (BVS string1) (BVS string2)	= string1 == string2
	(==) _ _							= False
			
instance == DefinedSymbol
where
	(==) ds1 ds2
		= ds1.ds_ident == ds2.ds_ident && ds1.ds_index == ds2.ds_index

instance == Type
where
	(==) t1 t2 = equal_constructor t1 t2 && equal_constructor_args t1 t2
	where
		equal_constructor_args (TV varid1) (TV varid2)
			= varid1 == varid2
		equal_constructor_args (TempV varid1) (TempV varid2)
			= varid1 == varid2
		equal_constructor_args (arg_type1 --> restype1) (arg_type2 --> restype2)
			= arg_type1 == arg_type2 && restype1 == restype2
		equal_constructor_args (TA tc1 types1) (TA tc2 types2)
			= tc1 == tc2 && types1 == types2
		equal_constructor_args (TB tb1) (TB tb2)
			= tb1 == tb2
		equal_constructor_args (TA tc1 types1) (TA tc2 types2)
			= tc1 == tc2 && types1 == types2
		equal_constructor_args (type1 :@: types1) (type2 :@: types2)
			= type1 == type2 && types1 == types2
		equal_constructor_args (TQV varid1) (TQV varid2)
			= varid1 == varid2
		equal_constructor_args type1 type2
			= True

::	CompareValue :== Int
Smaller :== -1
Greater	:== 1
Equal	:== 0

class (=<) infix 4 a :: !a !a -> CompareValue

instance =< Int
where
	(=<) i1 i2
		| i1 == i2
			= Equal
		| i1 < i2
			= Smaller
			= Greater

instance =< SymbKind
where
	(=<) symb1 symb2
		| equal_constructor symb1 symb2
			= compare_indexes  symb1 symb2
		with
			compare_indexes (SK_Function i1) (SK_Function i2)						= i1 =< i2
//			compare_indexes (SK_ClassRecord i1) (SK_ClassRecord i2)					= i1 =< i2
			compare_indexes (SK_Constructor i1) (SK_Constructor i2)					= i1 =< i2
//			compare_indexes (SK_DeltaFunction i1) (SK_DeltaFunction i2)				= i1 =< i2
//			compare_indexes (SK_InternalFunction i1) (SK_InternalFunction i2)		= i1 =< i2
			compare_indexes (SK_OverloadedFunction i1) (SK_OverloadedFunction i2)	= i1 =< i2
			compare_indexes (SK_GeneratedFunction _ i1) (SK_GeneratedFunction _ i2)	= i1 =< i2

		| less_constructor symb1 symb2
			= Smaller
			= Greater

instance =< SymbIdent
where
	(=<) {symb_kind=symb_kind1} {symb_kind=symb_kind2} = symb_kind1 =< symb_kind2
			

instance =< App
where
	(=<) app1 app2
		# cmp = app1.app_symb =< app2.app_symb
		| cmp == Equal
			= app1.app_args =< app2.app_args
			= cmp

instance =< (a,b) | =< a & =< b
where
	(=<) (x1,y1) (x2,y2)
		# cmp = x1 =< x2
		| cmp == Equal
			= y1 =< y2
			= cmp
	
instance =< [a] | =< a
where
	(=<) [x:xs] [y:ys]	= (x,xs) =< (y,ys)
	(=<) [] []			= Equal
	(=<) [] _			= Smaller
	(=<) _ _			= Greater

instance =< {# Char}
where
	(=<) s1 s2
		| s1 == s2
			= Equal
		| s1 < s2
			= Smaller
			= Greater
	
instance =< Expression
where
	(=<) expr1 expr2
		| equal_constructor expr1 expr2
			= compare_arguments  expr1 expr2
		with
			compare_arguments (App app1) (App app2)						= app1 =< app2
			compare_arguments (Var v1) (Var v2)							= v1 =< v2
			compare_arguments (fun1 @ args1) (fun2 @ args2)				= (fun1,args1) =< (fun2,args2) 
			compare_arguments (Lambda vars1 expr1) (Lambda vars2 expr2)	= (vars1,expr1) =< (vars2,expr2)
			compare_arguments EE EE										= Equal		
			compare_arguments _ _										= Greater		
		| less_constructor expr1 expr2
			= Smaller
			= Greater

instance =< BoundVar
where
	(=<) bv1 bv2
		= bv1.var_name =< bv2.var_name
	
instance =< FreeVar
where
	(=<) fv1 fv2
		= fv1.fv_name =< fv2.fv_name
	
instance =< Ident
where
	(=<) id1 id2
		= id1.id_name =< id2.id_name

instance =< Global a | =< a
where
	(=<) g1 g2
		= (g1.glob_module,g1.glob_object) =< (g2.glob_module,g2.glob_object)

instance =< TypeSymbIdent
where
	(=<) s1 s2
		= s1.type_name =< s2.type_name

instance =< Type
where
	(=<) t1 t2
		| equal_constructor t1 t2
			= compare_arguments t1 t2
		| less_constructor t1 t2
			= Smaller
			= Greater
	where
		compare_arguments (TB tb1) (TB tb2)		= tb1 =< tb2 
		compare_arguments (TA tc1 _) (TA tc2 _)	= tc1 =< tc2
		compare_arguments _ _					= Equal

instance =< BasicType
where
	(=<) bt1 bt2
		| equal_constructor bt1 bt2
			= Equal
		| less_constructor bt1 bt2
			= Smaller
			= Greater

instance < MemberDef
where
	(<) md1 md2 = md1.me_symb.id_name < md2.me_symb.id_name

