definition module typesupport

import checksupport, StdCompare

/*2.0
from unitype import ::Coercions, ::CoercionTree, ::AttributePartition, CT_Empty
0.2*/
//1.3
from unitype import Coercions, CoercionTree, AttributePartition, CT_Empty
//3.1

errorHeading :: !String !*ErrorAdmin -> *ErrorAdmin

// MW4 was:class (<::) infixl a :: !*File (!Format, !a) -> *File
(<::) infixl :: !*File (!Format, !a, !Optional TypeVarBeautifulizer) -> *File | writeType a

class writeType a :: !*File !(Optional TypeVarBeautifulizer) (!Format, !a) -> (!*File, !Optional TypeVarBeautifulizer)

:: Format =
	{	form_properties 	:: !BITVECT
	,	form_attr_position	:: Optional ([Int], Coercions)
	}

cNoProperties		:== 0
cAttributed			:== 1
cAnnotated			:== 2
cMarkAttribute		:== 4

:: TypeVarBeautifulizer // MW++

instance writeType SymbolType, Type, AType, [a] | writeType a

initialTypeVarBeautifulizer :: TypeVarBeautifulizer // MW4++

::	AttributeEnv	:== {! TypeAttribute }
::	VarEnv 			:== {! Type }

cleanSymbolType :: !Int !*TypeHeaps -> (!SymbolType, !*TypeHeaps)
extendSymbolType :: !SymbolType !Int !*TypeHeaps -> (!SymbolType, !*TypeHeaps)

cSpecifiedType	:== True
cDerivedType	:== False

cleanUpSymbolType :: !Bool !Bool !TempSymbolType ![TypeContext] ![ExprInfoPtr] !{! CoercionTree} !AttributePartition
						!*VarEnv !*AttributeEnv !*TypeHeaps !*VarHeap !*ExpressionHeap !*ErrorAdmin
							-> (!SymbolType, !*VarEnv, !*AttributeEnv, !*TypeHeaps, !*VarHeap, !*ExpressionHeap, !*ErrorAdmin)

equivalent :: !SymbolType !TempSymbolType !Int !{# CommonDefs} !*AttributeEnv !*TypeHeaps -> (!Bool, !*AttributeEnv, !*TypeHeaps) 

NewAttrVarId :: !Int -> Ident

beautifulizeAttributes :: !SymbolType !*AttrVarHeap -> (!SymbolType, !.AttrVarHeap)

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
	,	tst_attr_env	:: ![AttrCoercion]
	}

::	FunctionType = CheckedType !SymbolType | SpecifiedType !SymbolType ![AType] !TempSymbolType
				 | UncheckedType !TempSymbolType | ExpandedType !SymbolType !TempSymbolType !TempSymbolType  | EmptyFunctionType


updateExpressionTypes :: !SymbolType !SymbolType ![ExprInfoPtr] !*TypeHeaps !*ExpressionHeap -> (!*TypeHeaps, !*ExpressionHeap)

class substitute a :: !a !*TypeHeaps -> (!Bool, !a, !*TypeHeaps)

instance substitute AType, Type, TypeContext, AttrInequality, CaseType, [a] | substitute a,
			(a,b) | substitute a & substitute b

substituteType :: !TypeAttribute !TypeAttribute ![ATypeVar] ![AType] !Type !*TypeHeaps -> (!Bool, !Type, !*TypeHeaps)

bindTypeVarsAndAttributes :: !TypeAttribute !TypeAttribute ![ATypeVar] ![AType] !*TypeHeaps -> *TypeHeaps;
clearBindingsOfTypeVarsAndAttributes :: !TypeAttribute ![ATypeVar] !*TypeHeaps -> *TypeHeaps;

instance <<< TempSymbolType

removeInequality :: !Int !Int !*Coercions -> .Coercions
flattenCoercionTree :: !u:CoercionTree -> (![Int], !u:CoercionTree)
	// retrieve all numbers from a coercion tree
assignNumbersToAttrVars :: !SymbolType !*AttrVarHeap -> (!Int, ![AttributeVar], !.AttrVarHeap)
	// returns the number and a list of all attribute variables
getImplicitAttrInequalities :: !SymbolType -> [AttrInequality]
	// retrieve those inequalities that are implied by propagation
emptyCoercions :: !Int -> .Coercions
	// Int: nr of attribute variables
addAttrEnvInequalities :: ![AttrInequality] !*Coercions !u:AttrVarHeap
						-> (!.Coercions, !u:AttrVarHeap)
	// assertion: the attribute variables point to (AVI_Attr (TA_TempVar nr)) where
	// nr corresponds to the attribute variable
optBeautifulizeIdent :: !String -> Optional (!String, !LineNr)
	// convert something like "c;8;2" to Yes ("comprehension", 8)
removeUnusedAttrVars :: !{!CoercionTree} ![Int] -> Coercions
	
//accCoercionTree :: !.(u:CoercionTree -> (.a,u:CoercionTree)) !Int !*{!u:CoercionTree} -> (!.a,!{!u:CoercionTree})
accCoercionTree f i coercion_trees
	:== acc_coercion_tree i coercion_trees
  where
	acc_coercion_tree i coercion_trees
		# (coercion_tree, coercion_trees) = replace coercion_trees i CT_Empty
		  (x, coercion_tree) = f coercion_tree
		= (x, snd (replace coercion_trees i coercion_tree))
	
//accCoercionTree :: !.(u:CoercionTree -> u:CoercionTree) !Int !*{!u:CoercionTree} -> {!u:CoercionTree}
appCoercionTree f i coercion_trees
	:== acc_coercion_tree i coercion_trees
  where
	acc_coercion_tree i coercion_trees
		# (coercion_tree, coercion_trees) = replace coercion_trees i CT_Empty
		= snd (replace coercion_trees i (f coercion_tree))
	
class performOnTypeVars a :: !(TypeAttribute TypeVar .st -> .st) !a !.st -> .st
// run through a type and do something on each type variable

instance performOnTypeVars Type, AType, ConsVariable, [a] | performOnTypeVars a,
		(a, b) | performOnTypeVars a & performOnTypeVars b

getTypeVars :: !a !*TypeVarHeap -> (!.[TypeVar],!.TypeVarHeap) | performOnTypeVars a

class performOnAttrVars a :: !(AttributeVar .st -> .st) !a !.st -> .st
// run through a type and do something on each attribute variable

getAttrVars :: !a !*AttrVarHeap -> (!.[AttributeVar],!.AttrVarHeap) | performOnAttrVars a

instance performOnAttrVars Type, AType, [a] | performOnAttrVars a,
		(a, b) | performOnAttrVars a & performOnAttrVars b

initializeToTVI_Empty :: a !TypeVar !*TypeVarHeap -> .TypeVarHeap
initializeToAVI_Empty :: !AttributeVar !*AttrVarHeap -> .AttrVarHeap

appTypeVarHeap f type_heaps :== let th_vars = f type_heaps.th_vars in { type_heaps & th_vars = th_vars }
accTypeVarHeap f type_heaps :== let (r, th_vars) = f type_heaps.th_vars in (r, { type_heaps & th_vars = th_vars })
accAttrVarHeap f type_heaps :== let (r, th_attrs) = f type_heaps.th_attrs in (r, { type_heaps & th_attrs = th_attrs })
	
class removeAnnotations a :: !a  -> (!Bool, !a)

instance removeAnnotations Type, SymbolType

foldATypeSt on_atype on_type type st :== fold_atype_st type st
  where
	fold_type_st type=:(TA type_symb_ident args) st
		#! st
				= foldSt fold_atype_st args st
		= on_type type st
	fold_type_st type=:(TAS type_symb_ident args _) st
		#! st
				= foldSt fold_atype_st args st
		= on_type type st
	fold_type_st type=:(l --> r) st
		#! st
				= fold_atype_st r (fold_atype_st l st)
		= on_type type st
//AA..
	fold_type_st type=:(TArrow1 t) st
		#! st = fold_atype_st t st
		= on_type type st	
//..AA
	fold_type_st type=:(_ :@: args) st
		#! st
				= foldSt fold_atype_st args st
		= on_type type st
	fold_type_st type st
		= on_type type st
	
	fold_atype_st atype=:{at_type} st
		#! st
				= fold_type_st at_type st
		= on_atype atype st

