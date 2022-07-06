definition module compile

from StdFile import ::Files
import checksupport

compile :: ![{#Char}] !*DclCache !*Files -> (!Bool,!*DclCache,!*Files)

:: DclCache = {
	dcl_modules::!{#DclModule},
	functions_and_macros::!.{#.{#FunDef}},
	predef_symbols::!.PredefinedSymbols,
	hash_table::!.HashTable,
	function_heap :: !.FunctionHeap,
	kind_heap :: !.KindHeap,
	heaps::!.Heaps
 };

empty_cache :: !*VarHeap !*ExpressionHeap !*TypeVarHeap !*AttrVarHeap !*GenericHeap !*FunctionHeap !*KindHeap !*SymbolTable -> *DclCache
