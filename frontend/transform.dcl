definition module transform

import syntax, checksupport

::	Group =
	{	group_members	:: ![Int]
	}

:: PredefSymbolsForTransform = { predef_alias_dummy :: !PredefinedSymbol, predef_and :: !PredefinedSymbol, predef_or :: !PredefinedSymbol };

partitionateAndLiftFunctions :: ![IndexRange] !Index !PredefSymbolsForTransform !*{# FunDef} !*{# DclModule} !*VarHeap !*ExpressionHeap !*SymbolTable !*ErrorAdmin
	-> (!*{! Group}, !*{# FunDef}, !.{# DclModule}, !*VarHeap, !*ExpressionHeap,  !*SymbolTable, !*ErrorAdmin )

partitionateMacros :: !IndexRange !Index !PredefSymbolsForTransform !*{# FunDef} !*{# DclModule} !*VarHeap !*ExpressionHeap !*SymbolTable !*ErrorAdmin
	-> (!*{# FunDef}, !.{# DclModule}, !*VarHeap, !*ExpressionHeap, !*SymbolTable, !*ErrorAdmin )

::	CopiedLocalFunctions

// AA..

::	CollectState =
	{	cos_var_heap	:: !.VarHeap
	,	cos_symbol_heap :: !.ExpressionHeap
	,	cos_error		:: !.ErrorAdmin
	,	cos_predef_symbols_for_transform :: !PredefSymbolsForTransform
	,	cos_used_dynamics	:: !.{#Bool}
	}

determineVariablesAndRefCounts :: ![FreeVar] !Expression !*CollectState -> (!Expression , ![FreeVar], ![FreeVar], !*CollectState)

// ..AA

::	UnfoldState =
	{	us_var_heap				:: !.VarHeap
	,	us_symbol_heap			:: !.ExpressionHeap
	,	us_opt_type_heaps		:: !.Optional .TypeHeaps,
		us_cleanup_info			:: ![ExprInfoPtr],
		us_local_macro_functions :: !Optional CopiedLocalFunctions
	}

::	UnfoldInfo =
	{	ui_handle_aci_free_vars	:: !AciFreeVarHandleMode,
		ui_convert_module_n :: !Int, // -1 if no conversion
		ui_conversion_table :: !Optional ConversionTable
	}

:: AciFreeVarHandleMode = LeaveThem | RemoveThem | SubstituteThem

class unfold a :: !a !UnfoldInfo !*UnfoldState -> (!a, !*UnfoldState)
instance unfold Expression, CasePatterns
