definition module partition

import syntax, checksupport

partitionateFunctions :: !*{# FunDef} ![IndexRange] -> (!*{!Component}, !*{# FunDef})

partitionateFunctions` :: !*{#FunDef} ![IndexRange] !Index !Int !Int !*PredefinedSymbols !*VarHeap !*ExpressionHeap !*ErrorAdmin
									  -> (!*{!Component},!*{#FunDef},!*PredefinedSymbols,!*VarHeap,!*ExpressionHeap,!*ErrorAdmin)

partitionateFunctions`` :: !Int !Int !*{#FunDef} !ComponentMembers !Index !Int !Int !*FunctionHeap !*PredefinedSymbols !*VarHeap !*ExpressionHeap !*ErrorAdmin
												  -> (!Int,![Component],!*{#FunDef},!*FunctionHeap,!*PredefinedSymbols,!*VarHeap,!*ExpressionHeap,!*ErrorAdmin)
