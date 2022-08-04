implementation module coclmain

import StdEnv
import set_return_code
import CoclSystemDependent

import compile

coclMain :: !*VarHeap !*ExpressionHeap !*TypeVarHeap !*AttrVarHeap !*GenericHeap !*FunctionHeap !*KindHeap !*SymbolTable !*World -> *World
coclMain var_heap expression_heap type_var_heap attr_var_heap generic_heap function_heap kind_heap symbol_table world
	# world
		=	set_return_code 0 world
	# (symbol_table,world)
		= init_identifiers symbol_table world
	# (success, world)
		=	accFiles (compiler var_heap expression_heap type_var_heap attr_var_heap generic_heap function_heap kind_heap symbol_table) world
	=	set_return_code (if success 0(-1)) world

// Unix
compile2 args (cache, files)
	# (r, cache, files)
		=	compile args cache files
	= (r, (cache, files))

compiler var_heap expression_heap type_var_heap attr_var_heap generic_heap function_heap kind_heap symbol_table files
	# dcl_cache = empty_cache var_heap expression_heap type_var_heap attr_var_heap generic_heap function_heap kind_heap symbol_table
	# (r,(_,files))
		=	compiler_loop compile2 (dcl_cache, files)
	= (r, files)
