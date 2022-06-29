implementation module coclmain

import StdEnv
import set_return_code
import CoclSystemDependent

import compile

coclMain :: !*World -> *World
coclMain world
	# world
		=	set_return_code 0 world
	# (symbol_table,world)
		= init_identifiers newHeap world
	# (success, world)
		=	accFiles (compiler symbol_table) world
	=	set_return_code (if success 0(-1)) world

// Unix
compile2 args (cache, files)
	# (r, cache, files)
		=	compile args cache files
	= (r, (cache, files))

compiler symbol_table files
	# dcl_cache = empty_cache symbol_table
	# (r,(_,files))
		=	compiler_loop compile2 (dcl_cache, files)
	= (r, files)
