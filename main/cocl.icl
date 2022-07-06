module cocl

import coclmain
from Heap import newHeap

Start :: *World -> *World
Start world
	# symbol_table = newHeap
	  var_heap = newHeap
	  expression_heap = newHeap
	  type_var_heap = newHeap
	  attr_var_heap = newHeap
	  generic_heap = newHeap
	  function_heap = newHeap
	  kind_heap = newHeap
	= coclMain var_heap expression_heap type_var_heap attr_var_heap generic_heap function_heap kind_heap symbol_table world
