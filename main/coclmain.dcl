definition module coclmain

from syntax import ::Heap,
	::VarHeap,::VarInfo,
	::ExpressionHeap,::ExprInfo,
	::TypeVarHeap,::TypeVarInfo,
	::AttrVarHeap,::AttrVarInfo,
	::GenericHeap,::GenericInfo,
	::FunctionHeap,::FunctionInfo,
	::KindHeap,::KindInfo,
	::SymbolTable,::SymbolTableEntry

coclMain :: !*VarHeap !*ExpressionHeap !*TypeVarHeap !*AttrVarHeap !*GenericHeap !*FunctionHeap !*KindHeap !*SymbolTable !*World -> *World
