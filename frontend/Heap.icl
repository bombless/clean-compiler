implementation module Heap;

import StdOverloaded,StdMisc;

:: Heap v hi = {heap::!.HeapN}; // _;
:: HeapN = Heap;
:: Ptr v  hi = {pointer::!.(PtrN v)};
:: PtrN v = Ptr !v | NilPtrN | AllocPtrN !();

// don't use anymore, used because Clean 3.1 does not support :: Type = _
newHeap :: .Heap v hi;
newHeap = {heap=Heap};

newPtr :: !v !*(Heap v hi) -> (!.Ptr v hi,!.Heap v hi);
newPtr v h = ({pointer=Ptr v},h);

nilPtr :: Ptr v hi;
nilPtr = {pointer=NilPtrN};

isNilPtr :: !(Ptr v hi) -> Bool;
isNilPtr {pointer} = pointer=:NilPtrN;

readPtr :: !(Ptr v hi) !u:(Heap v hi) -> (!v,!u:Heap v hi);
readPtr p h = code {
	eq_desc e_Heap_kPtr 0 0
	jmp_false read_heap_error
	repl_arg 1 1
.d 2 0
	rtn
:read_heap_error
	pop_a 1
	print "readPtr: nil or uninitialized pointer"
	halt
};

sreadPtr :: !(Ptr v hi) !(Heap v hi) -> v;
sreadPtr p h = code {
	eq_desc e_Heap_kPtr 0 0
	jmp_false sread_heap_error
	repl_arg 1 1
	updatepop_a 0 1
.d 1 0
	rtn
:sread_heap_error
	pop_a 1
	print "sreadPtr: nil or uninitialized pointer"
	halt
};

writePtr :: !(Ptr v hi) !v !*(Heap v hi) -> .Heap v hi;
writePtr p v h
 = code {
	eq_desc e_Heap_kPtr 0 0
	jmp_false write_heap_error
	push_a 1
	fill1_r e_Heap_kPtr 1 0 1 01
.keep 0 2
	pop_a 2
.d 1 0
	rtn
:write_heap_error
	pop_a 2
	print "writePtr: nil or uninitialized pointer"
	halt
};

allocPtr :: Ptr v hi;
allocPtr = {pointer=AllocPtrN ()};

initPtr :: !(Ptr v hi) !v !*(Heap v hi) !*World -> (!.Heap v hi,!*World);
initPtr p v h w
 = code {
	eq_desc e_Heap_kAllocPtrN 0 0
	jmp_false init_pointer_error
	push_a 1
	fill1_r e_Heap_kPtr 1 0 1 11
.keep 0 2
	pop_a 2
.d 2 0
	rtn
:init_pointer_error
	pop_a 3
	print "initPtr: Pointer already initialized"
	halt
};

(<:=) infixl;
(<:=) heap ptr_and_val :== writePtr ptr val heap ;
{
	(ptr, val) = ptr_and_val;
}

ptrToInt :: !(Ptr v h) -> Int;
ptrToInt p = code {
	eq_desc e_Heap_dNilPtrN 0 0
	jmp_true nil
	push_a_b 0
	pop_a 1
.d 0 1 i
	rtn
:nil
	pop_a 1
	pushI 0
.d 0 1 i
	rtn	
};

instance == (Ptr a hi)
where
{	(==) p1 p2 = code {
	push_a_b 1
	push_a_b 0
	pop_a 2
	eqI
.d 0 1 b
	rtn	
}
};
