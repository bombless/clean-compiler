definition module Heap

import StdClass

:: Heap v hi = {heap::!.HeapN v}
:: .HeapN v
:: Ptr v hi = {pointer::!.(PtrN v)};
:: PtrN v = Ptr !v !(HeapN v);

newHeap		:: .Heap v hi

nilPtr		:: Ptr v hi

isNilPtr 	:: !(Ptr v hi) -> Bool

newPtr		:: !v !*(Heap v hi) -> (!.Ptr v hi,!.Heap v hi)

readPtr		:: !(Ptr v hi) !u:(Heap v hi) -> (!v,!u:Heap v hi)

writePtr	:: !(Ptr v hi) !v !*(Heap v hi) -> .Heap v hi

sreadPtr	:: !(Ptr v hi) !(Heap v hi) -> v

allocPtr :: Ptr v hi;

initPtr :: !(Ptr v hi) !v !*(Heap v hi) !*World -> (!.Heap v hi,!*World);

ptrToInt 	:: !(Ptr w hi) -> Int

(<:=) infixl 
(<:=) heap ptr_and_val :== writePtr ptr val heap 
where
	(ptr, val) = ptr_and_val

instance == (Ptr a hi)
