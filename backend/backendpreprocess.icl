implementation module backendpreprocess

import checksupport
import Heap

backEndPreprocess :: !Ident ![Index] !IclModule !*VarHeap -> *VarHeap
backEndPreprocess aliasDummyId functionIndices iclModule varHeap
	= varHeap
