definition module containers

/*2.0
from syntax import ::Optional,::StrictnessList,::Annotation
from StdOverloaded import class toString
0.2*/
//1.3
from syntax import Optional,StrictnessList,Annotation
from StdOverloaded import toString
//3.1

:: NumberSet = Numbers !Int !NumberSet | EndNumbers

addNr :: !Int !NumberSet -> NumberSet
inNumberSet :: !Int !NumberSet -> Bool
numberSetUnion :: !NumberSet !NumberSet -> NumberSet
nsFromTo :: !Int -> NumberSet
	// all numbers from 0 to (i-1)
bitvectToNumberSet :: !LargeBitvect -> .NumberSet

:: LargeBitvect :== {#Int}

bitvectCreate :: !Int -> .LargeBitvect 
bitvectSelect :: !Int !LargeBitvect -> Bool
bitvectSet :: !Int !*LargeBitvect -> .LargeBitvect 
bitvectReset :: !Int !*LargeBitvect -> .LargeBitvect
bitvectSetFirstN :: !Int !*LargeBitvect -> .LargeBitvect 
bitvectResetAll :: !*LargeBitvect -> .LargeBitvect 

add_strictness :: !Int !StrictnessList -> StrictnessList
first_n_strict :: !Int -> StrictnessList
insert_n_strictness_values_at_beginning :: !Int !StrictnessList -> StrictnessList
insert_n_lazy_values_at_beginning :: !Int !StrictnessList -> StrictnessList
arg_strictness_annotation :: !Int !StrictnessList -> Annotation;
arg_is_strict :: !Int !StrictnessList -> Bool;
is_not_strict :: !StrictnessList -> Bool
equal_strictness_lists :: !StrictnessList !StrictnessList -> Bool
add_next_strict :: !Int !Int !StrictnessList -> (!Int,!Int,!StrictnessList)
add_next_not_strict :: !Int !Int !StrictnessList -> (!Int,!Int,!StrictnessList)
append_strictness :: !Int !StrictnessList -> StrictnessList

:: IntKey :== Int

:: IntKeyHashtable a = IntKeyHashtable !Int !Int !Int !.{!.IntKeyTree a}
	
:: IntKeyTree a = IKT_Leaf | IKT_Node !IntKey a !.(IntKeyTree a) !.(IntKeyTree a)

ikhEmpty :: .(IntKeyHashtable a)
ikhInsert :: !Bool !IntKey a !*(IntKeyHashtable a) -> (!Bool, !.IntKeyHashtable a)
	// input bool: overide old value, output bool: a new element was inserted
ikhInsert` :: !Bool !IntKey a !*(IntKeyHashtable a) -> .IntKeyHashtable a
	// bool: overide old value
ikhSearch :: !IntKey !(IntKeyHashtable a) -> .Optional a
ikhSearch` :: !IntKey !(IntKeyHashtable a) -> a
ikhUSearch :: !IntKey !*(IntKeyHashtable a) -> (!.Optional a, !*IntKeyHashtable a)

iktUInsert :: !Bool !IntKey a !*(IntKeyTree a) -> (!Bool, !.IntKeyTree a)
	// input bool: overide old value, output bool: a new element was inserted
iktFlatten :: !(IntKeyTree a) -> [(IntKey, a)]
iktSearch :: !IntKey !(IntKeyTree a) -> .Optional a
iktSearch` :: !IntKey !(IntKeyTree a) -> a
iktUSearch :: !IntKey !*(IntKeyTree a) -> (!.Optional a,!.IntKeyTree a)

instance toString (IntKeyTree a) | toString a, (IntKeyHashtable a) | toString a
