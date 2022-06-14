definition module predef

import syntax, hashtable

::	PredefinedSymbols	:== {# PredefinedSymbol}

::	PredefinedSymbol = {
		pds_module	:: !Index,
		pds_def		:: !Index
	}

init_identifiers :: !*SymbolTable !*World -> (!*SymbolTable,!*World)

predefined_idents :: {!Ident}

buildPredefinedSymbols :: !*HashTable -> (!.PredefinedSymbols,!*HashTable)

buildPredefinedModule :: !Bool !*PredefinedSymbols -> (!ScannedModule, !.PredefinedSymbols)

PredefinedModuleIndex :== 1
cPredefinedModuleIndex :== 1

// index in com_type_defs

PD_StringTypeIndex :== 0

PD_ListTypeIndex :== 1
PD_StrictListTypeIndex :== 2
PD_UnboxedListTypeIndex :== 3
PD_TailStrictListTypeIndex :== 4
PD_StrictTailStrictListTypeIndex :== 5
PD_UnboxedTailStrictListTypeIndex :== 6
//PD_OverloadedListTypeIndex :== 7

PD_Arity2TupleTypeIndex :== 8
PD_Arity32TupleTypeIndex :== 38

PD_LazyArrayTypeIndex :== 39
PD_StrictArrayTypeIndex :== 40
PD_UnboxedArrayTypeIndex :== 41
PD_PackedArrayTypeIndex :== 42

PD_LazyArrayP2TypeIndex :== 43
PD_StrictArrayP2TypeIndex :== 44
PD_UnboxedArrayP2TypeIndex :== 45
PD_PackedArrayP2TypeIndex :== 46

PD_MaybeTypeIndex :== 47
PD_StrictMaybeTypeIndex :== 48
PD_UnboxedMaybeTypeIndex :== 49
//PD_OverloadedMaybeTypeIndex :== 50

PD_UnitTypeIndex :== 51

/* identifiers not present the hashtable */

PD_PredefinedModule			:== 0

FirstTypePredefinedSymbolIndex:==PD_StringType; // to compute index in com_type_defs

PD_StringType				:== 1

PD_ListType :== 2
PD_StrictListType :== 3
PD_UnboxedListType :== 4
PD_TailStrictListType :== 5
PD_StrictTailStrictListType :== 6
PD_UnboxedTailStrictListType :== 7
PD_OverloadedListType :== 8

PD_Arity2TupleType			:== 9
PD_Arity32TupleType			:== 39

PD_LazyArrayType			:== 40
PD_StrictArrayType			:== 41
PD_UnboxedArrayType			:== 42
PD_PackedArrayType			:== 43

PD_LazyArrayP2Type			:== 44
PD_StrictArrayP2Type		:== 45
PD_UnboxedArrayP2Type		:== 46
PD_PackedArrayP2Type		:== 47

// same order as in MaybeIdentToken
PD_MaybeType :== 48
PD_StrictMaybeType :== 49
PD_UnboxedMaybeType :== 50
PD_OverloadedMaybeType :== 51

PD_UnitType :== 52

// constructors:

FirstConstructorPredefinedSymbolIndex :== PD_ConsSymbol; // to compute index in com_cons_defs

PD_ConsSymbol :== 53
PD_StrictConsSymbol :== 54
PD_UnboxedConsSymbol :== 55
PD_TailStrictConsSymbol :== 56
PD_StrictTailStrictConsSymbol :== 57
PD_UnboxedTailStrictConsSymbol :== 58
PD_OverloadedConsSymbol :== 59

PD_NilSymbol :== 60
PD_StrictNilSymbol :== 61
PD_UnboxedNilSymbol :== 62
PD_TailStrictNilSymbol :== 63
PD_StrictTailStrictNilSymbol :== 64
PD_UnboxedTailStrictNilSymbol :== 65
PD_OverloadedNilSymbol :== 66

PD_Arity2TupleSymbol		:== 67
PD_Arity32TupleSymbol		:== 97

// same order as in MaybeIdentToken
PD_JustSymbol :== 98
PD_NoneSymbol :== 99
PD_StrictJustSymbol :== 100
PD_StrictNoneSymbol :== 101
PD_UnboxedJustSymbol :== 102
PD_UnboxedNoneSymbol :== 103
PD_OverloadedJustSymbol :== 104
PD_OverloadedNoneSymbol :== 105

PD_UnitConsSymbol :== 106

// end constructors

PD_TypeVar_a0				:== 107
PD_TypeVar_a31				:== 138

/* identifiers present in the hashtable */

PD_StdArray					:== 139
PD_StdEnum					:== 140
PD_StdBool					:== 141

PD_AndOp					:== 142
PD_OrOp						:== 143

/* Array functions */

PD_ArrayClass				:== 144

PD_CreateArrayFun			:== 145
PD__CreateArrayFun			:== 146
PD_ArraySelectFun			:== 147
PD_UnqArraySelectFun		:== 148
PD_ArrayUpdateFun			:== 149
PD_ArrayReplaceFun			:== 150
PD_ArraySizeFun				:== 151
PD_UnqArraySizeFun			:== 152

/* Enum/Comprehension functions */

PD_SmallerFun				:== 153
PD_LessOrEqualFun			:== 154
PD_IncFun					:== 155
PD_SubFun					:== 156
PD_From						:== 157
PD_FromThen					:== 158
PD_FromTo					:== 159
PD_FromThenTo				:== 160

/* StdMisc */
PD_StdMisc					:== 161
PD_abort					:== 162
PD_undef					:== 163

PD_Start					:== 164

PD_DummyForStrictAliasFun	:== 165

// StdStrictLists
PD_StdStrictLists:==166

PD_cons:==167
PD_decons:==168

PD_cons_u:==169
PD_decons_u:==170

PD_cons_uts:==171
PD_decons_uts:==172

PD_nil:==173
PD_nil_u:==174
PD_nil_uts:==175

PD_ListClass :== 176
PD_UListClass :== 177
PD_UTSListClass :== 178

// StdStrictMaybes
PD_StdStrictMaybes:==179

// same order as in MaybeIdentToken
PD_just_u:==180
PD_none_u:==181
PD_just:==182
PD_none:==183

PD_from_just_u:==184
PD_from_just:==185

PD_MaybeClass :== 186
PD_UMaybeClass :== 187

/* Dynamics */

// TC class
PD_TypeCodeMember			:== 188
PD_TypeCodeClass			:== 189
// dynamic module
PD_StdDynamic				:== 190
// dynamic type
PD_Dyn_DynamicTemp				:== 191
// type code (type)
PD_Dyn_TypeCode					:== 192
// unification (type)
PD_Dyn_UnificationEnvironment	:== 193
// type code (expressions)
PD_Dyn_TypeScheme			:== 194
PD_Dyn_TypeApp				:== 195
PD_Dyn_TypeVar				:== 196
PD_Dyn_TypeCons				:== 197
PD_Dyn_TypeUnique			:== 198
PD_Dyn__TypeFixedVar		:== 199
// unification (expressions)
PD_Dyn_initial_unification_environment	:== 200
PD_Dyn_bind_global_type_pattern_var_n	:== 201
PD_Dyn_unify							:== 202
PD_Dyn_unify_							:== 203
PD_Dyn_unify_tcs						:== 204
PD_Dyn_normalise						:== 205

/* Generics */
PD_StdGeneric				:== 206
// Generics types
PD_TypeUNIT					:== 207
PD_TypeEITHER				:== 208
PD_TypePAIR					:== 209
// for constructor info
PD_TypeCONS					:== 210
PD_TypeRECORD				:== 211
PD_TypeFIELD				:== 212
PD_TypeOBJECT				:== 213
PD_TGenericConsDescriptor	:== 214
PD_TGenericRecordDescriptor	:== 215
PD_TGenericFieldDescriptor 	:== 216
PD_TGenericTypeDefDescriptor :== 217
PD_TGenConsPrio				:== 218
PD_TGenConsAssoc			:== 219
PD_TGenType					:== 220

PD_TypeGenericDict 			:== 221
PD_TypeGenericDict0			:== 222
// Generics expression
PD_ConsUNIT					:== 223
PD_ConsLEFT					:== 224
PD_ConsRIGHT				:== 225
PD_ConsPAIR					:== 226
// for constructor info
PD_ConsCONS					:== 227
PD_ConsRECORD				:== 228
PD_ConsFIELD				:== 229
PD_ConsOBJECT				:== 230
PD_CGenericConsDescriptor 	:== 231
PD_CGenericRecordDescriptor	:== 232
PD_CGenericFieldDescriptor 	:== 233
PD_CGenericTypeDefDescriptor :== 234
PD_CGenConsNoPrio			:== 235
PD_CGenConsPrio				:== 236
PD_CGenConsAssocNone		:== 237
PD_CGenConsAssocLeft		:== 238
PD_CGenConsAssocRight		:== 239
PD_CGenTypeCons				:== 240
PD_CGenTypeVar				:== 241
PD_CGenTypeArrow			:== 242
PD_CGenTypeApp				:== 243

PD_GenericBimap				:== 244

PD__SystemEnumStrict:==245

PD_FromS					:== 246
PD_FromTS					:== 247
PD_FromSTS					:== 248
PD_FromU					:== 249
PD_FromUTS					:== 250
PD_FromO					:== 251

PD_FromThenS				:== 252
PD_FromThenTS				:== 253
PD_FromThenSTS				:== 254
PD_FromThenU				:== 255
PD_FromThenUTS				:== 256
PD_FromThenO				:== 257

PD_FromToS					:== 258
PD_FromToTS					:== 259
PD_FromToSTS				:== 260
PD_FromToU					:== 261
PD_FromToUTS				:== 262
PD_FromToO					:== 263

PD_FromThenToS				:== 264
PD_FromThenToTS				:== 265
PD_FromThenToSTS			:== 266
PD_FromThenToU				:== 267
PD_FromThenToUTS			:== 268
PD_FromThenToO				:== 269

PD_Dyn__to_TypeCodeConstructor	:== 270
PD_TypeCodeConstructor :== 271

PD_TC_Int			:== 272
PD_TC_Char			:== 273
PD_TC_Real			:== 274
PD_TC_Bool			:== 275
PD_TC_Dynamic		:== 276
PD_TC_File			:== 277
PD_TC_World			:== 278

PD_TC__Arrow		:== 279

PD_TC__List			:== 280
PD_TC__StrictList	:== 281
PD_TC__UnboxedList	:== 282
PD_TC__TailStrictList	:== 283
PD_TC__StrictTailStrictList	:== 284
PD_TC__UnboxedTailStrictList	:== 285

PD_TC__Tuple2		:== 286
PD_TC__Tuple32		:== 316

PD_TC__LazyArray	:== 317
PD_TC__StrictArray	:== 318
PD_TC__UnboxedArray	:== 319
PD_TC__PackedArray	:== 320

PD_TC__LazyArrayP2	:== 321
PD_TC__StrictArrayP2	:== 322
PD_TC__UnboxedArrayP2	:== 323
PD_TC__PackedArrayP2	:== 324

PD_TC__Maybe		:== 325
PD_TC__StrictMaybe	:== 326
PD_TC__UnboxedMaybe	:== 327

PD_TC__Unit			:== 328

PD_NrOfPredefSymbols		:== 329

GetTupleConsIndex tup_arity :== PD_Arity2TupleSymbol + tup_arity - 2
GetTupleTypeIndex tup_arity :== PD_Arity2TupleType + tup_arity - 2

// changes requires recompile of {static,dynamic}-linker plus all dynamics ever made
UnderscoreSystemDynamicModule_String	:== "_SystemDynamic"	

// List-type
PD_ListType_String				:== "_List"
PD_ConsSymbol_String			:== "_Cons"
PD_NilSymbol_String				:== "_Nil"

// Array-type
PD_UnboxedArray_String			:== "_#Array"

DynamicRepresentation_String			:== "DynamicTemp" // "_DynamicTemp"		
