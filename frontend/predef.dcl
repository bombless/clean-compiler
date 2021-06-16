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

PD_MaybeTypeIndex :== 43
PD_StrictMaybeTypeIndex :== 44
PD_UnboxedMaybeTypeIndex :== 45
//PD_OverloadedMaybeTypeIndex :== 46

PD_UnitTypeIndex :== 47

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

// same order as in MaybeIdentToken
PD_MaybeType :== 44
PD_StrictMaybeType :== 45
PD_UnboxedMaybeType :== 46
PD_OverloadedMaybeType :== 47

PD_UnitType :== 48

// constructors:

FirstConstructorPredefinedSymbolIndex :== PD_ConsSymbol; // to compute index in com_cons_defs

PD_ConsSymbol :== 49
PD_StrictConsSymbol :== 50
PD_UnboxedConsSymbol :== 51
PD_TailStrictConsSymbol :== 52
PD_StrictTailStrictConsSymbol :== 53
PD_UnboxedTailStrictConsSymbol :== 54
PD_OverloadedConsSymbol :== 55

PD_NilSymbol :== 56
PD_StrictNilSymbol :== 57
PD_UnboxedNilSymbol :== 58
PD_TailStrictNilSymbol :== 59
PD_StrictTailStrictNilSymbol :== 60
PD_UnboxedTailStrictNilSymbol :== 61
PD_OverloadedNilSymbol :== 62

PD_Arity2TupleSymbol		:== 63
PD_Arity32TupleSymbol		:== 93

// same order as in MaybeIdentToken
PD_JustSymbol :== 94
PD_NoneSymbol :== 95
PD_StrictJustSymbol :== 96
PD_StrictNoneSymbol :== 97
PD_UnboxedJustSymbol :== 98
PD_UnboxedNoneSymbol :== 99
PD_OverloadedJustSymbol :== 100
PD_OverloadedNoneSymbol :== 101

PD_UnitConsSymbol :== 102

// end constructors

PD_TypeVar_a0				:== 103
PD_TypeVar_a31				:== 134

/* identifiers present in the hashtable */

PD_StdArray					:== 135
PD_StdEnum					:== 136
PD_StdBool					:== 137

PD_AndOp					:== 138
PD_OrOp						:== 139

/* Array functions */

PD_ArrayClass				:== 140

PD_CreateArrayFun			:== 141
PD__CreateArrayFun			:== 142
PD_ArraySelectFun			:== 143
PD_UnqArraySelectFun		:== 144
PD_ArrayUpdateFun			:== 145
PD_ArrayReplaceFun			:== 146
PD_ArraySizeFun				:== 147
PD_UnqArraySizeFun			:== 148

/* Enum/Comprehension functions */

PD_SmallerFun				:== 149
PD_LessOrEqualFun			:== 150
PD_IncFun					:== 151
PD_SubFun					:== 152
PD_From						:== 153
PD_FromThen					:== 154
PD_FromTo					:== 155
PD_FromThenTo				:== 156

/* StdMisc */
PD_StdMisc					:== 157
PD_abort					:== 158
PD_undef					:== 159

PD_Start					:== 160

PD_DummyForStrictAliasFun	:== 161

// StdStrictLists
PD_StdStrictLists:==162

PD_cons:==163
PD_decons:==164

PD_cons_u:==165
PD_decons_u:==166

PD_cons_uts:==167
PD_decons_uts:==168

PD_nil:==169
PD_nil_u:==170
PD_nil_uts:==171

PD_ListClass :== 172
PD_UListClass :== 173
PD_UTSListClass :== 174

// StdStrictMaybes
PD_StdStrictMaybes:==175

// same order as in MaybeIdentToken
PD_just_u:==176
PD_none_u:==177
PD_just:==178
PD_none:==179

PD_from_just_u:==180
PD_from_just:==181

PD_MaybeClass :== 182
PD_UMaybeClass :== 183

/* Dynamics */

// TC class
PD_TypeCodeMember			:== 184
PD_TypeCodeClass			:== 185
// dynamic module
PD_StdDynamic				:== 186
// dynamic type
PD_Dyn_DynamicTemp				:== 187
// type code (type)
PD_Dyn_TypeCode					:== 188
// unification (type)
PD_Dyn_UnificationEnvironment	:== 189
// type code (expressions)
PD_Dyn_TypeScheme			:== 190
PD_Dyn_TypeApp				:== 191
PD_Dyn_TypeVar				:== 192
PD_Dyn_TypeCons				:== 193
PD_Dyn_TypeUnique			:== 194
PD_Dyn__TypeFixedVar		:== 195
// unification (expressions)
PD_Dyn_initial_unification_environment	:== 196
PD_Dyn_bind_global_type_pattern_var_n	:== 197
PD_Dyn_unify							:== 198
PD_Dyn_unify_							:== 199
PD_Dyn_normalise						:== 200

/* Generics */
PD_StdGeneric				:== 201
// Generics types
PD_TypeUNIT					:== 202
PD_TypeEITHER				:== 203
PD_TypePAIR					:== 204
// for constructor info
PD_TypeCONS					:== 205
PD_TypeRECORD				:== 206
PD_TypeFIELD				:== 207
PD_TypeOBJECT				:== 208
PD_TGenericConsDescriptor	:== 209
PD_TGenericRecordDescriptor	:== 210
PD_TGenericFieldDescriptor 	:== 211
PD_TGenericTypeDefDescriptor :== 212
PD_TGenConsPrio				:== 213
PD_TGenConsAssoc			:== 214
PD_TGenType					:== 215

PD_TypeGenericDict 			:== 216
PD_TypeGenericDict0			:== 217
// Generics expression
PD_ConsUNIT					:== 218
PD_ConsLEFT					:== 219
PD_ConsRIGHT				:== 220
PD_ConsPAIR					:== 221
// for constructor info
PD_ConsCONS					:== 222
PD_ConsRECORD				:== 223
PD_ConsFIELD				:== 224
PD_ConsOBJECT				:== 225
PD_CGenericConsDescriptor 	:== 226
PD_CGenericRecordDescriptor	:== 227
PD_CGenericFieldDescriptor 	:== 228
PD_CGenericTypeDefDescriptor :== 229
PD_CGenConsNoPrio			:== 230
PD_CGenConsPrio				:== 231
PD_CGenConsAssocNone		:== 232
PD_CGenConsAssocLeft		:== 233
PD_CGenConsAssocRight		:== 234
PD_CGenTypeCons				:== 235
PD_CGenTypeVar				:== 236
PD_CGenTypeArrow			:== 237
PD_CGenTypeApp				:== 238

PD_GenericBimap				:== 239

PD__SystemEnumStrict:==240

PD_FromS					:== 241
PD_FromTS					:== 242
PD_FromSTS					:== 243
PD_FromU					:== 244
PD_FromUTS					:== 245
PD_FromO					:== 246

PD_FromThenS				:== 247
PD_FromThenTS				:== 248
PD_FromThenSTS				:== 249
PD_FromThenU				:== 250
PD_FromThenUTS				:== 251
PD_FromThenO				:== 252

PD_FromToS					:== 253
PD_FromToTS					:== 254
PD_FromToSTS				:== 255
PD_FromToU					:== 256
PD_FromToUTS				:== 257
PD_FromToO					:== 258

PD_FromThenToS				:== 259
PD_FromThenToTS				:== 260
PD_FromThenToSTS			:== 261
PD_FromThenToU				:== 262
PD_FromThenToUTS			:== 263
PD_FromThenToO				:== 264

PD_Dyn__to_TypeCodeConstructor	:== 265
PD_TypeCodeConstructor :== 266

PD_TC_Int			:== 267
PD_TC_Char			:== 268
PD_TC_Real			:== 269
PD_TC_Bool			:== 270
PD_TC_Dynamic		:== 271
PD_TC_File			:== 272
PD_TC_World			:== 273

PD_TC__Arrow		:== 274

PD_TC__List			:== 275
PD_TC__StrictList	:== 276
PD_TC__UnboxedList	:== 277
PD_TC__TailStrictList	:== 278
PD_TC__StrictTailStrictList	:== 279
PD_TC__UnboxedTailStrictList	:== 280

PD_TC__Tuple2		:== 281
PD_TC__Tuple32		:== 311

PD_TC__LazyArray	:== 312
PD_TC__StrictArray	:== 313
PD_TC__UnboxedArray	:== 314
PD_TC__PackedArray	:== 315

PD_TC__Maybe		:== 316
PD_TC__StrictMaybe	:== 317
PD_TC__UnboxedMaybe	:== 318

PD_TC__Unit			:== 319

PD_NrOfPredefSymbols		:== 320

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
