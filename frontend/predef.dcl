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
PD_NothingSymbol :== 95
PD_StrictJustSymbol :== 96
PD_StrictNothingSymbol :== 97
PD_UnboxedJustSymbol :== 98
PD_UnboxedNothingSymbol :== 99
PD_OverloadedJustSymbol :== 100
PD_OverloadedNothingSymbol :== 101

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
PD_nothing_u:==177
PD_just:==178
PD_nothing:==179

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
PD_Dyn_bind_global_type_pattern_var		:== 197
PD_Dyn_unify							:== 198
PD_Dyn_normalise						:== 199

/* Generics */
PD_StdGeneric				:== 200
// Generics types
PD_TypeUNIT					:== 201
PD_TypeEITHER				:== 202
PD_TypePAIR					:== 203
// for constructor info
PD_TypeCONS					:== 204
PD_TypeRECORD				:== 205
PD_TypeFIELD				:== 206
PD_TypeOBJECT				:== 207
PD_TGenericConsDescriptor	:== 208
PD_TGenericRecordDescriptor	:== 209
PD_TGenericFieldDescriptor 	:== 210
PD_TGenericTypeDefDescriptor :== 211
PD_TGenConsPrio				:== 212
PD_TGenConsAssoc			:== 213
PD_TGenType					:== 214

PD_TypeGenericDict 			:== 215
PD_TypeGenericDict0			:== 216
// Generics expression
PD_ConsUNIT					:== 217
PD_ConsLEFT					:== 218
PD_ConsRIGHT				:== 219
PD_ConsPAIR					:== 220
// for constructor info
PD_ConsCONS					:== 221
PD_ConsRECORD				:== 222
PD_ConsFIELD				:== 223
PD_ConsOBJECT				:== 224
PD_CGenericConsDescriptor 	:== 225
PD_CGenericRecordDescriptor	:== 226
PD_CGenericFieldDescriptor 	:== 227
PD_CGenericTypeDefDescriptor :== 228
PD_CGenConsNoPrio			:== 229
PD_CGenConsPrio				:== 230
PD_CGenConsAssocNone		:== 231
PD_CGenConsAssocLeft		:== 232
PD_CGenConsAssocRight		:== 233
PD_CGenTypeCons				:== 234
PD_CGenTypeVar				:== 235
PD_CGenTypeArrow			:== 236
PD_CGenTypeApp				:== 237

PD_GenericBimap				:== 238

PD__SystemEnumStrict:==239

PD_FromS					:== 240
PD_FromTS					:== 241
PD_FromSTS					:== 242
PD_FromU					:== 243
PD_FromUTS					:== 244
PD_FromO					:== 245

PD_FromThenS				:== 246
PD_FromThenTS				:== 247
PD_FromThenSTS				:== 248
PD_FromThenU				:== 249
PD_FromThenUTS				:== 250
PD_FromThenO				:== 251

PD_FromToS					:== 252
PD_FromToTS					:== 253
PD_FromToSTS				:== 254
PD_FromToU					:== 255
PD_FromToUTS				:== 256
PD_FromToO					:== 257

PD_FromThenToS				:== 258
PD_FromThenToTS				:== 259
PD_FromThenToSTS			:== 260
PD_FromThenToU				:== 261
PD_FromThenToUTS			:== 262
PD_FromThenToO				:== 263

PD_Dyn__to_TypeCodeConstructor	:== 264
PD_TypeCodeConstructor :== 265

PD_TC_Int			:== 266
PD_TC_Char			:== 267
PD_TC_Real			:== 268
PD_TC_Bool			:== 269
PD_TC_Dynamic		:== 270
PD_TC_File			:== 271
PD_TC_World			:== 272

PD_TC__Arrow		:== 273

PD_TC__List			:== 274
PD_TC__StrictList	:== 275
PD_TC__UnboxedList	:== 276
PD_TC__TailStrictList	:== 277
PD_TC__StrictTailStrictList	:== 278
PD_TC__UnboxedTailStrictList	:== 279

PD_TC__Tuple2		:== 280
PD_TC__Tuple32		:== 310

PD_TC__LazyArray	:== 311
PD_TC__StrictArray	:== 312
PD_TC__UnboxedArray	:== 313
PD_TC__PackedArray	:== 314

PD_TC__Maybe		:== 315
PD_TC__StrictMaybe	:== 316

PD_TC__Unit			:== 317

PD_NrOfPredefSymbols		:== 318

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
