/*
	Version 1.1 23-1-1996
*/

#include "compiledefines.h"

#define	class	class_is_keyword
#define	new		new_is_keyword

#define STRUCT(struct_name,type_name) \
	typedef struct struct_name type_name##S; \
	typedef struct struct_name *type_name; \
	typedef struct struct_name *type_name##P; \
	struct struct_name

typedef unsigned long BITVECT;

typedef	enum
{	NoAttr, DeferAttr, CopyAttr
} GraphAttributeKind;

typedef enum
{	NotUsed, UniquelyUsed, SelectivelyUsed, MultiplyUsed, ObservinglyUsed
} OccurrenceKind;

typedef enum {
	TupleState,  ArrayState, RecordState, SimpleState
} StateType;

/* the order of the StateKinds is used by IsLazyState and ExpectsResultNode */
typedef enum {
	OnB, LazyRedirection, StrictRedirection,		/* strict states, no result node */
	StrictOnA,										/* strict state, result node */
	OnA, SemiStrict, Parallel, Undefined, UnderEval	/* lazy states, result node */
} StateKind;

typedef enum {
	UnknownObj,
#if ABSTRACT_OBJECT
	AbstractObj,
#endif
	IntObj, BoolObj, CharObj, RealObj, FileObj, StringObj,
	TupleObj, ListObj, RecordObj, ArrayObj, StrictArrayObj, UnboxedArrayObj,
	WorldObj, ProcIdObj, RedIdObj
#ifdef CLEAN2
	,DynamicObj
#endif
	, NrOfObjects
} ObjectKind;

#if ABSTRACT_OBJECT
# define BASIC_ELEMS_STRING "uuibcrfsaaaaaaippa" /* index by ObjectKind */
#else
# define BASIC_ELEMS_STRING "uibcrfsaaaaaaippa" /* index by ObjectKind */
#endif

typedef enum {
	int_type, bool_type, char_type, real_type,
	file_type, string_type,world_type, procid_type,
	redid_type,
	Nr_Of_Basic_Types,		
	int_denot, bool_denot, char_denot, real_denot,
	Nr_Of_Basic_Denots,
	string_denot,
	fun_type, array_type, strict_array_type, unboxed_array_type, list_type, tuple_type, empty_type,
#ifdef CLEAN2
	dynamic_type,
#endif
	Nr_Of_Predef_Types,
	tuple_symb, cons_symb, nil_symb,
	apply_symb, if_symb, fail_symb, all_symb,
	select_symb,
	Nr_Of_Predef_FunsOrConses,
	definition, newsymbol, instance_symb, empty_symbol, field_symbol_list,
	erroneous_symb
} SymbKind;

STRUCT (state,State){
	union {
		struct state *				sd_args;		/* for TupleState and ArrayState */
		struct record_state_descr *	sd_rs;			/* for RecordState */
		unsigned long				sd_unq_type_args; /* for SimpleState with STATE_UNIQUE_TYPE_ARGUMENTS_MASK */
	} state_descr;
	short							state_arity;
	unsigned char 					state_kind:4;	/* StateKind, for SimpleState */
	unsigned char					state_mark:4;
	unsigned char					state_object:6;	/* ObjectKind, for SimpleState */
	unsigned char					state_type:2;	/* StateType */
};

#define state_unq_type_args state_descr.sd_unq_type_args

#define STATE_UNIQUE_TYPE_ARGUMENTS_MASK 8

# define state_record_symbol		state_descr.sd_rs->rs_symb
# define state_record_arguments		state_descr.sd_rs->rs_args
# define state_record_desc			state_descr.sd_rs
# define state_tuple_arguments		state_descr.sd_args
# define state_array_arguments		state_descr.sd_args

typedef struct state		*States;

#define STATE_PARALLEL_MASK 1
#define STATE_UNBOXED_ARRAY_MASK 2				/* for ArrayState */
#define STATE_ELEMENTS_UPDATEABLE_MASK 2		/* for TupleState */
#define STATE_UNIQUE_MASK 4

typedef struct record_state_descr {
	struct symbol_def *		rs_symb;
	StateS					rs_args[1];
} *RecordStateDescr;

typedef enum {
	SymbolIdTable, TypeSymbolIdTable, TypeVarIdTable, ModuleIdTable, FieldIdTable, KeyWordTable, InternalIdTable
} TableKind;

typedef union symb_value {
	struct ident *					val_ident;
	struct symbol_def *				val_def;
	char *							val_int;
	Bool 							val_bool;
	char *							val_char;
	char *							val_string;
	char *							val_real;
	char *							val_error_mess;
	int								val_arity;
	struct symbol_type *			val_type;		/* for cons_symb, nil_symb apply_symbol ? */
	struct symbol *					val_symb;		/* for field_symbol_list */
#if STRICT_LISTS
	struct state *					val_state_p;		/* element state for unboxed list cons in lhs */
	struct unboxed_cons *			val_unboxed_cons_p;	/* state and symbol definition for unboxed list cons in rhs */
#endif
} SymbValue;

#if STRICT_LISTS
struct unboxed_cons {
	struct state *					unboxed_cons_state_p;
	struct symbol_def *				unboxed_cons_sdef_p;
};
#endif

STRUCT (symbol,Symbol) {
	SymbValue			symb_val;
	Symbol				symb_next;
	unsigned			symb_kind:8;		/* SymbKind */
	Bool				symb_infix:1;
	unsigned			symb_infix_priority:4;
	unsigned			symb_infix_assoc:2;	/* Assoc */
};

#if STRICT_LISTS
# define symb_head_strictness symb_infix_priority /* 0=lazy,1=overloaded,2=strict,3=unboxed overloaded,4=unboxed*/
# define symb_tail_strictness symb_infix_assoc /* 0=lazy,1=strict */

# define symb_state_p symb_val.val_state_p
# define symb_unboxed_cons_p symb_val.val_unboxed_cons_p
# define symb_unboxed_cons_state_p symb_val.val_unboxed_cons_p->unboxed_cons_state_p
# define symb_unboxed_cons_sdef_p symb_val.val_unboxed_cons_p->unboxed_cons_sdef_p
#endif

#define symb_ident symb_val.val_ident
#define symb_def symb_val.val_def
#define symb_int symb_val.val_int
#define symb_bool symb_val.val_bool
#define symb_char symb_val.val_char
#define symb_string symb_val.val_string
#define symb_real symb_val.val_real
#define symb_arity symb_val.val_arity
#define symb_type symb_val.val_type
#define symb_arrfun symb_val.val_arrfun
#define symb_symb symb_val.val_symb
#define symb_instance symb_val.val_instance

#define symb_member symb_val.val_member
#define symb_error_mess symb_val.val_error_mess

STRUCT(ident,Ident){
	char *				ident_name;
	char *				ident_environ;
	union{
		Symbol 				ident_u1_symbol;
		struct node_id *	ident_u1_nodeid;
		struct type_var *	ident_u1_tv;
		struct uni_var *	ident_u1_uni_var;
		char *				ident_u1_instructions;
	} ident_union1;

#ifdef SHORT_CLASS_NAMES
	union{
		struct local_def *		ident_u2_local_defs;
		struct module_info *	ident_u2_mod_info;
	} ident_union2;
#else
	struct local_def *		ident_local_defs;
#endif

	struct ident *		ident_next;
	unsigned char		ident_table; /* TableKind */
	unsigned char		ident_mark;
};

#define ident_symbol		ident_union1.ident_u1_symbol
#define ident_nodeid		ident_union1.ident_u1_nodeid
#define ident_tv			ident_union1.ident_u1_tv
#define ident_uni_var		ident_union1.ident_u1_uni_var
#define ident_instructions	ident_union1.ident_u1_instructions

#ifdef SHORT_CLASS_NAMES
#define ident_local_defs	ident_union2.ident_u2_local_defs
#define ident_mod_info		ident_union2.ident_u2_mod_info
#endif
 
#define IMPORT_MASK					1
#define IMPORTED_MASK				2
#define	BOUND_MASK					4
#define INLINE_MASK					8
#define IMPLICITLY_IMPORTED_MASK	16
#define ID_UNIVAR_MASK				(1 << 5)
#define ID_TYPEVAR_MASK				(1 << 6)
#define ID_CLASSVAR_MASK			(1 << 7)

/*
	The order in which the annotationkinds appear in the enum type
	determines their priority
*/

typedef enum {
	NoAnnot, StrictAnnot,
	/* parallel annotations: */
	ContinueAnnot, ParallelAnnot,
	LazyParallelAnnot, InterleavedAnnot, LazyInterleavedAnnot,
	ProcessAnnot,ParallelAtAnnot, DeferAnnot, ContInterleavedAnnot, WaitAnnot,
	ParallelNFAnnot, InterleavedNFAnnot
} Annotation;

typedef enum { AssocNone=0, AssocLeft=1, AssocRight=2 } Assoc;

typedef struct ident_string *IdentStringP;

struct ident_string {
	IdentStringP	left;
	IdentStringP	right;
	Ident			ident;
	char			*string;
};

typedef struct symb_list SymbElem,*SymbList;

struct symb_list {
	IdentStringP	slist_ident_string;
	SymbList		slist_next;
	unsigned		slist_line;
};

typedef struct def_repr DefRepr,*DefMod;

typedef struct node_def *NodeDefs;

typedef struct {
	short index_a;
	short index_b;
} Index;

struct _exp;

STRUCT (node_id,NodeId){
	Ident			nid_ident;
	unsigned short	nid_mark;
	unsigned short	nid_mark2;
	int				nid_refcount;
	int				nid_number;
	union {
		struct node_id *				inf2_forward_node_id;
		Index							inf2_index;
		int								inf2_lazy_selector_ref_count;
	} nid_inf2;
	union {
		int	inf1_ref_count_copy;
		StateS			inf1_state;
	} nid_inf1;
	int				nid_scope;
	struct node *	nid_node;
	union {
		struct _exp *	u3_exp;
		struct node_id*	u3_lhs_tuple_node_id;
		struct node_id_ref_count_list *	u3_ref_count_element;	/* pattern_match: graph */
	} nid_u3;
	union {
		NodeDefs		u4_node_def;	/* only for rhs */
		struct state *	u4_lhs_state_p;	/* only for lhs */
	} nid_u4;
};

#define nid_ref_count_copy		nid_inf1.inf1_ref_count_copy			/* statesgen */
#define nid_state 				nid_inf1.inf1_state						/* codegen2,instructions */

#define nid_forward_node_id				nid_inf2.inf2_forward_node_id	/* checker,transform */
#define nid_node_id_ref_count_element	nid_u3.u3_ref_count_element		/* pattern_match */
#define nid_node_id_ref_count_element_	nid_u3.u3_ref_count_element		/* pattern_match */
#define nid_a_index						nid_inf2.inf2_index.index_a		/* codegen2,instructions */
#define nid_b_index 					nid_inf2.inf2_index.index_b		/* codegen2,instructions */

#define nid_lazy_selector_ref_count		nid_inf2.inf2_lazy_selector_ref_count/* statesgen */

#define nid_forward_node_id_			nid_inf2.inf2_forward_node_id	/* checker,transform */
#define nid_a_index_					nid_inf2.inf2_index.index_a		/* codegen2,instructions */
#define nid_b_index_					nid_inf2.inf2_index.index_b		/* codegen2,instructions */

#define nid_exp					nid_u3.u3_exp							/* sa */
#define nid_lhs_tuple_node_id	nid_u3.u3_lhs_tuple_node_id

#define nid_node_def			nid_u4.u4_node_def						/* buildtree,sa,statesgen,optimisations */
#define nid_lhs_state_p			nid_u4.u4_lhs_state_p

#define nid_ref_count_copy_		nid_ref_count_copy
#define nid_ref_count_copy__	nid_ref_count_copy
#define nid_node_def_			nid_node_def
#define nid_state_				nid_state
#define nid_state__				nid_state
#define nid_lhs_tuple_node_id_	nid_lhs_tuple_node_id
#define nid_exp_				nid_exp
#define nid_lhs_state_p_		nid_lhs_state_p

/*	Masks for nid_mark */

#define SHARED_NODES_COLLECTED_MASK				1
#define NID_ALIAS_MASK 							2
#define NID_ALIAS_MARK_MASK						4
#define NID_COUNTED_AND_USED_IN_INNER_SCOPE		8
#define NID_EXTRA_REFCOUNT_MASK					16
#define COPY_NODE_MASK							64
#define ON_A_CYCLE_MASK							128
#define NID_VERIFY_MASK							256		/* macros */
#define NID_THEN_ELSE_NON_LOCAL_NODE_ID			512		/* pattern_match */

#define NID_STRICT_LHS_TUPLE_ELEMENT_MASK		8192	/* codegen1,codegen2 */
#define NID_SHARED_SELECTION_NODE_ID			16384	/* optimisations,codegen2 */
#define NID_LIFTED_BY_OPTIMISE					32768	/* optimisations */

/* Masks for nid_mark2 */

#define NID_SELECTION_NODE_ID				1
#if BOXED_RECORDS
# define NID_RECORD_USED_BY_UPDATE			2
# define NID_RECORD_USED_BY_NON_SELECTOR_OR_UPDATES 4
#endif
#define NID_FIELD_NAME_MASK					32			/* typechecker */

#define NID_COMPONENT_DETERMINED_MASK		256				/* optimise_lambda */
#define NID_LHS_PUSHED						4096			/* codegen1 */

#define NID_HAS_LAZY_SELECTOR_COUNTER		8192			/* statesgen */
#define NID_CALL_VIA_LAZY_SELECTIONS_ONLY	16384			/* statesgen */
#define NID_HAS_REFCOUNT_WITHOUT_UPDATES	32768

typedef struct imp_rule *ImpRules;
typedef struct rule_type *RuleTypes;

STRUCT (strict_node_id,StrictNodeId){
	union {
		NodeId			val_node_id;	/* if snid_kind==0 */
		Ident			val_ident;	/* if snid_kind==1 */
	} snid_val;
	struct strict_node_id *	snid_next;
	unsigned				snid_mark:8;
#ifdef OBSERVE_ARRAY_SELECTS_IN_PATTERN
	unsigned				snid_array_select_in_pattern:1;
#endif
};

#define STRICT_NODE_ID_IDENT_MASK 1
#define STRICT_NODE_ID_OBSERVE_MASK 2

#define snid_node_id snid_val.val_node_id
#define snid_ident snid_val.val_ident

STRUCT (if_node_contents,IfNodeContents){
	NodeDefs		if_then_node_defs;
	ImpRules		if_then_rules;
	union {
		StrictNodeIdP					u_strict_node_ids;
		struct node_id_ref_count_list *	u_node_id_ref_counts;
	} if_then_u;
	NodeDefs		if_else_node_defs;
	ImpRules		if_else_rules;
	union {
		StrictNodeIdP					u_strict_node_ids;
		struct node_id_ref_count_list *	u_node_id_ref_counts;
	} if_else_u;
	int				if_local_scope;
};

#define if_then_strict_node_ids	if_then_u.u_strict_node_ids
#define if_else_strict_node_ids	if_else_u.u_strict_node_ids
#define node_then_node_id_ref_counts node_contents.contents_if->if_then_u.u_node_id_ref_counts
#define node_else_node_id_ref_counts node_contents.contents_if->if_else_u.u_node_id_ref_counts

typedef enum {
	IfNode, NormalNode, SelectorNode, NodeIdNode, UpdateNode, MatchNode,						/* normal nodes */
	RecordNode, IdentNode, ApplyNode, ScopeNode,												/* nodes in parser and checker */
	IndirectionNode,																			/* nodes in optimise_lambda */
	SwitchNode, CaseNode, DefaultNode, PushNode, GuardNode, TupleSelectorsNode, FillUniqueNode	/* nodes in codegen */
} NodeKind;

#define SELECTOR_U 2
#define SELECTOR_F 3
#define SELECTOR_L 4
#define SELECTOR_N 5 

#ifdef TRANSFORM_PATTERNS_BEFORE_STRICTNESS_ANALYSIS
STRUCT (case_node_contents,CaseNodeContents){
	struct node_id_ref_count_list *	case_node_id_ref_counts;
	StrictNodeIdP					case_strict_node_ids;
};
#endif

STRUCT (node,Node){
	union {
		struct if_node_contents *	contents_if;
		Symbol						contents_symbol;
		NodeId						contents_node_id;
		Ident						contents_ident;
		struct node *				contents_node;
		struct node_id_list_element *contents_node_ids;
#ifdef TRANSFORM_PATTERNS_BEFORE_STRICTNESS_ANALYSIS
		StrictNodeIdP				contents_guard_strict_node_ids;
#endif
	} node_contents;

	struct arg *					node_arguments;

	union {
		StateS						 su_state;
		struct {
			Symbol							s_record_symbol;			/* comparser,checker */
			int								s_line;						/* size for PushNode if not STRICT_LISTS) */
		} su_s;
		struct {
			struct node_def *			 	u_node_defs;		/* for CaseNode,DefaultNode and GuardNode */
#ifdef TRANSFORM_PATTERNS_BEFORE_STRICTNESS_ANALYSIS
			struct case_node_contents	  * u_case;
#else
			struct node_id_ref_count_list *	u_node_id_ref_counts;
#endif
		} su_u;
		struct {
			struct node_def *			scope_node_defs;
			struct imp_rule *			scope_imp_rules;
		} su_scope;												/* for ScopeNode */
#if STRICT_LISTS
		struct {
			SymbolP						push_symbol;
			union {
				NodeP					pu_decons_node;			/* if overloaded push */
				int						pu_size;				/* if unique non overloaded push */
			} push_pu;
		} su_push;												/* for PushNode */
#endif
	} node_su;

	short			node_arity;
	unsigned char	node_kind;		/* NodeKind */
	signed char		node_number:2;	/* statesgen: -1,0 or 1,pattern_match ? */
	Annotation		node_annotation:6;
};

#ifdef TRANSFORM_PATTERNS_BEFORE_STRICTNESS_ANALYSIS
# define node_node_id_ref_counts	node_su.su_u.u_case->case_node_id_ref_counts
# define node_strict_node_ids		node_su.su_u.u_case->case_strict_node_ids
#else
# define node_node_id_ref_counts	node_su.su_u.u_node_id_ref_counts
#endif

#define node_state					node_su.su_state
#define node_record_symbol			node_su.su_s.s_record_symbol
#define node_line					node_su.su_s.s_line
#define node_node_defs				node_su.su_u.u_node_defs
#define node_symbol					node_contents.contents_symbol
#define node_node_id				node_contents.contents_node_id
#define node_ident					node_contents.contents_ident
#define node_node					node_contents.contents_node
#define node_node_ids				node_contents.contents_node_ids

#ifdef TRANSFORM_PATTERNS_BEFORE_STRICTNESS_ANALYSIS
#define node_guard_strict_node_ids	node_contents.contents_guard_strict_node_ids
#endif

#define node_then_node_defs			node_contents.contents_if->if_then_node_defs
#define node_then_rules				node_contents.contents_if->if_then_rules
#define node_then_strict_node_ids	node_contents.contents_if->if_then_strict_node_ids
#define node_else_node_defs			node_contents.contents_if->if_else_node_defs
#define node_else_rules				node_contents.contents_if->if_else_rules
#define node_else_strict_node_ids	node_contents.contents_if->if_else_strict_node_ids
#define node_if_scope				node_contents.contents_if->if_local_scope

#define node_scope_node_defs		node_su.su_scope.scope_node_defs
#define node_scope_imp_rules		node_su.su_scope.scope_imp_rules

#if STRICT_LISTS
# define node_push_symbol			node_su.su_push.push_symbol
# define node_decons_node			node_su.su_push.push_pu.pu_decons_node
# define node_push_size				node_su.su_push.push_pu.pu_size
#endif

STRUCT (arg,Arg){
	Node 				arg_node;
	struct arg *		arg_next;
	union {
		StateS			u_state;
		unsigned long	u_occurrence; /* OccurrenceKind */
	} arg_u;
};
typedef struct arg *Args;

#define arg_state arg_u.u_state
#define arg_occurrence arg_u.u_occurrence

STRUCT (node_def,NodeDef){
	union {
		NodeId	u1_id;
		Node	u1_pattern;
	} def_u1;
	Node 		def_node;
	NodeDefs	def_next;
	int			def_mark;
};

#define def_id def_u1.u1_id
#define def_pattern def_u1.u1_pattern

#define NODE_DEF_HAS_LHS_PATTERN_MASK 1
#define NODE_DEF_NEW_SCOPE_MASK 2
#define NODE_DEF_NORMAL_SCOPE_MASK 4
#define NODE_DEF_MARKED 8
#define NODE_DEF_OBSERVE_MASK 16
#define NODE_DEF_SELECT_AND_REMOVE_MASK 32

typedef struct local_def {
	union {
		NodeId	contents_node_id;	/*	ldef_node_id, if ldef_kind==0 */
		Symbol	contents_symbol;	/*	ldef_symbol,  if ldef_kind==1 */
	} ldef_contents;
	struct local_def *				ldef_next;
	int								ldef_scope;
	char							ldef_kind;
	char							ldef_lifted;
} LocalDef,*LocalDefP;

#define ldef_node_id ldef_contents.contents_node_id
#define ldef_symbol ldef_contents.contents_symbol

/*	for implementing calls to C or the OS */

typedef struct parameter Parameter,*Parameters;

struct parameter {
	union {
		NodeId	val_node_id;	/* if par_kind == 0 */
		Ident	val_ident;	/* if par_kind == 1 */
	} par_val;
	Ident		par_loc;
	Parameters	par_next;
	int			par_kind;
};

#define par_node_id par_val.val_node_id
#define par_ident par_val.val_ident

typedef struct instruction Instruction,*Instructions;

struct instruction {
	char *		instr_this;
	Instructions	instr_next;
};

STRUCT (code_block,CodeBlock){
	Parameters	co_parin;
	Parameters	co_parout;
	Instructions	co_instr;
	Bool			co_is_abc_code;
#ifdef CLEAN2
	Bool			co_is_inline;
#endif
};

typedef enum {
	Contractum, ExternalCall
} RhsKind;

typedef struct rule_alt 	*RuleAlts;

STRUCT (rule_alt,RuleAlt){
	Node					alt_lhs_root;	
	NodeDefs				alt_lhs_defs;
	union {
		Node				rhs_root;
		CodeBlock			rhs_code;
	} alt_rhs;
	NodeDefs				alt_rhs_defs;
	StrictNodeIdP			alt_strict_node_ids;
	RuleAlts				alt_next;
	unsigned				alt_line;
#ifdef OS2
	unsigned				alt_kind:4;	/* RhsKind */
#else
	unsigned				alt_kind:3;	/* RhsKind */
#endif
	Bool					alt_may_fail:1;
};

#define alt_rhs_root alt_rhs.rhs_root
#define alt_rhs_code alt_rhs.rhs_code

typedef enum {
	NEWDEFINITION, ABSTYPE, TYPE, TYPESYN, DEFRULE, IMPRULE,
	CONSTRUCTOR, SYSRULE, 
	RECORDTYPE, FIELDSELECTOR,
	INSTANCE
} SDefKind;

#define SDefKindSize 5

typedef enum {
	Indefinite, CurrentlyChecked, TypeChecked,
	Predefined, Expanded, TotallyExpanded,
	ConvertingToState, ConvertedToState
} CheckStatus;

typedef enum {
	CreateArrayFun, ArraySelectFun, UnqArraySelectFun, ArrayUpdateFun,
	ArrayReplaceFun, ArraySizeFun, UnqArraySizeFun,
	_CreateArrayFun,_UnqArraySelectFun,_UnqArraySelectNextFun,_UnqArraySelectLastFun,
	_ArrayUpdateFun,
	NoArrayFun 
} ArrayFunKind;

#define ArrayFunKindBitSize 4

#include "syntax_tree_types.h"

STRUCT (imp_rule,ImpRule){
	NodeP 						rule_root;
	RuleAlts 					rule_alts;
	struct type_alt * 			rule_type;
	StateP						rule_state_p;
	ImpRules					rule_next;
	union {
		ImpRuleP				u_next_changed_function;
		ImpRuleP				u_next_used_function;
		ImpRuleP				u_next_function_with_more_arguments;
	} rule_u;
	struct node *				rule_lazy_call_node;
#if STORE_STRICT_CALL_NODES
	struct node *				rule_strict_call_node;
	struct node *				rule_strict_call_node2;
#endif
	unsigned					rule_line;
	unsigned					rule_mark;
	unsigned					rule_ref_count;
};

#define RULE_CHECKED_MASK				1
#define RULE_CAF_MASK					2
#define RULE_LAZY_CALL_NODE_MASK		4
#if STORE_STRICT_CALL_NODES
# define RULE_STRICT_CALL_NODE_MASK		8
# define RULE_STRICT_CALL_NODE2_MASK	16
#endif
#define RULE_HAS_VERSION_WITH_MORE_ARGUMENTS 32
#define RULE_UNBOXED_LAZY_CALL			64
#define RULE_INTERNAL_FUNCTION_MASK		128
#define RULE_LAMBDA_FUNCTION_MASK		256
#define RULE_HAS_REF_COUNT_MASK			512

#define RULE_CALL_VIA_LAZY_SELECTIONS_ONLY	1024
#define RULE_TAIL_MODULO_CONS_ENTRY_MASK	2048

#define rule_next_changed_function				rule_u.u_next_changed_function				/* optimisations */
#define rule_next_used_function					rule_u.u_next_used_function					/* optimisations */
#define rule_next_function_with_more_arguments	rule_u.u_next_function_with_more_arguments	/* statesgen */

STRUCT (symbol_def,SymbDef){
	char    	*sdef_module;
	Ident    	 sdef_ident;
	union
	{	Types			u_type;
		RuleTypes		u_rule_type;
		SynTypes		u_syn_type;
		AbsTypes		u_abs_type;
		ImpRules		u_rule;
	} sdef_u;
	union
	{	struct symbol_type_info *	sti_rule_type_info;
		struct symbol_type *		sti_type_cons_info;
		StateS					typeinfo_record_state;
		struct
		{	FieldList	fieldinfo_sel_field;
#ifndef CLEAN2
			Node		fieldinfo_sel_node;
#endif
			int			fieldinfo_sel_field_number;
		} sdef_fieldinfo;
		struct constructor_list * typeinfo_constructor;	/* for CONSTRUCTOR */
	} sdef_typeinfo;

	unsigned		sdef_number;
	unsigned		sdef_ancestor;
	short			sdef_arity;
	short			sdef_cons_arity;
	short			sdef_over_arity;
	unsigned short	sdef_nr_of_lifted_nodeids;

	union {
		struct _fun *	u3_sa_fun;					/* sa.c */
#ifdef CLEAN2
		SymbolP			u3_unboxed_cons_symbol;		/* backend.c */
#endif
	} sdef_u3;

	struct symbol_def *	sdef_dcl_icl;					/* to dcl if sdef_exported, to icl if sdef_main_dcl */

	union {
		struct symbol_def *	u1_next_scc;
		Symbol				u1_subst_symbol;
	} sdef_u1;

	union {
		struct symbol_def *		sdef_u2_parent;
		struct type_cons_repr *	sdef_u2_type_cons_repr;
		struct symbol_def *		sdef_u2_next_version;	/* for IMPRULES */
	} sdef_u2;
	
	unsigned	 	sdef_line;
	int				sdef_mark;

	Bool			sdef_isused:1;
	Bool			sdef_no_sa:1;
	Bool			sdef_returnsnode:1;
	Bool			sdef_calledwithrootnode:1;
	Bool			sdef_unq_attributed:1;
	Bool			sdef_strict_constructor:1;		/* for CONSTRUCTOR and RECORDTYPE */
	Bool			sdef_boxed_record:1;			/* for RECORDTYPE */
	Bool			sdef_exported:1;
	Bool			sdef_main_dcl:1;				/* if in .dcl of main .icl */
	Bool			sdef_infix:1;
#ifdef OS2
	int				sdef_stupid_gcc;
	SDefKind		sdef_kind:SDefKindSize;
	unsigned		sdef_infix_priority:4;
	unsigned		sdef_checkstatus:4;		/* CheckStatus */
	unsigned		sdef_arfun:ArrayFunKindBitSize;			/* ArrayFunKind */
	unsigned		sdef_infix_assoc:2;		/* Assoc */
#else
	unsigned		sdef_kind:SDefKindSize;
	unsigned		sdef_infix_priority:4;
	unsigned		sdef_infix_assoc:2;		/* Assoc */
	unsigned		sdef_checkstatus:3;		/* CheckStatus */
	unsigned		sdef_arfun:ArrayFunKindBitSize;			/* ArrayFunKind */
#endif
};

#define sdef_type			sdef_u.u_type
#define sdef_rule_type		sdef_u.u_rule_type
#define sdef_syn_type		sdef_u.u_syn_type
#define sdef_abs_type		sdef_u.u_abs_type
#define sdef_rule			sdef_u.u_rule

#define sdef_sa_fun					sdef_u3.u3_sa_fun
#ifdef CLEAN2
 #define sdef_unboxed_cons_symbol sdef_u3.u3_unboxed_cons_symbol
#endif

#define sdef_next_scc			sdef_u1.u1_next_scc
#define sdef_subst_symbol		sdef_u1.u1_subst_symbol	/* macros */

#define	SDEF_USED_LAZILY_MASK 1
#define SDEF_USED_STRICTLY_MASK 2
#define SDEF_USED_CURRIED_MASK 4
#define SDEF_LOCAL_MACRO_FUNCTION_MASK 8
#define SDEF_NEXT_IMP_RULE_VERSION_MASK 32
#define	SDEF_HAS_IMP_RULE_VERSIONS_MASK 64
#define	SDEF_OPTIMISED_FUNCTION_MASK 128

/* some macros to reuse bit fields */

#define sdef_group_number		sdef_ancestor
#define sdef_has_instance_info	sdef_used_as_instance

#define sdef_parent			sdef_u2.sdef_u2_parent
#define sdef_type_cons_repr	sdef_u2.sdef_u2_type_cons_repr

#define sdef_next_version	sdef_u2.sdef_u2_next_version

#define sdef_constructor sdef_typeinfo.typeinfo_constructor

#define sdef_rule_type_info			sdef_typeinfo.sti_rule_type_info
#define sdef_type_cons_info			sdef_typeinfo.sti_type_cons_info

#define sdef_rule_cons_type_info  sdef_rc->rc_type_info

#define sdef_rule_cons_imprule    sdef_rc->rc_imprule
#define sdef_rule_cons_defrule    sdef_rc->rc_defrule

#define sdef_record_state	sdef_typeinfo.typeinfo_record_state
#define sdef_ar_fun_aps	sdef_typeinfo.typeinfo_ar_fun_aps
#define sdef_sel_field	sdef_typeinfo.sdef_fieldinfo.fieldinfo_sel_field
#define sdef_sel_node	sdef_typeinfo.sdef_fieldinfo.fieldinfo_sel_node

#define sdef_sel_field_number	sdef_typeinfo.sdef_fieldinfo.fieldinfo_sel_field_number

#if IMPORT_OBJ_AND_LIB
struct string_list {
	char *				sl_string;
	struct string_list *sl_next;
};
#endif

struct foreign_export_list {
	SymbolP						fe_symbol_p;
	int							fe_stdcall;
	struct foreign_export_list *fe_next;
};

#if CLEAN2
typedef char * ModuleFileTime;
#else
typedef FileTime ModuleFileTime;
#endif

typedef struct {
	Symbol				im_name;
	Symbol				im_symbols;
	Types				im_types;
	SynTypes			im_syn_types;
	ImpRules			im_rules;
	struct symbol_def *	im_start;
	Bool				im_main;
	DefMod				im_def_module;

#ifdef SHORT_CLASS_NAMES
	struct module_info *	im_module_info;
#endif
#if IMPORT_OBJ_AND_LIB
	struct string_list *	im_imported_objs;
	struct string_list *	im_imported_libs;
#endif
	struct foreign_export_list *	im_foreign_exports;
#if WRITE_DCL_MODIFICATION_TIME
	ModuleFileTime		im_modification_time;
#endif
} *ImpMod, ImpRepr;

struct def_repr {
	Symbol		dm_name;
	Symbol		dm_symbols;
	Types		dm_types;
	SynTypes	dm_syn_types;
	AbsTypes	dm_abs_types;
	RuleTypes	dm_rules;
	Bool		dm_system_module;

#ifdef SHORT_CLASS_NAMES
	struct module_info *	dm_module_info;
#endif
#if WRITE_DCL_MODIFICATION_TIME
	ModuleFileTime	dm_modification_time;
#endif
};
