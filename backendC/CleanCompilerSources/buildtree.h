
typedef enum
{
	LazyArrayInstance, StrictArrayInstance, UnboxedArrayInstance, NrOfArrayInstances
} ArrayInstance;

typedef enum
{
	NoQuantifier, AllQuantifier, ExistQuantifier, ExistAttributeQuantifier
} Quantifier;

typedef enum
{
										/* defining symbol */
	kUnknownRuleAlternativeKind,		/* ':==', '=:', '=>' or '=' */
	kUnknownFunctionAlternativeKind,	/* '=>' or '=' */
	kFunctionAlternativeKind,			/* '=' */
	kExplicitFunctionAlternativeKind,	/* '=>' */
	kCAFAlternativeKind,				/* '=:' */
	kArrowAlternativeKind				/* '->' */
} RuleAltKind;

STRUCT (scope, Scope)
{
	ImpRules		*sc_rulesP;

	ImpRule			sc_rule;

	RuleAlts		*sc_altP;
	Symbol			sc_ruleSymbol;
	RuleAltKind		sc_altKind;

	NodeDefP		*sc_nodeDefsP;
	NodeDefP		*sc_firstNodeDefP;
	int				sc_scopeMask;

	StrictNodeIdP	*sc_strictDefsP;
};

extern Args NewArgument (NodeP pattern);
extern NodeP NewNode (SymbolP symb, Args args, int arity);
extern NodeP NewIfNode (void);
extern NodeP NewSelectorNode (SymbolP symb, Args args, int arity);
extern NodeP NewNodeIdNode (NodeIdP node_id);
extern NodeP NewApplyNode (NodeP function_node, Args args, int arity);
extern NodeP NewUpdateNode (SymbolP symb,Args args,int arity);
extern NodeP NewIdentifierNode (IdentP ident, Args args, int arity);
extern NodeP NewNodeByKind (NodeKind nodeKind, SymbolP symb, Args args, int arity);
# define	NewNormalNode(symb, args, arity)	NewNodeByKind (NormalNode, (symb), (args), (arity))
# define	NewRecordNode(symb, args, arity)	NewNodeByKind (RecordNode, (symb), (args), (arity))
# define	NewMatchNode(symb, args, arity)		NewNodeByKind (MatchNode, (symb), (args), (arity))
# define	NewCons(element)	NewNormalNode (ConsSymbol, element, 2)
# define	NewNil()			NewNormalNode (NilSymbol, NIL, 0)
# define	NewFalse()			NewNormalNode (FalseSymbol, NIL, 0)
# define	NewTrue()			NewNormalNode (TrueSymbol, NIL, 0)
extern	NodeP NewIntNode (int value);
extern	ImpRules NewRule (unsigned line_number, TypeAlts typeAlternative, NodeP rule_root, ScopeP scope);

extern NodeIdP NewNodeId (IdentP nid);
extern StrictNodeIdP NewStrictNodeId (NodeIdP node_id, StrictNodeIdP next);
extern StrictNodeIdP NewStrictIdent (Ident ident, StrictNodeIdP next);
extern TypeVar NewTypeVar (IdentP nid);
extern UniVar NewUniVar (IdentP nid);
extern NodeDefs NewNodeDefinition (NodeIdP nid, NodeP node);
extern SymbolP NewSymbol (SymbKind symbolKind);
extern TypeNode NewTypeNode (Annotation annot, AttributeKind attr, SymbolP symb, TypeArgs args, int arity);
extern TypeArgs NewTypeArgument (TypeNode pattern);
extern TypeNode NewTypeVarNode (TypeVar node_id,Annotation annot, AttributeKind attr);

extern RuleTypes NewRuleType (TypeAlts type_alt, unsigned line_nr);

extern NodeP NewSelectNode (SymbolP selectSymbol, NodeIdP selectId, int arity);
extern NodeP NewScopeNode (NodeP node, NodeDefP node_defs,ImpRuleS *imp_rules);
extern NodeIdP BuildSelect (NodeP node, NodeDefs **node_defs_p);
extern NodeIdP BuildSelectors (NodeP pattern, NodeP node, NodeDefs **node_defs_p);

extern SymbolP NewSelectSymbol (int arity);
extern SymbolP NewTupleTypeSymbol (int arity);
extern SymbolP NewListFunctionSymbol (void);

extern	ImpRules	NewImpRule (unsigned line_number,TypeAlts typeAlternative,NodeP rule_root);
extern RuleAltP	NewRuleAlt (void);

extern NodeIdP FreshNodeId (NodeP node, NodeDefs **node_defs_h);

extern TypeArgs ConvertFieldsToTypeArguments (FieldList fields);

extern char *CopyString (char *to, char *from, int *rest_size);

extern	char BasicTypeIds  [];
#define ConvertBasicTypeToChar(type_symb) BasicTypeIds [(type_symb) -> symb_kind]

extern TypeNode NewEmptyTypeNode (void);

extern IdentP DetermineNewSymbolId (char *prefix, TypeNode inst_type, TableKind table);

extern	IdentP	gArrayIdents [];

extern SymbolP	BasicTypeSymbols [],
				ArraySymbols [],
				TrueSymbol, FalseSymbol, TupleSymbol, ListSymbol, ConsSymbol, NilSymbol,
				ApplySymbol, ApplyTypeSymbol, SelectSymbols[],
				FailSymbol, IfSymbol, AllSymbol, EmptyTypeSymbol;

extern	SymbolP	TupleTypeSymbols [];
IdentP UseArrayFunctionId (ArrayFunKind kind);
void InitialiseEnumFunctionIds (void);

typedef enum {
	FromEnumFun, FromThenEnumFun, FromToEnumFun, FromThenToEnumFun,
	IncEnumFun, DecEnumFun, MinusEnumFun, LessThanEqEnumFun,
	NoEnumFun
} EnumFunKind;
IdentP EnumFunctionId (EnumFunKind kind);
IdentP UseEnumFunctionId (EnumFunKind kind);


extern unsigned import_system_functions, import_system_array_functions;

void clear_p_at_node_tree (void);
void store_p_at_node (NodeP annoted_node,NodeP at_node);
NodeP *get_p_at_node_p (NodeP annoted_node);
NodeP get_p_at_node (NodeP annoted_node);

# define	kCasePrefix				"_case"
# define	kLambdaPrefix			"_lambda"
# define	kArrayGeneratorPrefix	"_array"
# define	kListGeneratorPrefix	"_list"
# define	kFromPrefix				"_from"
# define	kFromThenPrefix			"_from_then"
# define	kFromToPrefix			"_from_to"
# define	kFromThenToPrefix		"_from_then_to"

