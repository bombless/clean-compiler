
#define DESTRUCTIVE_RECORD_UPDATES 1
#define ADD_ARGUMENTS_TO_HIGHER_ORDER_FUNCTIONS

#define IsLazyState(state) ((state).state_type==SimpleState && (state).state_kind>StrictOnA)
#define IsLazyStateKind(statekind) ((statekind)>StrictOnA)

extern StateS BasicSymbolStates[],LazyState,StrictState;
extern StateS BasicTypeSymbolStates[];
extern int FirstStateIsStricter (StateS offered_state,StateS demanded_state);
extern int FieldArgumentNodeStatesAreStricter (ArgS *offered_args,ArgS *field_args,States record_states);
extern void ConvertAnnotationToState (Annotation annot, States state);
extern void SetUnaryState (States state, StateKind kind, ObjectKind object);
extern Bool HasExternalAnnot (Node node);
extern void GenerateStatesForRecords (struct module_function_and_type_symbols mts,int size_dcl_mfts_a,struct module_function_and_type_symbols dcl_mfts_a[]);
extern void InitStatesGen (void);
extern void GenerateStates (ImpRules rules);
extern ImpRuleP DetermineSharedAndAnnotatedNodes (ImpRules rules);
extern void DetermineStateOfArrayElem (Symbol elemtype, States state);
extern void ExamineTypesAndLhsOfSymbols
	(struct module_function_and_type_symbols mfts,int size_dcl_mfts_a,struct module_function_and_type_symbols dcl_mfts_a[],ImpRuleP new_imp_rules);
extern void ImportSymbols (int size_dcl_mfts_a,struct module_function_and_type_symbols dcl_mfts_a[]);
extern void import_not_yet_imported_record_r_labels (int size_dcl_mfts_a,struct module_function_and_type_symbols dcl_mfts_a[]);
extern void DetermineStatesOfRootNodeAndDefs (Node root_node,NodeDefs *rootdef,StateS demstate,int local_scope);

extern unsigned next_def_number;

extern void ExamineTypesAndLhsOfSymbolDefinition (SymbDef def);
extern void ExamineTypesAndLhsOfImpRuleSymbolDefinitionAgain (SymbDef def);
extern void GenerateStatesForRule (ImpRuleS *rule);
extern void reset_states_and_ref_count_copies (ImpRuleS *rule);
extern void DetermineNodeState (Node node);
extern void ConvertTypeToState (TypeNode type,States state,StateKind kind);

extern int optimise_strict_tuple_result_functions;

extern PolyList UserDefinedArrayFunctions;

extern SymbDefP special_types[];
extern char *StdBoolId;
extern SymbDef AndSymbDef,OrSymbDef;
