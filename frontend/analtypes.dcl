definition module analtypes

import checksupport, typesupport

partionateAndExpandTypes :: !NumberSet !Index !*CommonDefs !*{#DclModule} !*TypeHeaps !*ErrorAdmin
	-> (!TypeGroups, !*{# CommonDefs}, !*TypeDefInfos, !*CommonDefs, !*{#DclModule}, !*TypeHeaps, !*ErrorAdmin)

::	TypeGroups :== [[GlobalIndex]]

analyseTypeDefs :: !{#CommonDefs} !TypeGroups !{#CheckedTypeDef} !Int !*TypeDefInfos !*TypeVarHeap !*KindHeap !*ErrorAdmin
																  -> (!*TypeDefInfos,!*TypeVarHeap,!*KindHeap,!*ErrorAdmin)

determineKindsOfClasses :: !NumberSet !{#CommonDefs} !*TypeDefInfos !*TypeVarHeap !*KindHeap !*ErrorAdmin
								-> (!*ClassDefInfos, !*TypeDefInfos,!*TypeVarHeap,!*KindHeap,!*ErrorAdmin)

checkKindsOfCommonDefsAndFunctions :: !Index !Index !NumberSet ![IndexRange] !{#CommonDefs} !u:{# FunDef} !v:{#DclModule} !*TypeDefInfos !*ClassDefInfos
														!*TypeVarHeap !*ExpressionHeap !*KindHeap !*GenericHeap !*ErrorAdmin
	-> (!u:{# FunDef}, !v:{#DclModule}, !*TypeDefInfos, !*TypeVarHeap,!*ExpressionHeap,!*KindHeap,!*GenericHeap,!*ErrorAdmin)

isATopConsVar cv		:== cv < 0
encodeTopConsVar cv		:== dec (~cv)
decodeTopConsVar cv		:== ~(inc cv)
