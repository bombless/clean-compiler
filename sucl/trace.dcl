definition module trace

// $Id$

from history import History
from spine import Answer
from rule import Rule
from spine import Spine,Subspine // for Answer
from rule import Rgraph          // for History
from basic import Optional       // for Answer

/*

trace.lit - Symbolic reduction traces
=====================================

Description
-----------

This script implements traces of  symbolic  reduction,  indicating  what
happened   and  why.   Representation  functions  for  traces  are  also
provided.

A trace is a possibly infinite tree,  with  the  nodes  labeled  with  a
rewrite  rule,  the  strategy  answer  for  that  rewrite  rule, and the
selected transformation according to the rewrite rule and  the  strategy
answer.  If any transformation is applicable, then a list of subtrees is
present and indicates the result of applying the transformation  to  the
rewrite  rule.   This is a list because a transformation may return more
than one transformed rewrite rule.

------------------------------------------------------------------------

Interface
---------

Exported identifiers:

>   %export
>       trace          ||  Type of a trace
>       transformation ||  Type of applied transformation

>       foldtransformation ||  Break down a transformation
>       mapleaves      ||  Map a function on the rules at the leaves of a trace
>       printtrace     ||  Make a human-readable representation of a trace
>       showtrace      ||  Make a representation of a trace
>       strictchar     ||  Representation of strictness annotation
>       tips           ||  Determine tips of a finite trace

>       result         ||  Deprecated in the new trace structure
>       onresults      ||  Deprecated
>       printresult    ||  Deprecated

Required types:

------------------------------------------------------------

Includes
--------

>   %include "../src/basic.lit"  ||  optional       -
>   %include "../src/pfun.lit"   ||  pfun           -
>   %include "../src/graph.lit"
>   %include "../src/rule.lit"   ||  rule           - printrule rhs rulegraph showrule
>   %include "../src/spine.lit"

------------------------------------------------------------

Deprecated
----------

>   result * ** *** :: type
>   onresults :: (result * ** ***->result * ** ***) -> trace * ** *** -> trace * ** ***
>   printresult :: * -> (*->[char]) -> (**->[char]) -> (***->[char]) -> result * ** *** -> [[char]]

Implementation
--------------

>   trace * ** ***
>   ::= Trace
>           [bool]                    ||  Strict arguments
>           (rule * **)               ||  Current rule
>           (answer * ** ***)         ||  Answer for uninstantiated rule
>           (history * **)            ||  History up to current rule
>           (transformation * ** ***) ||  The applied action and subtraces

*/

:: Trace sym var pvar
   = Trace [Bool]
           (Rule sym var)
           (Answer sym var pvar)
           (History sym var)
           (Transformation sym var pvar)

/*

>   transformation * ** ***
>   ::= Reduce ** (trace * ** ***) | ||  Reduction of the graph by a rewrite rule
>       Annotate (trace * ** ***) |  ||  Addition of a strictness annotation to an argument
>       Stop |                       ||  Stop symbolic reduction
>       Instantiate (trace * ** ***)
>                   (trace * ** ***) ||  Instantiation

*/

/* The abstraction transformation divides the subject graph into areas.
   The abstraction operation is applied when a part or parts of the subject graph must be turned into closures.
   There are two possibilities: closure to an existing function, and closure to a new function.
   Each area becomes a new initial task expression, for which a trace is subsequently produced.
   The root of each area is the same variable as its root in the original subject graph.
   The arguments of each area are found back as the arguments of the initial rewrite rule of the subsequent trace.
   The arguments of each area should be repeated for each of their occurrences in the area.
   Alternatively, an area can become a backpointer to an earlier occurrence in the trace.

   Abstraction can happen for several reasons:
   
   [1] The result of the application of a primitive function is needed.
       The abstracted area is the application of the primitive function alone.
       It is "folded" to itself.
       The abstracted area is not partially evaluated itself.
       
   [2] The strategy found an instance of a pattern in the history.
       The old pattern had a function name attached.
       The abstracted area is the pattern. It is folded to the named function.
       The abstracted area is no longer partially evaluated.

   [3] The strategy found a cycle in the spine.
       The abstracted area is the cyclic tail of the spine.
       It is "folded" to itself (or maybe a special "cycle in spine" function).
       The abstracted area is not partially evaluated itself.
       In fact, the whole graph can be replaced with the "cycle in spine" operator,
       though this may seem kind of opportunistic,
       and just an optimisation of the optimisation process.

   [4] Partial evaluation of the graph had a new occurrence of the area (introduced recursion).
       The current occurrence has no name attached.
       The abstracted area is the recurring pattern.
       It is abstracted, and a name is assigned to it.
       It is folded to the assigned name.
       The abstracted area is still partially evaluated by itself.

   [5] The graph is in root normal form.
       The root node should be abstracted.
       The root node must be "folded" to an application of itself.
       The remainder must be partially evaluated.

   In all these cases, one specific area for abstraction is indicated.
   This specific area may or may not be partially evaluated itself.

   The meaning of the Stop constructor should be changed.
   It is no longer used to force stopping when abstraction is needed.
   Instead, it is used when nothing at all is left to be done.
*/

:: Transformation sym var pvar
   = Reduce var (Trace sym var pvar)
   | Annotate (Trace sym var pvar)
   | Stop
   | Instantiate (Trace sym var pvar)
                 (Trace sym var pvar)
   | Abstract [Abstraction sym var pvar]

:: Abstraction sym var pvar
   = NewAbstraction (Trace sym var pvar)
   | KnownAbstraction (Rule sym var)

/* Alternatives for the Abstract constructor:

     Abstract [Trace sym var pvar]
     together with: Backpointer (Trace sym var pvar)
     
         This means there is always a new trace after an area of the abstraction operator.

         However, the area is never really partially evaluated.
         Instead, a trace is produced that immediately ends with the Stop operator.



     Abstract [Abstraction sym var pvar]
     with
     :: Abstraction sym var pvar
        = NewAbstraction (Trace sym var pvar)
        | OldAbstraction (Rule sym var)

         In this case, the abstraction also determines what happens to the area.
         This may also happen in the former case, but here it's included.
         The former seems better.
*/

/*

>   showtrace showa showb showc (Trace stricts rule answer history transf)
>   =   "(Trace "++
>       show (map strictchar stricts)++' ':
>       showrule showa showb rule++' ':
>       showanswer showa showb showc answer++' ':
>       showhistory showa showb history++' ':
>       showtransf showa showb showc transf++")"

>   showtransf showa showb showc
>   =   stf
>       where stf (Reduce reductroot trace) = "(Reduce "++showb reductroot++' ':str trace++")"
>             stf (Annotate trace) = "(Annotate "++str trace++")"
>             stf Stop = "Stop"
>             stf (Instantiate yestrace notrace) = "(Instantiate "++str yestrace++' ':str notrace++")"
>             str = showtrace showa showb showc

>   strictchar :: bool -> char
>   strictchar strict = cond strict '!' '-'

>   printtrace :: * -> (*->[char]) -> (**->[char]) -> (***->[char]) -> trace * ** *** -> [[char]]

>   printtrace sym showa showb showc
>   =   ptr
>       where ptr (Trace stricts rule answer history transf)
>             =   (showa sym++' ':printrule' showa showb stricts rule (map fst history++answernodes answer)):
>                 indent "    " (printanswer showa showb showc answer)++
>                 printhistory showa showb history++
>                 printtransf sym showa showb showc transf

>   printtransf :: * -> (*->[char]) -> (**->[char]) -> (***->[char]) -> transformation * ** *** -> [[char]]

>   printtransf sym showa showb showc
>   =   ptf
>       where ptf (Reduce reductroot trace) = ("Reduce to "++showb reductroot):ptr trace
>             ptf (Annotate trace) = "Annotate":ptr trace
>             ptf Stop = ["Stop"]
>             ptf (Instantiate yestrace notrace) = indent "I=> " (ptr yestrace)++ptr notrace
>             ptr = printtrace sym showa showb showc

>   answernodes = foldoptional [] spinenodes

>   printrule' :: (*->[char]) -> (**->[char]) -> [bool] -> rule * ** -> [**] -> [char]

>   printrule' printa printb stricts rule anchors
>   =   concat (map2 annot stricts args')++"-> "++root'
>       where graph = rulegraph rule; args = lhs rule; root = rhs rule
>             (args',root':anchors') = claim args reprs
>             reprs = printgraph printa printb graph (args++root:anchors)
>             annot strict repr = cond strict ('!':) id (repr++" ")


Tips traverses a finite trace and produces the  list  of  rewrite  rules
that  are  found  at the leaves of the tree.  This list of rewrite rules
precisely constitutes the result of symbolic reduction of  the  original
rewrite rule, which can be found at the root of the tree.  No folds have
been applied; this has to be done afterwards.

>   tips :: trace * ** *** -> [rule * **]

>   tips
>   =   foldtrace reduce annotate stop instantiate
>       where reduce stricts rule answer history reductroot = id
>             annotate stricts rule answer history = id
>             stop stricts rule answer history = [rule]
>             instantiate stricts rule answer history = (++)


Mapleaves maps a function onto the rules of the leaves of a trace.

>   mapleaves :: (rule * **->rule * **) -> trace * ** *** -> trace * ** ***

>   mapleaves f
>   =   foldtrace reduce annotate stop instantiate
>       where reduce stricts rule answer history reductroot trace = Trace stricts rule answer history (Reduce reductroot trace)
>             annotate stricts rule answer history trace = Trace stricts rule answer history (Annotate trace)
>             stop stricts rule answer history = Trace stricts (f rule) answer history Stop
>             instantiate stricts rule answer history yestrace notrace = Trace stricts rule answer history (Instantiate yestrace notrace)

*/

foldtrace
 :: ([Bool] (Rule sym var) (Answer sym var pvar) (History sym var) var .result -> .result)
    ([Bool] (Rule sym var) (Answer sym var pvar) (History sym var) .result -> .result)
    ([Bool] (Rule sym var) (Answer sym var pvar) (History sym var) -> .result)
    ([Bool] (Rule sym var) (Answer sym var pvar) (History sym var) .result .result -> .result)
    !.(Trace sym var pvar)
 -> .result

foldtransformation
 :: ((Trace sym var pvar) -> .result)
    (var .result -> .subresult)
    (.result -> .subresult)
    .subresult
    (.result .result -> .subresult)
    ([.absresult] -> .subresult)
    ((Rule sym var) -> .absresult)
    (.result -> .absresult)
    !.(Transformation sym var pvar)
 -> .subresult