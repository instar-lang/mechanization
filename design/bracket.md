# The Quasiquotation-style Staging Calculus

The "bracket" calculus found in this repository (`Instar/TwoLevelRecBrack`) 
mirrors other quasiquotation languages like MetaOCaml, where staging is accomplished
by way of bracket `.<e>.` and escape `.~e` constructs which produce and 
combine code. It is otherwise identical to a simply typed lambda calculus with 
recursion and constants.

The aim of this particular calculus is to have a quotation-based staging calculus with
the property of erasure soundness:
given that a staged program $e$ produces code $t$, $t$ will be semantically
equivalent to the original program with all staging constructs erased, $|e|$.

The bracket calculus has recursion but no mutable references.

## Semantics

The bracket calculus has a semantics that is somewhat different to the conventional
quasiquotation paradigm. In this calculus, quoted code represents deferred
computation, rather than inert syntactic constructs, as well as being
automatically let-inserted.

So, for a pair of informal examples of this alternate semantics using MetaOCaml syntax:

```ocaml
# .<loop ()>.; .<1>. ;;
- : int code = .<loop (); 1>.
```

Above, the loop reappears in the produced code, rather than being discarded.

```ocaml
# let x = .<2 * 2>. in .<.~x + .~x>. ;;
- : int code = .<let x_0 = 2 * 2 in x_0 + x_0>.
```

Above, although `x` is spliced twice, the generated code contains only one instance
of the `.<2 * 2>.`, because a `let` was automatically inserted to capture the value
of that computation before it was used.

### Elaboration
We define the semantics of this bracket calculus via an elaboration relation
to the calculus found in `Instar/TwoLevelRec` (henceforth referred to as just the
"two-level calculus"). For unquoted (or escaped) code,
the elaboration just corresponds bracket-calculus syntactic forms to their 
first-stage counterparts in the two-level calculus. For quoted code, the same
is true except it is with their second-stage counterparts, and `lift`'s
are inserted for literals, lambdas, and first stage variables 
(thus implementing cross-stage persistence).

The two-level calculus's erasure-soundness metatheory is then leveraged to 
prove the same for the bracket language.

There is also an `option`-typed algorithmic version of the elaboration found at
`Instar/TwoLevelRecBrack/Algorithm.lean` which is proven to produce `some`
expression `t` for well-typed bracket-calculus expressions, and that `t` will
satisfy the elaboration relation with `e`.

## Type-and-effect system

The bracket calculus has a type-and-effect system which is similar
to that of the two-level calculus, designed to guarantee that
elaboration preserves well-typed-ness between the two calculi.

Like the two-level calculus, the bracket-calculus's effect system has two effects, $\top$ and 
$\bot$, which exist to track the existence of code-generation within an expression 
($\top$ for yes, $\bot$ otherwise). There is a stage-sensitive typing
judgement which assigns $\top$ to most expression forms within the second stage 
(that is, within quotes), and is either effect-transparent or $\bot$ for forms in the first
(that is, within escaped code / outside quotes).

The bracket and escape constructs are effect-transparent as well, and just serve
to change the stage of the typing judgement.

There is also another typing judgement used at the top-level of expressions to
ensure that any expression that produces code (has effect $\top$) is of code
type.

Note that unlike the other two-level calculi within this repository,
these two judgments are not mutually recursive and there is only one
code type.

## Future work
The bracket calculus could be extended to have second-stage mutable references
by rebasing it onto the `TwoLevelFinal` calculus.

For another, consider a possible semantic relation between staged programs and 
the code they produce slightly different than erasure-soundness. One wherein
the analog to the erasure transform, perhaps called "unstaging" or some such thing,
would replace certain staging constructs with thunks, rather than removing them
outright.

With this alternative relation, we suspect that this calculus could be 
extended with an additional quoting construct with traditional quoting semantics
that would leave this "unstaging"-soundness intact.