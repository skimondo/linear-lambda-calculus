# Overview

This is an artifact for the CPP 2025 submission "Split Decisions: Explicit Contexts for Substructural Languages". The artifact contains an implementation in [Beluga](https://github.com/Beluga-lang/Beluga) of CARVe, a general infrastructure for encoding substructural systems and reasoning about their meta-theory. It also includes encodings of several case studies: the linear λ-calculus using HOAS (`lin_lam`), the linear λ-calculus using de Bruijn levels and an environment-based operational semantics (`closures`), the affine λ-calculus (`aff_lam`), the linear sequent calculus (`seq`), the bidirectional linear natural deduction calculus (`nd`), and the multiplicative-additive fragment of the session-typed process calculus [CP](https://dl.acm.org/doi/10.1145/2398856.2364568) (`cp`). We implement proofs of various metatheoretical and equivalence properties for each encoding.

## Structure

To ease navigation, the artifact is organized into folders by theme: The `common` folder contains the general infrastructure, including both definitions (`defs`) and lemmas (`lemmas`). The subfolders of `case_studies` hold the abovementioned case studies; each has a `thms.bel` file containing the main results mechanized. The folder `run` contains configuration files to run the case studies and test the common infrastructure against different multiplicity structures; for convenience, the file `run_all.cfg` is available to execute all of the tests.

Below is a more detailed breakdown:

    run_all.cfg                       - Collects Beluga source files

    common/defs/general.bel           - Encodings of definitions for proofs
    common/defs/nat.bel               - Encodings of natural numbers
    common/defs/obj.bel               - Generic encoding of objects
    common/defs/obj2.bel              - Encodings of object properties, context schema
    common/defs/tp.bel                - Generic encoding of object-level types
    common/defs/mult/                 - Encodings of algebraic structures as multiplicities
    common/defs/ctx.bel               - Encodings of substructural contexts and operations on them

    common/lemmas/nat/                - Lemmas about natural numbers
    common/lemmas/obj.bel, obj2.bel   - Lemmas about objects
    common/lemmas/mult/               - Lemmas about multiplicities
    common/lemmas/upd/                - Lemmas about update operation
    common/lemmas/merge/              - Lemmas about merge operation
    common/lemmas/exh.bel             - Lemmas about exhaustedness
    common/lemmas/same_elts.bel       - Lemmas about contexts containing the same elements
    common/lemmas/wf.bel, varctx.bel  - Lemmas about well-formedness predicates

    case_studies/lin_lam/tm.bel       - Encoding of terms (lin_lam, aff_lam)
    case_studies/lin_lam/tp.bel       - Encoding of object-level types (lin_lam, aff_lam, closures)
    case_studies/lin_lam/dyn.bel      - Encoding of dynamics (lin_lam, aff_lam)
    case_studies/lin_lam/statics.bel  - Encoding of typing rules (lin_lam)
    case_studies/lin_lam/lemmas/      - Lemmas about typing judgment (lin_lam)
    case_studies/lin_lam/thms.bel     - Proof of type preservation (lin_lam)

    case_studies/aff_lam/statics.bel  - Encoding of typing rules (aff_lam)
    case_studies/aff_lam/lemmas/      - Lemmas about typing judgment (aff_lam)
    case_studies/aff_lam/thms.bel     - Proof of type preservation (aff_lam)

    case_studies/closures/tm.bel      - Encoding of terms (closures)
    case_studies/closures/dyn.bel     - Encoding of dynamics (closures)
    case_studies/closures/statics.bel - Encoding of typing rules (closures)
    case_studies/closures/lemmas/     - Lemmas about typing judgment (closures)
    case_studies/closures/thms.bel    - Proof of type preservation (closures)

    case_studies/seq-nd/tm.bel        - Encoding of terms (nd)
    case_studies/seq-nd/tp.bel        - Encoding of object-level types (seq, nd)
    case_studies/seq-nd/seq.bel       - Encoding of typing rules (seq)
    case_studies/seq-nd/nd.bel        - Encoding of typing rules (nd)
    case_studies/seq-nd/subst.bel     - Encoding of simultaneous substitution (seq, nd)
    case_studies/seq-nd/lemmas/       - Lemmas about seq, nd
    case_studies/lin_lam/thms.bel     - Proof of cut elimination (seq), equivalence of seq and nd

    case_studies/cp/proc.bel          - Encoding of processes and operations on processes (cp)
    case_studies/cp/tm.bel            - Encoding of object-level types (cp)
    case_studies/cp/dyn.bel           - Encoding of dynamics (cp)
    case_studies/cp/statics.bel       - Encoding of typing rules (cp)
    case_studies/cp/scp.bel           - Encoding of Structural CP
    case_studies/cp/transl.bel        - Encoding of translation between CP and SCP contexts
    case_studies/cp/lemmas/           - Lemmas about CP, SCP
    case_studies/cp/thms.bel          - Proof of type preservation (cp), equivalence of CP and SCP

## Paper-to-artifact correspondence guide

### Definitions

| Definition                                   | Paper           | File / folder                        | Definition name                                   |
|----------------------------------------------|-----------------|------------------------------------- |---------------------------------------------------|
| Typing contexts                              | §2, §4.1        | common/defs/ctx.bel                  | lctx                                              |
| Linear multiplicities                        | §2.1, §4.1      | common/defs/mult/lin_aff.bel         | mult, •, unr                                      |
| Alternative multiplicity structures          | §5              | common/defs/mult/                    | mult, •, unr                                      |
| Context merge                                | §2.1, §4.1      | common/defs/ctx.bel                  | merge                                             |
| Exhaustedness                                | §2.2, §4.1      | common/defs/ctx.bel                  | exh                                               |
| Context update                               | §2.3, §4.1      | common/defs/ctx.bel                  | upd                                               |
| Context element permutation                  | §2.3, §4.1      | common/defs/ctx.bel                  | exch                                              |
| Context look-up                              | §2.3, §4.1      | common/defs/ctx.bel                  | lookup_intm, lookup_n                             |
| Context well-formedness                      | §4.1            | common/defs/ctx.bel                  | Wf                                                |
| Linear natural deduction terms               | §3.1            | case_studies/seq-nd/tm.bel           | obj                                               |
| Lin. seq. / nat. deduction types             | §4.2            | case_studies/seq-nd/tp.bel           | tp                                                |
| Linear sequent calculus typing judgment      | §3.1            | case_studies/seq-nd/seq.bel          | seq                                               |
| Linear natural deduction typing judgment     | §3.1            | case_studies/seq-nd/nd.bel           | syn, chk                                          |
| Simultaneous substitutions                   | §3.2            | case_studies/seq-nd/subst.bel        | subst, wf_subst                                   |
| CP processes                                 | §4.2            | case_studies/cp/proc.bel             | obj                                               |
| CP typing judgment                           | §4.2            | case_studies/cp/statics.bel          | oft                                               |
| CP / SCP context relations                   | §4.2            | case_studies/cp/transl.bel           | Enc, Dec                                          |
| Linear λ-calculus terms (de Bruijn)          | §4.2            | case_studies/closures/tm.bel         | obj                                               |
| Environment-based operational semantics      | §4.2            | case_studies/closures/dyn.bel        | venv, val, eval                                   |
| Linear λ-calculus typing rules               | §4.2            | case_studies/closures/semantics.bel  | oft                                               |

### Theorems

| Theorem                                      | Paper           | File / folder                        | Definition name                                   |
|----------------------------------------------|-----------------|--------------------------------      |---------------------------------------------------|
| Algebraic properties of lin. multiplicities  | §2.1            | common/lemmas/mult/lin_aff.bel       | mult_func, mult_canc, mult_assoc,                 |
|                                              |                 |                                      | mult_comm, mult_zsfree                            |
| Algebraic properties of context merge        | §2.1, Prop 2.1  | common/lemmas/merge/unrid.bel        | merge_id                                          |
|                                              |                 | common/lemmas/merge/main.bel         | merge_assoc, merge_comm                           |
|                                              |                 | common/lemmas/merge/cancl.bel        | mult_canc                                         |
| Well-formedness properties of context merge  | §2.1, Prop 2.2  | common/lemmas/mult/merge/            | wf_merge, wf_merge_l                              |
| Algebraic properties of context update       | §2.3, Prop 2.3  | common/lemmas/upd/main.bel           | upd_func, upd_refl, upd_symm, upd_trans, upd_conf |
|                                              |                 | common/lemmas/merge/main.bel         | merge_upd                                         |
| Properties of context look-up                | §2.3, Prop 2.4  | common/lemmas/upd/main.bel           | lookup_unq, lookup_upd                            |
|                                              |                 | common/lemmas/merge/main.bel         | merge_lookup, merge_lookup2                       |
| Well-formedness properties of context update | §2.1, Prop 2.5  | common/lemmas/upd/main.bel           | lookup_neq_nat2var, lookup_neq_var2nat,           |
|                                              |                 | common/lemmas/wf.bel                 | wf_upd, wf_upd_neq                                |
| Properties of substitution                   | §3.2, Lemma 3.1 | case_studies/seq-nd/lemmas/subst.bel | subst_exh, subst_merge, subst_upd                 |
| Equivalence theorem (seq. / nat. deduction)  | §3.2, Thm. 3.2  | case_studies/seq-nd/thms.bel         | seq2nd, chk2seq, syn2seq                          |
| Extract lineaity judgment in CP              | §4.2            | case_studies/cp/lemmas/cp2scp.bel    | oft_linear                                        |
| Equivalence of CP and SCP                    | §4.2            | case_studies/cp/thms.bel             | cp2scp, scp2cp                                    |
| Type preservation for linear λ-calculus      | §4.2            | case_studies/closures/thms.bel       | tps                                               |

# Installation and execution

This mechanization is compatible with Beluga version 1.1.1.

## Installation

Beluga may be installed using the OCaml package manager ([`opam`](https://opam.ocaml.org/doc/Install.html)):

	>> opam install beluga.1.1.1

It may also be built and installed from source following the instructions at https://github.com/Beluga-lang/Beluga.

## Execution

Once installed, Beluga can be run on the file `run_all.cfg`. The expected total runtime is approximately 0m7s, and the expected output as follows.

<details>
	<summary>View expected output</summary>
    >> beluga run_all.cfg
    ## Type Reconstruction begin: ./run/mult/../../common/defs/mult/intuit.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/mult/intuit.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/mult/intuit.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/mult/intuit.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/nat.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/nat.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/general.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/general.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/tp/tp.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/tp/tp.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/obj.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/obj.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/obj2.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/obj2.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/ctx.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/ctx.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/obj.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/obj.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/obj2.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/obj2.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/exh.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/exh.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/wf.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/wf.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/varctx.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/varctx.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/merge/unrid.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/merge/unrid.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/merge/cancl.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/merge/cancl.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/mult/lin_aff.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/mult/lin_aff.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/mult/lin_aff.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/mult/lin_aff.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/nat.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/nat.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/general.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/general.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/tp/tp.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/tp/tp.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/obj.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/obj.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/obj2.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/obj2.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/ctx.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/ctx.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/obj.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/obj.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/obj2.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/obj2.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/exh.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/exh.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/wf.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/wf.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/varctx.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/varctx.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/upd/lin_aff.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/upd/lin_aff.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/merge/unrid.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/merge/unrid.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/merge/cancl.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/merge/cancl.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/mult/expon.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/mult/expon.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/mult/expon.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/mult/expon.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/nat.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/nat.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/general.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/general.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/tp/tp.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/tp/tp.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/obj.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/obj.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/obj2.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/obj2.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/ctx.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/ctx.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/obj.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/obj.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/obj2.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/obj2.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/exh.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/exh.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/wf.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/wf.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/varctx.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/varctx.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/mult/strict.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/mult/strict.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/mult/strict.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/mult/strict.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/nat.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/nat.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/general.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/general.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/tp/tp.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/tp/tp.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/obj.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/obj.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/obj2.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/obj2.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/ctx.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/ctx.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/obj.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/obj.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/obj2.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/obj2.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/exh.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/exh.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/wf.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/wf.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/varctx.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/varctx.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/merge/unrid.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/merge/unrid.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/merge/cancl.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/merge/cancl.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/nat.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/nat.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/mult/graded.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/mult/graded.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/nat/plus.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/nat/plus.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/mult/graded.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/mult/graded.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/nat.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/nat.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/general.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/general.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/tp/tp.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/tp/tp.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/obj.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/obj.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/obj2.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/obj2.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/defs/ctx.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/defs/ctx.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/obj.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/obj.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/obj2.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/obj2.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/exh.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/exh.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/wf.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/wf.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/varctx.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/varctx.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/merge/unrid.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/merge/unrid.bel ##
    ## Type Reconstruction begin: ./run/mult/../../common/lemmas/merge/cancl.bel ##
    ## Type Reconstruction done:  ./run/mult/../../common/lemmas/merge/cancl.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/general.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/general.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/mult/lin_aff.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/mult/lin_aff.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/nat.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/nat.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/tp/lin.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/tp/lin.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/seq-nd/tm.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/seq-nd/tm.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/obj2.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/obj2.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/ctx.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/ctx.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/seq-nd/seq.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/seq-nd/seq.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/seq-nd/nd.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/seq-nd/nd.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/seq-nd/subst.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/seq-nd/subst.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/cp/lemmas/tp.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/cp/lemmas/tp.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/mult/lin_aff.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/mult/lin_aff.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/obj.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/obj.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/upd/lin_aff.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/upd/lin_aff.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/exh.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/exh.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/merge/unrid.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/merge/unrid.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/same_elts.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/same_elts.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/seq-nd/lemmas/seq.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/seq-nd/lemmas/seq.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/seq-nd/lemmas/nd.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/seq-nd/lemmas/nd.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/seq-nd/lemmas/subst.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/seq-nd/lemmas/subst.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/seq-nd/thms.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/seq-nd/thms.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/lin_lam/tp.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/lin_lam/tp.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/general.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/general.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/mult/lin_aff.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/mult/lin_aff.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/nat.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/nat.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/closures/tm.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/closures/tm.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/obj2.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/obj2.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/ctx.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/ctx.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/closures/dyn.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/closures/dyn.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/closures/statics.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/closures/statics.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/mult/lin_aff.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/mult/lin_aff.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/obj.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/obj.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/exh.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/exh.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/closures/lemmas/closures.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/closures/lemmas/closures.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/closures/thms.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/closures/thms.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/general.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/general.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/mult/lin_aff.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/mult/lin_aff.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/nat.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/nat.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/lin_lam/tp.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/lin_lam/tp.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/lin_lam/tm.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/lin_lam/tm.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/obj2.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/obj2.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/ctx.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/ctx.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/lin_lam/statics.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/lin_lam/statics.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/lin_lam/dyn.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/lin_lam/dyn.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/mult/lin_aff.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/mult/lin_aff.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/obj.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/obj.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/exh.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/exh.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/merge/unrid.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/merge/unrid.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/varctx.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/varctx.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/lin_lam/lemmas/lin_lam.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/lin_lam/lemmas/lin_lam.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/lin_lam/thms.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/lin_lam/thms.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/general.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/general.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/mult/lin_aff.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/mult/lin_aff.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/nat.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/nat.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/lin_lam/tm.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/lin_lam/tm.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/obj2.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/obj2.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/lin_lam/tp.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/lin_lam/tp.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/ctx.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/ctx.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/aff_lam/statics.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/aff_lam/statics.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/lin_lam/dyn.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/lin_lam/dyn.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/mult/lin_aff.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/mult/lin_aff.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/obj.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/obj.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/exh.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/exh.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/varctx.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/varctx.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/aff_lam/lemmas/aff_lam.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/aff_lam/lemmas/aff_lam.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/aff_lam/thms.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/aff_lam/thms.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/general.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/general.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/mult/lin_aff.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/mult/lin_aff.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/nat.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/nat.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/tp/lin.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/tp/lin.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/cp/proc.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/cp/proc.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/obj2.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/obj2.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/defs/ctx.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/defs/ctx.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/cp/statics.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/cp/statics.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/cp/dyn.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/cp/dyn.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/cp/scp.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/cp/scp.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/cp/transl.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/cp/transl.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/nat/ineq.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/mult/lin_aff.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/mult/lin_aff.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/obj.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/obj.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/obj2.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/obj2.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/upd/main.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/upd/lin_aff.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/upd/lin_aff.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/exh.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/exh.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/merge/main.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/merge/unrid.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/merge/unrid.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../common/lemmas/upd/exch.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/cp/lemmas/tp.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/cp/lemmas/tp.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/cp/lemmas/cp.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/cp/lemmas/cp.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/cp/lemmas/hyp.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/cp/lemmas/hyp.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/cp/lemmas/cp2scp.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/cp/lemmas/cp2scp.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/cp/lemmas/scp2cp.bel ##
    ## Type Reconstruction done:  ./run/case_studies/../../case_studies/cp/lemmas/scp2cp.bel ##
    ## Type Reconstruction begin: ./run/case_studies/../../case_studies/cp/thms.bel ##
</details>
