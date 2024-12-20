# Comparison Between Beluga and Coq

This document outlines the **similarities** and **differences** between implementing the linear lambda calculus using the **Carve methoda** and **writing lemmas** in Beluga and Coq** proof assistants.

---

## Similarities

1. **Type Definitions**
   - Both Coq and Beluga define types for objects (`obj`), contexts (`ctx`), and multiplicities (`mult`) in a style similar to functional programming languages.

   - **Example in Coq**:
     ```coq
     Inductive mult : Type :=
     | zero : mult (* used *)
     | one : mult. (* available once *)
     ```

   - **Example in Beluga**:
     ```beluga
     LF mult : type =
     | 𝟘 : mult  % used
     | 𝟙 : mult; % available once
     ```

2. **Recursive Definitions**
   - Both languages support recursive definitions for context operations like `merge` and equality checks.

   - **Coq**:
     ```coq
     Inductive merge : forall {N : nat}, lctx N -> lctx N -> lctx N -> Type :=
     | mg_n : merge nil nil nil
     | mg_c : merge delta1 delta2 delta
            -> mult_op alpha1 alpha2 alpha
            -> merge (cons delta1 obj tp alpha1)
                     (cons delta2 obj tp alpha2)
                     (cons delta obj tp alpha).
     ```

   - **Beluga**:
     ```beluga
     rec merge : lctx N → lctx N → lctx N → type =
     | mg/n : merge nil nil nil
     | mg/c : merge Δ₁ Δ₂ Δ → • α₁ α₂ α →
              merge (cons Δ₁ X A α₁) (cons Δ₂ X A α₂) (cons Δ X A α);
     ```

3. **Formal Proofs**
   - Both systems define properties and relationships such as:
     - **Equality of multiplicities** (`mult_op`, `mult_eq`)
     - **Context merging rules** (`merge`, `cx_eq`)

4. **Linear Context Handling**
   - Both systems carefully manage assumptions about multiplicities, ensuring `zero` and `one` are used correctly in the linear lambda calculus.

5. **Base Case & Inductive Case Reasoning**
   - Both involve reasoning in cases (e.g., `mg/n` and `mg/c` for `merge`).
   - Coq uses tactics like `inversion` and `constructor`, while Beluga uses dependent case analysis with `case`.

---

## Differences

### 1. Handling of Proofs

- **Beluga**:
  - Uses **dependent pattern matching** and recursion in the proof itself, often combining type definitions and proofs in one structure.
  - **Example**:
    ```beluga
    rec prune_obj : {#p:#[Ψ,x:obj ⊢ obj]}
                   ([Ψ,x:obj ⊢ obj_eq #p x] → [ ⊢ false]) →
                   PruneObj [Ψ,x:obj ⊢ #p] =
      / total /
      mlam #p ⇒ fn n ⇒
      case [_,x:obj ⊢ #p] of
      | [_,x:obj ⊢ x] ⇒ impossible n [_,x:obj ⊢ obj/refl]
      | [_,x:obj ⊢ #q[..]] ⇒ Prune-Obj;
    ```

- **Coq**:
  - Separates proof objects (lemmas) from definitions, requiring explicit proof steps using tactics or term-based reasoning.
  - **Example**:
    ```coq
    Lemma prune_obj :
      forall (psi : ctx) (x p : obj),
        obj_eq p x -> False -> PruneObj (extend x psi) (fun _ => p).
    Proof.
      intros psi x p H_eq H_false.
      inversion H_eq; subst.
      exfalso; exact H_false.
    Qed.
    ```

### 2. Notion of Contexts

- **Beluga**:
  - Uses **implicit contexts** directly tied to LF objects and their logical dependencies. The ambient context (`Ψ`) is threaded implicitly through definitions and proofs.
  - **Example**:
    ```beluga
    rec comp_obj : (Ψ:ctx) {M:[Ψ ⊢ obj]} {N:[Ψ ⊢ obj]}
                   CompareObjs [Ψ ⊢ M] [Ψ ⊢ N] =
      mlam M, N ⇒ ...
    ```

- **Coq**:
  - Requires **explicit context passing**, e.g., `ctx` and `lctx` parameters must be explicitly threaded through definitions and lemmas.
  - **Example**:
    ```coq
    Lemma comp_obj :
      forall (psi : ctx) (M N : obj),
        CompareObjs psi M N.
    ```

### 3. Proof Automation

- **Beluga**:
  - Relies heavily on its ability to **pattern match** and apply dependent constructors recursively. The proofs are more **constructive** in nature.

- **Coq**:
  - Uses **tactics** for step-by-step proof construction. The proof process is often more explicit and modular.

---

## Summary Table

| **Aspect**                | **Beluga**                                                                                     | **Coq**                                                                                  |
|---------------------------|------------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------|
| **Type Definitions**      | LF-based, syntax similar to functional languages.                                              | Inductive definitions, also similar to functional languages.                            |
| **Proof Approach**        | Recursive proofs with dependent pattern matching.                                              | Explicit lemmas and tactics for proofs.                                                 |
| **Context Handling**      | Implicit, ambient contexts passed automatically (`Ψ`).                                         | Explicitly parameterized contexts (`ctx`).                                              |
| **Syntax**                | LF-style (`mlam`, `case`).                                                                     | Functional-style (`match`, `fix`).                                                      |
| **Automation**            | Relies on constructive pattern matching and recursion.                                         | Tactic-driven proof construction.                                                       |
| **Linear Logic**          | Naturally embedded through LF’s dependent typing.                                              | Explicit encoding with inductive types and properties.                                  |
| **Integration**           | Strong coupling between type definitions and proofs in one structure.                          | Separation of type definitions and proofs into different constructs.                    |
| **Suitability**           | Great for systems leveraging dependent types and direct encoding of logical systems.            | Versatile, general-purpose proof assistant suitable for broader formalization efforts.  |

---

Both systems are powerful, but Beluga is more specialized for dependently-typed systems like LF, while Coq provides broader utility at the cost of more explicit handling of contexts and proofs.


## Differences

The same naming convection will be used, however some exceptions will be made to accommodate the differences between the two proof assistants.

Here's a list of differences :

- **Lemmas**: Beluga relies on recursive function definitions (rec) to drive the proof logic, Coq uses a rich set of tactics to guide proofs, making proof development more interactive and adaptable
Here's a list of minor differences :

- **Predefined Types**: We utilize Coq's nat from the PeanoNat library directly, avoiding the need to reimplement nat as was done in Beluga.

- **Overshadowing**: Coq allows overshadowing of definitions, however, to avoid confusion, especially for those familiar with Coq's standard library, alternative names will be used. For example, instead of redefining `lt`, we use `lt_alt` to represent the less-than relation for our custom natural number type, `nat_alt`.

- **Slashes in Names**: Coq does not allow slashes in names, so we replace them with underscores. For example, `lt/z` becomes `lt_z`

- **Dashes in Names**: Coq does not allow dashes in names, so we replace them with underscores and add `_cons` as a suffix. For example, `lt-z` becomes `lt_z_cons`. The `_cons` suffix is used to differentiate between the constructor and the inductive type, for example, `is_suc` is the inductive type and `is_suc_cons` is the constructor.
