# Equality, predicates and indexed carriers

Universal agreement across the indexed carriers characterizes equality. One selected carrier can agree even when its indices differ.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [association export roots](../../verification/roots/association.txt)

[Full Lean source](../../PerfectAssociation/EqualityBridge.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>EqualityBridge.eq_iff_same</code></summary>

```lean
theorem eq_iff_same {a b : α} : a = b ↔ Same a b
```

[`EqualityBridge.eq_iff_same`](../../PerfectAssociation/EqualityBridge.lean#L21)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L47) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>EqualityBridge.eq_iff_indiscernible</code></summary>

```lean
theorem eq_iff_indiscernible {a b : α} :
    a = b ↔ ∀ P : α → Prop, P a ↔ P b
```

[`EqualityBridge.eq_iff_indiscernible`](../../PerfectAssociation/EqualityBridge.lean#L24)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L48) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>EqualityBridge.Iso.injective</code></summary>

```lean
theorem injective {A : Sort v} {B : Sort w} (e : Iso A B) {x y : A}
    (h : e.toFun x = e.toFun y) : x = y
```

[`EqualityBridge.Iso.injective`](../../PerfectAssociation/EqualityBridge.lean#L44)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L52) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>EqualityBridge.Iso.surjective</code></summary>

```lean
theorem surjective {A : Sort v} {B : Sort w} (e : Iso A B) (y : B) :
    ∃ x, e.toFun x = y
```

[`EqualityBridge.Iso.surjective`](../../PerfectAssociation/EqualityBridge.lean#L48)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L53) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>EqualityBridge.transport_refl</code></summary>

```lean
theorem transport_refl (F : α → Sort v) (a : α) (x : F a) :
    (transport F (rfl : a = a)).toFun x = x
```

[`EqualityBridge.transport_refl`](../../PerfectAssociation/EqualityBridge.lean#L65)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L56) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>EqualityBridge.transport_trans</code></summary>

```lean
theorem transport_trans (F : α → Sort v) {a b c : α}
    (h₁ : a = b) (h₂ : b = c) (x : F a) :
    (transport F (h₁.trans h₂)).toFun x =
      (transport F h₂).toFun ((transport F h₁).toFun x)
```

[`EqualityBridge.transport_trans`](../../PerfectAssociation/EqualityBridge.lean#L68)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L57) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>EqualityBridge.transport_symm</code></summary>

```lean
theorem transport_symm (F : α → Sort v) {a b : α} (h : a = b) (y : F b) :
    (transport F h.symm).toFun y = (transport F h).invFun y
```

[`EqualityBridge.transport_symm`](../../PerfectAssociation/EqualityBridge.lean#L76)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L58) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>EqualityBridge.transport_natural</code></summary>

```lean
theorem transport_natural (F G : α → Sort v) (g : ∀ x, F x → G x)
    {a b : α} (h : a = b) (x : F a) :
    (transport G h).toFun (g a x) = g b ((transport F h).toFun x)
```

[`EqualityBridge.transport_natural`](../../PerfectAssociation/EqualityBridge.lean#L82)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L59) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>EqualityBridge.eq_iff_forall_iso</code></summary>

```lean
theorem eq_iff_forall_iso {a b : α} :
    a = b ↔ ∀ F : α → Type v, Nonempty (Iso (F a) (F b))
```

[`EqualityBridge.eq_iff_forall_iso`](../../PerfectAssociation/EqualityBridge.lean#L94)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L60) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>EqualityBridge.distinct_indices_selected_iso</code></summary>

```lean
theorem distinct_indices_selected_iso :
    Nonempty (Iso (constantInfo 0) (constantInfo 1)) ∧ (0 : Nat) ≠ 1
```

[`EqualityBridge.distinct_indices_selected_iso`](../../PerfectAssociation/EqualityBridge.lean#L109)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L63) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>EqualityBridge.selected_iso_does_not_entail_equality</code></summary>

```lean
theorem selected_iso_does_not_entail_equality :
    ¬ (Nonempty (Iso (constantInfo 0) (constantInfo 1)) → (0 : Nat) = 1)
```

[`EqualityBridge.selected_iso_does_not_entail_equality`](../../PerfectAssociation/EqualityBridge.lean#L114)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L64) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>
