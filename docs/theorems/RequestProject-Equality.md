# Set extensionality, transport and structured isomorphism

Equality permits substitution. Conversely, testing the equality predicate itself yields equality. Indexed families, explicit inverse maps, sets and magmas supply the formal foundation.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [measurement export roots](../../verification/roots/measurement.txt)

[Full Lean source](../../RequestProject/Equality.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>Sameness.eq_iff_same</code></summary>

```lean
theorem eq_iff_same {a b : α} : a = b ↔ Same a b
```

[`Sameness.eq_iff_same`](../../RequestProject/Equality.lean#L31)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L583) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.eq_iff_indiscernible</code></summary>

```lean
theorem eq_iff_indiscernible {a b : α} : a = b ↔ ∀ P : α → Prop, (P a ↔ P b)
```

[`Sameness.eq_iff_indiscernible`](../../RequestProject/Equality.lean#L35)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L584) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.eq_iff_same_values</code></summary>

```lean
theorem eq_iff_same_values {a b : α} :
    a = b ↔ ∀ (β : Sort u) (f : α → β), f a = f b
```

[`Sameness.eq_iff_same_values`](../../RequestProject/Equality.lean#L39)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L585) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.refl'</code></summary>

```lean
theorem refl' (a : α) : a = a
```

[`Sameness.refl'`](../../RequestProject/Equality.lean#L44)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L586) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.symm'</code></summary>

```lean
theorem symm' {a b : α} (hab : a = b) : b = a
```

[`Sameness.symm'`](../../RequestProject/Equality.lean#L48)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L587) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.trans'</code></summary>

```lean
theorem trans' {a b c : α} (hab : a = b) (hbc : b = c) : a = c
```

[`Sameness.trans'`](../../RequestProject/Equality.lean#L55)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L588) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.eq_equivalence</code></summary>

```lean
theorem eq_equivalence : Equivalence (@Eq α)
```

[`Sameness.eq_equivalence`](../../RequestProject/Equality.lean#L60)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L589) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.eq_le_of_refl</code></summary>

```lean
theorem eq_le_of_refl (R : α → α → Prop) (hR : ∀ x, R x x) {a b : α} (h : a = b) : R a b
```

[`Sameness.eq_le_of_refl`](../../RequestProject/Equality.lean#L64)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L590) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.SetUniverse.mem_right_of_eq</code></summary>

```lean
theorem mem_right_of_eq {x y : S.U} (h : x = y) : ∀ z, (S.mem z x ↔ S.mem z y)
```

[`Sameness.SetUniverse.mem_right_of_eq`](../../RequestProject/Equality.lean#L77)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L592) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.SetUniverse.mem_left_of_eq</code></summary>

```lean
theorem mem_left_of_eq {x y : S.U} (h : x = y) : ∀ z, (S.mem x z ↔ S.mem y z)
```

[`Sameness.SetUniverse.mem_left_of_eq`](../../RequestProject/Equality.lean#L80)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L593) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.SetUniverse.eq_iff_same_members</code></summary>

```lean
theorem eq_iff_same_members (hS : S.Extensional) (x y : S.U) :
    x = y ↔ ∀ z, (S.mem z x ↔ S.mem z y)
```

[`Sameness.SetUniverse.eq_iff_same_members`](../../RequestProject/Equality.lean#L87)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L595) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.ackermann_extensional</code></summary>

```lean
theorem ackermann_extensional : ackermann.Extensional
```

[`Sameness.ackermann_extensional`](../../RequestProject/Equality.lean#L104)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L597) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.PSet.mem_iff_of_eq</code></summary>

```lean
theorem PSet.mem_iff_of_eq {β : Type u} {x y : PSet β} (h : x = y) :
    ∀ z, (x.Mem z ↔ y.Mem z)
```

[`Sameness.PSet.mem_iff_of_eq`](../../RequestProject/Equality.lean#L118)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L600) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.PSet.mem_of_iff_of_eq</code></summary>

```lean
theorem PSet.mem_of_iff_of_eq {β : Type u} {x y : PSet β} (h : x = y) :
    ∀ z : PSet (PSet β), (z.Mem x ↔ z.Mem y)
```

[`Sameness.PSet.mem_of_iff_of_eq`](../../RequestProject/Equality.lean#L123)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L601) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.PSet.ext'</code></summary>

```lean
theorem PSet.ext' {β : Type u} {x y : PSet β} (h : ∀ z, (x.Mem z ↔ y.Mem z)) : x = y
```

[`Sameness.PSet.ext'`](../../RequestProject/Equality.lean#L129)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L602) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.PSet.eq_iff</code></summary>

```lean
theorem PSet.eq_iff {β : Type u} (x y : PSet β) : x = y ↔ ∀ z, (x.Mem z ↔ y.Mem z)
```

[`Sameness.PSet.eq_iff`](../../RequestProject/Equality.lean#L135)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L603) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.Iso.injective</code></summary>

```lean
theorem injective {A : Sort v} {B : Sort w} (e : Iso A B) {x y : A}
    (h : e.toFun x = e.toFun y) : x = y
```

[`Sameness.Iso.injective`](../../RequestProject/Equality.lean#L155)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L607) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.Iso.surjective</code></summary>

```lean
theorem surjective {A : Sort v} {B : Sort w} (e : Iso A B) (y : B) : ∃ x, e.toFun x = y
```

[`Sameness.Iso.surjective`](../../RequestProject/Equality.lean#L159)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L608) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.transport_refl</code></summary>

```lean
theorem transport_refl (F : α → Sort v) (a : α) (x : F a) :
    (transport F (rfl : a = a)).toFun x = x
```

[`Sameness.transport_refl`](../../RequestProject/Equality.lean#L173)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L611) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.transport_trans</code></summary>

```lean
theorem transport_trans (F : α → Sort v) {a b c : α} (h₁ : a = b) (h₂ : b = c) (x : F a) :
    (transport F (h₁.trans h₂)).toFun x =
      (transport F h₂).toFun ((transport F h₁).toFun x)
```

[`Sameness.transport_trans`](../../RequestProject/Equality.lean#L176)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L612) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.transport_symm</code></summary>

```lean
theorem transport_symm (F : α → Sort v) {a b : α} (h : a = b) (y : F b) :
    (transport F h.symm).toFun y = (transport F h).invFun y
```

[`Sameness.transport_symm`](../../RequestProject/Equality.lean#L181)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L613) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.transport_natural</code></summary>

```lean
theorem transport_natural (F G : α → Sort v) (g : ∀ x, F x → G x) {a b : α} (h : a = b)
    (x : F a) : (transport G h).toFun (g a x) = g b ((transport F h).toFun x)
```

[`Sameness.transport_natural`](../../RequestProject/Equality.lean#L186)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L614) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.eq_iff_forall_iso</code></summary>

```lean
theorem eq_iff_forall_iso {a b : α} :
    a = b ↔ ∀ F : α → Type v, Nonempty (Iso (F a) (F b))
```

[`Sameness.eq_iff_forall_iso`](../../RequestProject/Equality.lean#L192)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L615) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Sameness.MagmaIso.ofEq_refl</code></summary>

```lean
theorem MagmaIso.ofEq_refl (M : Magma.{u}) (x : M.carrier) :
    (MagmaIso.ofEq (rfl : M = M)).toFun x = x
```

[`Sameness.MagmaIso.ofEq_refl`](../../RequestProject/Equality.lean#L244)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L623) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>
