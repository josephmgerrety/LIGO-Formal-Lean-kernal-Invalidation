# Affine maps and algebraic structure

For ordinary integer addition, the affine offset is exactly the obstruction. The results also treat the shifted operation and the two observational samples that preclude a fitting additive map.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [association export roots](../../verification/roots/association.txt)

[Full Lean source](../../PerfectAssociation/Algebra.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>AssociationAlgebra.affine_hom_offset_zero</code></summary>

```lean
theorem affine_hom_offset_zero (a b : Int) (h : AdditiveHom (Affine a b)) : b = 0
```

[`AssociationAlgebra.affine_hom_offset_zero`](../../PerfectAssociation/Algebra.lean#L74)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L19) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.affine_defect</code></summary>

```lean
theorem affine_defect (a b u v : Int) :
    AdditiveDefect (Affine a b) u v = -b
```

[`AssociationAlgebra.affine_defect`](../../PerfectAssociation/Algebra.lean#L85)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L20) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.affine_hom_iff</code></summary>

```lean
theorem affine_hom_iff (a b : Int) :
    AdditiveHom (Affine a b) ↔ b = 0
```

[`AssociationAlgebra.affine_hom_iff`](../../PerfectAssociation/Algebra.lean#L93)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L21) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.affine_nonzero_offset_not_hom</code></summary>

```lean
theorem affine_nonzero_offset_not_hom (a b : Int) (hb : b ≠ 0) :
    ¬ AdditiveHom (Affine a b)
```

[`AssociationAlgebra.affine_nonzero_offset_not_hom`](../../PerfectAssociation/Algebra.lean#L101)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L22) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.affine_nonzero_offset_not_iso</code></summary>

```lean
theorem affine_nonzero_offset_not_iso (a b : Int) (hb : b ≠ 0) :
    ¬ AdditiveIso (Affine a b)
```

[`AssociationAlgebra.affine_nonzero_offset_not_iso`](../../PerfectAssociation/Algebra.lean#L106)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L23) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.seven_minus_four_not_hom</code></summary>

```lean
theorem seven_minus_four_not_hom : ¬ AdditiveHom (Affine 7 (-4))
```

[`AssociationAlgebra.seven_minus_four_not_hom`](../../PerfectAssociation/Algebra.lean#L111)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L24) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.seven_minus_four_not_iso</code></summary>

```lean
theorem seven_minus_four_not_iso : ¬ AdditiveIso (Affine 7 (-4))
```

[`AssociationAlgebra.seven_minus_four_not_iso`](../../PerfectAssociation/Algebra.lean#L114)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L25) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.affine_preserves_shifted_add</code></summary>

```lean
theorem affine_preserves_shifted_add (a b u v : Int) :
    Affine a b (u + v) = shiftedAdd b (Affine a b u) (Affine a b v)
```

[`AssociationAlgebra.affine_preserves_shifted_add`](../../PerfectAssociation/Algebra.lean#L121)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L27) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.shifted_add_associative</code></summary>

```lean
theorem shifted_add_associative (b u v w : Int) :
    shiftedAdd b (shiftedAdd b u v) w =
      shiftedAdd b u (shiftedAdd b v w)
```

[`AssociationAlgebra.shifted_add_associative`](../../PerfectAssociation/Algebra.lean#L127)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L28) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.shifted_add_identity</code></summary>

```lean
theorem shifted_add_identity (b u : Int) :
    shiftedAdd b b u = u ∧ shiftedAdd b u b = u
```

[`AssociationAlgebra.shifted_add_identity`](../../PerfectAssociation/Algebra.lean#L133)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L29) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.MagmaIso.injective</code></summary>

```lean
theorem MagmaIso.injective {M N : Magma} (e : MagmaIso M N)
    (u v : M.carrier) (h : e.toFun u = e.toFun v) : u = v
```

[`AssociationAlgebra.MagmaIso.injective`](../../PerfectAssociation/Algebra.lean#L169)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L37) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.int_add_not_isomorphic_int_mul</code></summary>

```lean
theorem int_add_not_isomorphic_int_mul : ¬ Nonempty (MagmaIso intAdd intMul)
```

[`AssociationAlgebra.int_add_not_isomorphic_int_mul`](../../PerfectAssociation/Algebra.lean#L177)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L38) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.int_add_ne_int_mul</code></summary>

```lean
theorem int_add_ne_int_mul : intAdd ≠ intMul
```

[`AssociationAlgebra.int_add_ne_int_mul`](../../PerfectAssociation/Algebra.lean#L189)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L39) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.identity_observation_not_hom</code></summary>

```lean
theorem identity_observation_not_hom :
    ¬ (∀ u v : Int, u + v = u * v)
```

[`AssociationAlgebra.identity_observation_not_hom`](../../PerfectAssociation/Algebra.lean#L194)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L40) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.no_hom_from_two_samples</code></summary>

```lean
theorem no_hom_from_two_samples (h : Int → Int) (hh : AdditiveHom h)
    (h5 : h 5 = 3) (h15 : h 15 = 38) : False
```

[`AssociationAlgebra.no_hom_from_two_samples`](../../PerfectAssociation/Algebra.lean#L208)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L42) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.no_hom_fits_supplied_observations</code></summary>

```lean
theorem no_hom_fits_supplied_observations :
    ¬ ∃ h : Int → Int, AdditiveHom h ∧ CalibrationFits h
```

[`AssociationAlgebra.no_hom_fits_supplied_observations`](../../PerfectAssociation/Algebra.lean#L222)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L43) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.no_iso_fits_supplied_observations</code></summary>

```lean
theorem no_iso_fits_supplied_observations :
    ¬ ∃ h : Int → Int, AdditiveIso h ∧ CalibrationFits h
```

[`AssociationAlgebra.no_iso_fits_supplied_observations`](../../PerfectAssociation/Algebra.lean#L228)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L44) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>AssociationAlgebra.identity_additive_iso</code></summary>

```lean
theorem identity_additive_iso : AdditiveIso (fun z : Int => z)
```

[`AssociationAlgebra.identity_additive_iso`](../../PerfectAssociation/Algebra.lean#L237)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L45) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>
