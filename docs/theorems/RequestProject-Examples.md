# Short tons, kilograms and the calibrated integer range

The exact rational short-ton conversion preserves addition and order in both directions. Whole-ton readings embed in a proper integer subrange of fine units. A target value outside that subrange supplies an explicit obstruction to full-range exact calibration.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [examples export roots](../../verification/roots/examples.txt)

[Full Lean source](../../RequestProject/Examples.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>Measure.tons_smiles_not_sameKind</code></summary>

```lean
theorem tons_smiles_not_sameKind : ¬ SameKind tonScale smileScale
```

[`Measure.tons_smiles_not_sameKind`](../../RequestProject/Examples.lean#L113)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L639) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.tons_vs_smiles_not_comparable</code></summary>

```lean
theorem tons_vs_smiles_not_comparable :
    ¬ SameKind tonScale smileScale ∧
    (∀ T : Tons → Smiles, ¬ ValidMeasurementComparison tonScale smileScale T) ∧
    (∀ (Bcal : Smiles → Prop) (T : Tons → Smiles),
      ¬ Nonempty (ExactCalibration tonScale smileScale Bcal T)) ∧
    ¬ Isomorphic tonScale smileScale
```

[`Measure.tons_vs_smiles_not_comparable`](../../RequestProject/Examples.lean#L121)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L640) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.numerals_do_not_create_comparability</code></summary>

```lean
theorem numerals_do_not_create_comparability :
    ∃ T : Tons → Smiles, T ⟨200⟩ = ⟨41⟩ ∧
      ¬ ValidMeasurementComparison tonScale smileScale T ∧
      ∀ Bcal : Smiles → Prop, ¬ Nonempty (ExactCalibration tonScale smileScale Bcal T)
```

[`Measure.numerals_do_not_create_comparability`](../../RequestProject/Examples.lean#L132)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L641) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.shortTon_pos</code></summary>

```lean
theorem shortTon_pos : (0 : Rat) < shortTon
```

[`Measure.shortTon_pos`](../../RequestProject/Examples.lean#L144)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L643) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.shortTon_ne_zero</code></summary>

```lean
theorem shortTon_ne_zero : shortTon ≠ 0
```

[`Measure.shortTon_ne_zero`](../../RequestProject/Examples.lean#L146)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L644) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.kgToTons_tonsToKg</code></summary>

```lean
theorem kgToTons_tonsToKg (a : Tons) : kgToTons (tonsToKg a) = a
```

[`Measure.kgToTons_tonsToKg`](../../RequestProject/Examples.lean#L155)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L647) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.tonsToKg_kgToTons</code></summary>

```lean
theorem tonsToKg_kgToTons (b : Kilograms) : tonsToKg (kgToTons b) = b
```

[`Measure.tonsToKg_kgToTons`](../../RequestProject/Examples.lean#L161)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L648) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.tonsToKg_add</code></summary>

```lean
theorem tonsToKg_add (a b : Rat) : shortTon * (a + b) = shortTon * a + shortTon * b
```

[`Measure.tonsToKg_add`](../../RequestProject/Examples.lean#L167)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L649) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.shortTon_lt_iff</code></summary>

```lean
theorem shortTon_lt_iff (a b : Rat) : shortTon * a < shortTon * b ↔ a < b
```

[`Measure.shortTon_lt_iff`](../../RequestProject/Examples.lean#L171)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L650) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.shortTon_le_iff</code></summary>

```lean
theorem shortTon_le_iff (a b : Rat) : shortTon * a ≤ shortTon * b ↔ a ≤ b
```

[`Measure.shortTon_le_iff`](../../RequestProject/Examples.lean#L175)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L651) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.shortTon_eq_iff</code></summary>

```lean
theorem shortTon_eq_iff (a b : Rat) : shortTon * a = shortTon * b ↔ a = b
```

[`Measure.shortTon_eq_iff`](../../RequestProject/Examples.lean#L183)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L652) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.tonsToKg_preservesOperation</code></summary>

```lean
theorem tonsToKg_preservesOperation : PreservesOperation tonScale kgScale tonsToKg
```

[`Measure.tonsToKg_preservesOperation`](../../RequestProject/Examples.lean#L192)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L653) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.tonsToKg_eq_iff</code></summary>

```lean
theorem tonsToKg_eq_iff (a₁ a₂ : Tons) : a₁ = a₂ ↔ tonsToKg a₁ = tonsToKg a₂
```

[`Measure.tonsToKg_eq_iff`](../../RequestProject/Examples.lean#L200)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L654) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.tonsToKg_rel_iff</code></summary>

```lean
theorem tonsToKg_rel_iff {n : Nat} (r : OrderRel n) (xs : Fin n → Tons) :
    tonScale.rel r xs ↔ kgScale.rel r (fun i => tonsToKg (xs i))
```

[`Measure.tonsToKg_rel_iff`](../../RequestProject/Examples.lean#L211)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L655) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.tonsToKg_fullSubstitution</code></summary>

```lean
theorem tonsToKg_fullSubstitution : FullSubstitution tonScale kgScale tonsToKg
```

[`Measure.tonsToKg_fullSubstitution`](../../RequestProject/Examples.lean#L218)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L656) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.tons_kg_isomorphic_transposition</code></summary>

```lean
theorem tons_kg_isomorphic_transposition : IsomorphicTransposition tonScale kgScale tonsToKg
```

[`Measure.tons_kg_isomorphic_transposition`](../../RequestProject/Examples.lean#L233)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L658) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.tonsKgCalibration_recal</code></summary>

```lean
theorem tonsKgCalibration_recal : tonsKgCalibration.recal = kgToTons
```

[`Measure.tonsKgCalibration_recal`](../../RequestProject/Examples.lean#L237)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L659) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.two_hundred_tons_eq</code></summary>

```lean
theorem two_hundred_tons_eq : tonsToKg ⟨200⟩ = ⟨181436.948⟩
```

[`Measure.two_hundred_tons_eq`](../../RequestProject/Examples.lean#L240)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L660) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.two_hundred_tons_vs_fifteen_kg</code></summary>

```lean
theorem two_hundred_tons_vs_fifteen_kg :
    SameKind tonScale kgScale ∧
    tonsToKg ⟨200⟩ ≠ ⟨15⟩ ∧
    kgScale.rel OrderRel.lt (fun i => if i = 0 then ⟨15⟩ else tonsToKg ⟨200⟩)
```

[`Measure.two_hundred_tons_vs_fifteen_kg`](../../RequestProject/Examples.lean#L247)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L661) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.equality_representation_independent</code></summary>

```lean
theorem equality_representation_independent (a b : Tons) :
    a = b ↔ tonsToKg a = tonsToKg b
```

[`Measure.equality_representation_independent`](../../RequestProject/Examples.lean#L263)

Lean lists `propext`, `Classical.choice`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L662) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.shortTonFine_pos</code></summary>

```lean
theorem shortTonFine_pos : 0 < shortTonFine
```

[`Measure.shortTonFine_pos`](../../RequestProject/Examples.lean#L319)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L673) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.shortTonFine_ne_zero</code></summary>

```lean
theorem shortTonFine_ne_zero : shortTonFine ≠ 0
```

[`Measure.shortTonFine_ne_zero`](../../RequestProject/Examples.lean#L321)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L674) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.tonsToFine_preservesOperation</code></summary>

```lean
theorem tonsToFine_preservesOperation :
    PreservesOperation wholeTonScale fineScale tonsToFine
```

[`Measure.tonsToFine_preservesOperation`](../../RequestProject/Examples.lean#L324)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L675) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.tonsToFine_eq_iff</code></summary>

```lean
theorem tonsToFine_eq_iff (a₁ a₂ : WholeTons) : a₁ = a₂ ↔ tonsToFine a₁ = tonsToFine a₂
```

[`Measure.tonsToFine_eq_iff`](../../RequestProject/Examples.lean#L333)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L676) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.tonsToFine_rel_iff</code></summary>

```lean
theorem tonsToFine_rel_iff {n : Nat} (r : OrderRel n) (xs : Fin n → WholeTons) :
    wholeTonScale.rel r xs ↔ fineScale.rel r (fun i => tonsToFine (xs i))
```

[`Measure.tonsToFine_rel_iff`](../../RequestProject/Examples.lean#L344)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L677) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.wholeTons_isomorphic_calibrated_range</code></summary>

```lean
theorem wholeTons_isomorphic_calibrated_range :
    Isomorphic wholeTonScale (fineScale.restrict fineCalibrated wholeTonsCalibration.closedRange)
```

[`Measure.wholeTons_isomorphic_calibrated_range`](../../RequestProject/Examples.lean#L365)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L679) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.tonsToFine_not_full_calibration</code></summary>

```lean
theorem tonsToFine_not_full_calibration :
    ¬ Nonempty (ExactCalibration wholeTonScale fineScale (fun _ => True) tonsToFine)
```

[`Measure.tonsToFine_not_full_calibration`](../../RequestProject/Examples.lean#L371)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L680) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>

<details>
<summary><code>Measure.two_hundred_whole_tons</code></summary>

```lean
theorem two_hundred_whole_tons :
    tonsToFine ⟨200⟩ = ⟨18143694800⟩ ∧
    fineScale.rel OrderRel.lt (fun i => if i = 0 then ⟨1500000⟩ else tonsToFine ⟨200⟩)
```

[`Measure.two_hundred_whole_tons`](../../RequestProject/Examples.lean#L379)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L681) · [Accepted checker runs](../../verification/evidence/checkers.log#L63)

</details>
