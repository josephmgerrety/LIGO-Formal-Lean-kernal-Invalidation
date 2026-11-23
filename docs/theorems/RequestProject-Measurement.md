# Structural measurement and exact calibration

An explicitly supplied reverse map, full substitution and range coverage yield a structure-preserving isomorphism onto the calibrated range. A missing operation equation, relation, preimage or injectivity witness invalidates the corresponding claim.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [measurement export roots](../../verification/roots/measurement.txt)

[Full Lean source](../../RequestProject/Measurement.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>Measure.preservesEquality_of_sameness</code></summary>

```lean
theorem preservesEquality_of_sameness (T : A.carrier → B.carrier) :
    PreservesEquality A B T
```

[`Measure.preservesEquality_of_sameness`](../../RequestProject/Measurement.lean#L232)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L873) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.FullSubstitution.preservesRelation</code></summary>

```lean
theorem FullSubstitution.preservesRelation {T : A.carrier → B.carrier}
    (h : FullSubstitution A B T) : PreservesRelation A B T
```

[`Measure.FullSubstitution.preservesRelation`](../../RequestProject/Measurement.lean#L237)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L874) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.FullSubstitution.reflectsRelation</code></summary>

```lean
theorem FullSubstitution.reflectsRelation {T : A.carrier → B.carrier}
    (h : FullSubstitution A B T) : ReflectsRelation A B T
```

[`Measure.FullSubstitution.reflectsRelation`](../../RequestProject/Measurement.lean#L242)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L875) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.fullSubstitution_reflectsEquality</code></summary>

```lean
theorem fullSubstitution_reflectsEquality {T : A.carrier → B.carrier}
    (h : FullSubstitution A B T) : ReflectsEquality A B T
```

[`Measure.fullSubstitution_reflectsEquality`](../../RequestProject/Measurement.lean#L249)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L876) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.fullSubstitution_injective</code></summary>

```lean
theorem fullSubstitution_injective {T : A.carrier → B.carrier}
    (h : FullSubstitution A B T) : Injective A B T
```

[`Measure.fullSubstitution_injective`](../../RequestProject/Measurement.lean#L255)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L877) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.ExactCalibration.surjectiveOnto</code></summary>

```lean
theorem surjectiveOnto (C : ExactCalibration A B Bcal T) : SurjectiveOnto A B Bcal T
```

[`Measure.ExactCalibration.surjectiveOnto`](../../RequestProject/Measurement.lean#L266)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L878) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.ExactCalibration.recal_left</code></summary>

```lean
theorem recal_left (C : ExactCalibration A B Bcal T) (a : A.carrier) :
    C.recal (T a) = a
```

[`Measure.ExactCalibration.recal_left`](../../RequestProject/Measurement.lean#L271)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L879) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.ExactCalibration.tuple_recal</code></summary>

```lean
theorem tuple_recal (C : ExactCalibration A B Bcal T) {n : Nat} (bs : Fin n → B.carrier)
    (hbs : ∀ i, Bcal (bs i)) : (fun i => T (C.recal (bs i))) = bs
```

[`Measure.ExactCalibration.tuple_recal`](../../RequestProject/Measurement.lean#L278)

Lean lists `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L880) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.ExactCalibration.closedRange</code></summary>

```lean
theorem closedRange (C : ExactCalibration A B Bcal T) : ClosedRange B Bcal
```

[`Measure.ExactCalibration.closedRange`](../../RequestProject/Measurement.lean#L283)

Lean lists `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L881) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.ExactCalibration.recal_preservesOperation</code></summary>

```lean
theorem recal_preservesOperation (C : ExactCalibration A B Bcal T) {n : Nat} (f : σ.Op n)
    (bs : Fin n → B.carrier) (hbs : ∀ i, Bcal (bs i)) :
    C.recal (B.op f bs) = A.op f (fun i => C.recal (bs i))
```

[`Measure.ExactCalibration.recal_preservesOperation`](../../RequestProject/Measurement.lean#L291)

Lean lists `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L882) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.ExactCalibration.recal_rel_iff</code></summary>

```lean
theorem recal_rel_iff (C : ExactCalibration A B Bcal T) {n : Nat} (r : σ.Rel n)
    (bs : Fin n → B.carrier) (hbs : ∀ i, Bcal (bs i)) :
    B.rel r bs ↔ A.rel r (fun i => C.recal (bs i))
```

[`Measure.ExactCalibration.recal_rel_iff`](../../RequestProject/Measurement.lean#L299)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L883) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.exact_calibration_implies_isomorphic_transposition</code></summary>

```lean
theorem exact_calibration_implies_isomorphic_transposition {Bcal : B.carrier → Prop}
    {T : A.carrier → B.carrier} (C : ExactCalibration A B Bcal T) :
    SameKind A B ∧
    HomomorphicAssociation A B T ∧
    FullSubstitution A B T ∧
    Injective A B T ∧
    SurjectiveOnto A B Bcal T ∧
    (∀ {n : Nat} (f : σ.Op n) (bs : Fin n → B.carrier), (∀ i, Bcal (bs i)) →
      C.recal (B.op f bs) = A.op f (fun i => C.recal (bs i))) ∧
    (∀ {n : Nat} (r : σ.Rel n) (bs : Fin n → B.carrier), (∀ i, Bcal (bs i)) →
      (B.rel r bs ↔ A.rel r (fun i => C.recal (bs i)))) ∧
    IsomorphicTransposition A (B.restrict Bcal C.closedRange) (fun a => ⟨T a, C.lands a⟩)
```

[`Measure.exact_calibration_implies_isomorphic_transposition`](../../RequestProject/Measurement.lean#L339)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L886) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.exact_calibration_isomorphic</code></summary>

```lean
theorem exact_calibration_isomorphic {Bcal : B.carrier → Prop} {T : A.carrier → B.carrier}
    (C : ExactCalibration A B Bcal T) : Isomorphic A (B.restrict Bcal C.closedRange)
```

[`Measure.exact_calibration_isomorphic`](../../RequestProject/Measurement.lean#L357)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L887) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.exact_full_calibration_isomorphic_transposition</code></summary>

```lean
theorem exact_full_calibration_isomorphic_transposition {T : A.carrier → B.carrier}
    (C : ExactCalibration A B (fun _ => True) T) : IsomorphicTransposition A B T
```

[`Measure.exact_full_calibration_isomorphic_transposition`](../../RequestProject/Measurement.lean#L363)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L888) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.exists_exact_calibration_iff_isomorphic</code></summary>

```lean
theorem exists_exact_calibration_iff_isomorphic :
    (∃ T : A.carrier → B.carrier, Nonempty (ExactCalibration A B (fun _ => True) T)) ↔
      Isomorphic A B
```

[`Measure.exists_exact_calibration_iff_isomorphic`](../../RequestProject/Measurement.lean#L381)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L890) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.not_preservesOperation_of_noncommuting</code></summary>

```lean
theorem not_preservesOperation_of_noncommuting {T : A.carrier → B.carrier} {n : Nat}
    (f : σ.Op n) (xs : Fin n → A.carrier)
    (hne : T (A.op f xs) ≠ B.op f (fun i => T (xs i))) : ¬ PreservesOperation A B T
```

[`Measure.not_preservesOperation_of_noncommuting`](../../RequestProject/Measurement.lean#L391)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L891) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.not_hom_implies_not_valid</code></summary>

```lean
theorem not_hom_implies_not_valid {T : A.carrier → B.carrier}
    (h : ¬ PreservesOperation A B T) :
    ¬ HomomorphicAssociation A B T ∧ ¬ ValidMeasurementComparison A B T ∧
      ∀ Bcal : B.carrier → Prop, ¬ Nonempty (ExactCalibration A B Bcal T)
```

[`Measure.not_hom_implies_not_valid`](../../RequestProject/Measurement.lean#L398)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L892) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.not_preservesRelation_implies_not_valid</code></summary>

```lean
theorem not_preservesRelation_implies_not_valid {T : A.carrier → B.carrier}
    (h : ¬ PreservesRelation A B T) :
    ¬ HomomorphicAssociation A B T ∧ ¬ ValidMeasurementComparison A B T ∧
      ¬ FullSubstitution A B T
```

[`Measure.not_preservesRelation_implies_not_valid`](../../RequestProject/Measurement.lean#L405)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L893) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.not_injective_implies_not_fullSubstitution</code></summary>

```lean
theorem not_injective_implies_not_fullSubstitution {T : A.carrier → B.carrier}
    (h : ∃ a₁ a₂, a₁ ≠ a₂ ∧ T a₁ = T a₂) : ¬ FullSubstitution A B T
```

[`Measure.not_injective_implies_not_fullSubstitution`](../../RequestProject/Measurement.lean#L415)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L894) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.not_surjective_implies_not_calibration</code></summary>

```lean
theorem not_surjective_implies_not_calibration {Bcal : B.carrier → Prop}
    {T : A.carrier → B.carrier} (h : ∃ b, Bcal b ∧ ∀ a, T a ≠ b) :
    ¬ Nonempty (ExactCalibration A B Bcal T)
```

[`Measure.not_surjective_implies_not_calibration`](../../RequestProject/Measurement.lean#L421)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L895) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.calibration_bijective</code></summary>

```lean
theorem calibration_bijective {Bcal : B.carrier → Prop} {T : A.carrier → B.carrier}
    (C : ExactCalibration A B Bcal T) : Injective A B T ∧ SurjectiveOnto A B Bcal T
```

[`Measure.calibration_bijective`](../../RequestProject/Measurement.lean#L427)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L896) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.not_isomorphic_implies_not_full_calibration</code></summary>

```lean
theorem not_isomorphic_implies_not_full_calibration {Bcal : B.carrier → Prop}
    (h : ∀ hc : ClosedRange B Bcal, ¬ Isomorphic A (B.restrict Bcal hc))
    (T : A.carrier → B.carrier) : ¬ Nonempty (ExactCalibration A B Bcal T)
```

[`Measure.not_isomorphic_implies_not_full_calibration`](../../RequestProject/Measurement.lean#L434)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L897) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.not_isomorphic_implies_not_exact_calibration</code></summary>

```lean
theorem not_isomorphic_implies_not_exact_calibration (h : ¬ Isomorphic A B)
    (T : A.carrier → B.carrier) : ¬ Nonempty (ExactCalibration A B (fun _ => True) T)
```

[`Measure.not_isomorphic_implies_not_exact_calibration`](../../RequestProject/Measurement.lean#L440)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L898) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>Measure.different_quantity_kind_implies_not_comparable</code></summary>

```lean
theorem different_quantity_kind_implies_not_comparable (h : A.kind ≠ B.kind) :
    ¬ SameKind A B ∧
    (∀ T : A.carrier → B.carrier, ¬ ValidMeasurementComparison A B T) ∧
    (∀ (Bcal : B.carrier → Prop) (T : A.carrier → B.carrier),
      ¬ Nonempty (ExactCalibration A B Bcal T)) ∧
    ¬ Isomorphic A B
```

[`Measure.different_quantity_kind_implies_not_comparable`](../../RequestProject/Measurement.lean#L448)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L899) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>
