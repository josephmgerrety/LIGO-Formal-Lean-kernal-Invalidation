# Printed median intervals, KS thresholds and the calibration domain

Endpoint inequalities rule out additive and redshift relations for the specified componentwise readings. The domain examples use explicit thousandth-grid points, and the marginal-tail result retains the quantile and monotonicity assumptions.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [measurement export roots](../../verification/roots/measurement.txt)

[Full Lean source](../../RequestProject/LIGO_published_ledger.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>LigoSpecious.tableI_median_not_additive</code></summary>

```lean
theorem tableI_median_not_additive (A : MeasStructure.{0} LigoKind tableSig)
    (T : A.carrier → Nat) (xs : Fin 2 → A.carrier) (aLo aHi bLo bHi cLo cHi : Nat)
    (ha : aLo ≤ T (xs 0) ∧ T (xs 0) ≤ aHi) (hb : bLo ≤ T (xs 1) ∧ T (xs 1) ≤ bHi)
    (hc : cLo ≤ T (A.op AddOp.add xs) ∧ T (A.op AddOp.add xs) ≤ cHi)
    (hgap : aHi + bHi < cLo ∨ cHi < aLo + bLo) :
    ¬ PreservesOperation A natStr T
```

[`LigoSpecious.tableI_median_not_additive`](../../RequestProject/LIGO_published_ledger.lean#L80)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L687) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_tableI_imrphenom_median_not_additive</code></summary>

```lean
theorem ligo_tableI_imrphenom_median_not_additive (A : MeasStructure.{0} LigoKind tableSig)
    (T : A.carrier → Nat) (xs : Fin 2 → A.carrier)
    (hm1 : 3845 ≤ T (xs 0) ∧ T (xs 0) ≤ 3855)
    (hm2 : 3215 ≤ T (xs 1) ∧ T (xs 1) ≤ 3225)
    (hM : 7085 ≤ T (A.op AddOp.add xs) ∧ T (A.op AddOp.add xs) ≤ 7095) :
    ¬ PreservesOperation A natStr T ∧ ¬ ValidMeasurementComparison A natStr T ∧
    ∀ Bcal : natStr.carrier → Prop, ¬ Nonempty (ExactCalibration A natStr Bcal T)
```

[`LigoSpecious.ligo_tableI_imrphenom_median_not_additive`](../../RequestProject/LIGO_published_ledger.lean#L101)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L688) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.tableI_median_not_redshift_relation</code></summary>

```lean
theorem tableI_median_not_redshift_relation (A : MeasStructure.{0} LigoKind tableSig)
    (T : A.carrier → Nat) (xs : Fin 3 → A.carrier) (hA : A.rel TableRel.redshift xs)
    (dLo dHi zLo zHi sLo sHi : Nat)
    (hd : dLo ≤ T (xs 0) ∧ T (xs 0) ≤ dHi) (hz : zLo ≤ T (xs 1) ∧ T (xs 1) ≤ zHi)
    (hs : sLo ≤ T (xs 2) ∧ T (xs 2) ≤ sHi)
    (hgap : 10000 * dHi < (10000 + zLo) * sLo ∨ (10000 + zHi) * sHi < 10000 * dLo) :
    ¬ PreservesRelation A natStr T
```

[`LigoSpecious.tableI_median_not_redshift_relation`](../../RequestProject/LIGO_published_ledger.lean#L126)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L689) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_tableI_eobnr_totalMass_not_redshift</code></summary>

```lean
theorem ligo_tableI_eobnr_totalMass_not_redshift (A : MeasStructure.{0} LigoKind tableSig)
    (T : A.carrier → Nat) (xs : Fin 3 → A.carrier) (hA : A.rel TableRel.redshift xs)
    (hd : 7155 ≤ T (xs 0) ∧ T (xs 0) ≤ 7165)
    (hz : 935 ≤ T (xs 1) ∧ T (xs 1) ≤ 945)
    (hs : 6555 ≤ T (xs 2) ∧ T (xs 2) ≤ 6565) :
    ¬ PreservesRelation A natStr T ∧ ¬ ValidMeasurementComparison A natStr T ∧
    ∀ Bcal : natStr.carrier → Prop, ¬ Nonempty (ExactCalibration A natStr Bcal T)
```

[`LigoSpecious.ligo_tableI_eobnr_totalMass_not_redshift`](../../RequestProject/LIGO_published_ledger.lean#L151)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L690) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_tableI_imrphenom_totalMass_not_redshift</code></summary>

```lean
theorem ligo_tableI_imrphenom_totalMass_not_redshift (A : MeasStructure.{0} LigoKind tableSig)
    (T : A.carrier → Nat) (xs : Fin 3 → A.carrier) (hA : A.rel TableRel.redshift xs)
    (hd : 7085 ≤ T (xs 0) ∧ T (xs 0) ≤ 7095)
    (hz : 925 ≤ T (xs 1) ∧ T (xs 1) ≤ 935)
    (hs : 6495 ≤ T (xs 2) ∧ T (xs 2) ≤ 6505) :
    ¬ PreservesRelation A natStr T ∧ ¬ ValidMeasurementComparison A natStr T ∧
    ∀ Bcal : natStr.carrier → Prop, ¬ Nonempty (ExactCalibration A natStr Bcal T)
```

[`LigoSpecious.ligo_tableI_imrphenom_totalMass_not_redshift`](../../RequestProject/LIGO_published_ledger.lean#L167)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L691) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_tableI_imrphenom_secondaryMass_not_redshift</code></summary>

```lean
theorem ligo_tableI_imrphenom_secondaryMass_not_redshift
    (A : MeasStructure.{0} LigoKind tableSig)
    (T : A.carrier → Nat) (xs : Fin 3 → A.carrier) (hA : A.rel TableRel.redshift xs)
    (hd : 3215 ≤ T (xs 0) ∧ T (xs 0) ≤ 3225)
    (hz : 925 ≤ T (xs 1) ∧ T (xs 1) ≤ 935)
    (hs : 2955 ≤ T (xs 2) ∧ T (xs 2) ≤ 2965) :
    ¬ PreservesRelation A natStr T ∧ ¬ ValidMeasurementComparison A natStr T ∧
    ∀ Bcal : natStr.carrier → Prop, ¬ Nonempty (ExactCalibration A natStr Bcal T)
```

[`LigoSpecious.ligo_tableI_imrphenom_secondaryMass_not_redshift`](../../RequestProject/LIGO_published_ledger.lean#L183)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L692) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_tableI_imrphenom_finalMass_not_redshift</code></summary>

```lean
theorem ligo_tableI_imrphenom_finalMass_not_redshift (A : MeasStructure.{0} LigoKind tableSig)
    (T : A.carrier → Nat) (xs : Fin 3 → A.carrier) (hA : A.rel TableRel.redshift xs)
    (hd : 6755 ≤ T (xs 0) ∧ T (xs 0) ≤ 6765)
    (hz : 925 ≤ T (xs 1) ∧ T (xs 1) ≤ 935)
    (hs : 6195 ≤ T (xs 2) ∧ T (xs 2) ≤ 6205) :
    ¬ PreservesRelation A natStr T ∧ ¬ ValidMeasurementComparison A natStr T ∧
    ∀ Bcal : natStr.carrier → Prop, ¬ Nonempty (ExactCalibration A natStr Bcal T)
```

[`LigoSpecious.ligo_tableI_imrphenom_finalMass_not_redshift`](../../RequestProject/LIGO_published_ledger.lean#L200)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L693) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_ks_phi12_verdict_split</code></summary>

```lean
theorem ligo_ks_phi12_verdict_split :
    (ksVerdict 77 = true ∧ ksVerdict 750 = false) ∧
    (∀ p : Nat, 77 ≤ p → p < 500 → ksVerdict p = true) ∧
    (∀ p : Nat, 500 ≤ p → p ≤ 750 → ksVerdict p = false) ∧
    (∀ p : Nat, 3000 ≤ p → p ≤ 6000 → ksVerdict p = false)
```

[`LigoSpecious.ligo_ks_phi12_verdict_split`](../../RequestProject/LIGO_published_ledger.lean#L229)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L695) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.calibrated_subset</code></summary>

```lean
theorem calibrated_subset (p : ParamPoint) (h : calibratedRegion p) : statedDomain p
```

[`LigoSpecious.calibrated_subset`](../../RequestProject/LIGO_published_ledger.lean#L297)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L703) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.calEmbed_preservesOperation</code></summary>

```lean
theorem calEmbed_preservesOperation : PreservesOperation calStr statedStr calEmbed
```

[`LigoSpecious.calEmbed_preservesOperation`](../../RequestProject/LIGO_published_ledger.lean#L306)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L705) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.calEmbed_homomorphic</code></summary>

```lean
theorem calEmbed_homomorphic : HomomorphicAssociation calStr statedStr calEmbed
```

[`LigoSpecious.calEmbed_homomorphic`](../../RequestProject/LIGO_published_ledger.lean#L313)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L706) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.calEmbed_injective</code></summary>

```lean
theorem calEmbed_injective : Measure.Injective calStr statedStr calEmbed
```

[`LigoSpecious.calEmbed_injective`](../../RequestProject/LIGO_published_ledger.lean#L317)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L707) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_calibration_scope_not_exact</code></summary>

```lean
theorem ligo_calibration_scope_not_exact :
    ValidMeasurementComparison calStr statedStr calEmbed ∧
    Measure.Injective calStr statedStr calEmbed ∧
    ∀ Bcal : statedStr.carrier → Prop, Bcal uncalibratedPoint →
      ¬ Nonempty (ExactCalibration calStr statedStr Bcal calEmbed)
```

[`LigoSpecious.ligo_calibration_scope_not_exact`](../../RequestProject/LIGO_published_ledger.lean#L334)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L709) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.not_calibrated_of_spin</code></summary>

```lean
theorem not_calibrated_of_spin (q a1 a2 : Nat) (hq : q < 1000) (h : 500 < a1 ∨ 500 < a2) :
    ¬ calibratedRegion ⟨q, a1, a2⟩
```

[`LigoSpecious.not_calibrated_of_spin`](../../RequestProject/LIGO_published_ledger.lean#L351)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L710) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_calibration_injection_outside</code></summary>

```lean
theorem ligo_calibration_injection_outside :
    statedDomain ⟨810, 340, 670⟩ ∧ ¬ calibratedRegion ⟨810, 340, 670⟩ ∧
    calibratedRegion ⟨810, 340, 500⟩
```

[`LigoSpecious.ligo_calibration_injection_outside`](../../RequestProject/LIGO_published_ledger.lean#L367)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L711) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_calibration_credible_spin_bounds</code></summary>

```lean
theorem ligo_calibration_credible_spin_bounds :
    ∀ q : Nat, 640 ≤ q → q ≤ 980 →
      (∀ u : Nat, (u = 540 ∨ u = 740 ∨ u = 650) → ¬ calibratedRegion ⟨q, u, 0⟩) ∧
      (∀ u : Nat, (u = 700 ∨ u = 780 ∨ u = 750) → ¬ calibratedRegion ⟨q, 0, u⟩)
```

[`LigoSpecious.ligo_calibration_credible_spin_bounds`](../../RequestProject/LIGO_published_ledger.lean#L377)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L712) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_calibration_posterior_mass_outside</code></summary>

```lean
theorem ligo_calibration_posterior_mass_outside (F : Int → Int)
    (hF : ∀ x y : Int, x ≤ y → F x ≤ F y) (b : Int) (hb : 500 < b) (h90 : F b = 90) :
    10 ≤ 100 - F 500
```

[`LigoSpecious.ligo_calibration_posterior_mass_outside`](../../RequestProject/LIGO_published_ledger.lean#L392)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L713) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>
