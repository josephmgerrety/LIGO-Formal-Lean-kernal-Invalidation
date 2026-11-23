# Effective spin, reporting maps and calibration

Witnesses for difference, effective precession spin, two-bin pooling, higher-mode projection, Gaussian exponent, and six-to-four spin projection give explicit failures of injectivity or structure reflection. The parity-range inverse supplies a positive recovery result.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [measurement export roots](../../verification/roots/measurement.txt)

[Full Lean source](../../RequestProject/LIGO_specious_measures.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>LigoSpecious.pair_congr</code></summary>

```lean
theorem pair_congr {α β : Type} {a c : α} {b d : β} (h₁ : a = c) (h₂ : b = d) :
    (a, b) = (c, d)
```

[`LigoSpecious.pair_congr`](../../RequestProject/LIGO_specious_measures.lean#L80)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L721) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.fibre_obstructs</code></summary>

```lean
theorem fibre_obstructs {A B : MeasStructure.{u} K σ} {T : A.carrier → B.carrier}
    (h : ∃ a₁ a₂, a₁ ≠ a₂ ∧ T a₁ = T a₂) :
    ¬ Measure.Injective A B T ∧ ¬ FullSubstitution A B T ∧
    (∀ Bcal : B.carrier → Prop, ¬ Nonempty (ExactCalibration A B Bcal T)) ∧
    ¬ IsomorphicTransposition A B T
```

[`LigoSpecious.fibre_obstructs`](../../RequestProject/LIGO_specious_measures.lean#L95)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L722) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.relation_not_reflected</code></summary>

```lean
theorem relation_not_reflected {A B : MeasStructure.{u} K σ} {T : A.carrier → B.carrier}
    {n : Nat} (r : σ.Rel n) (xs : Fin n → A.carrier)
    (hB : B.rel r (fun i => T (xs i))) (hA : ¬ A.rel r xs) :
    ¬ FullSubstitution A B T
```

[`LigoSpecious.relation_not_reflected`](../../RequestProject/LIGO_specious_measures.lean#L119)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L723) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.modelDiff_preservesOperation</code></summary>

```lean
theorem modelDiff_preservesOperation : PreservesOperation pairStr diffStr modelDiff
```

[`LigoSpecious.modelDiff_preservesOperation`](../../RequestProject/LIGO_specious_measures.lean#L154)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L727) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.modelDiff_homomorphic</code></summary>

```lean
theorem modelDiff_homomorphic : HomomorphicAssociation pairStr diffStr modelDiff
```

[`LigoSpecious.modelDiff_homomorphic`](../../RequestProject/LIGO_specious_measures.lean#L162)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L728) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modelDifference_commonMode_fibre</code></summary>

```lean
theorem ligo_modelDifference_commonMode_fibre :
    modelDiff (84, 84) = 0 ∧ modelDiff (98, 98) = 0 ∧ modelDiff (64, 64) = 0 ∧
    (∀ x y : Int, modelDiff (x, y) = 0 ↔ x = y) ∧
    (∀ x y g : Int, modelDiff (x + g, y + g) = modelDiff (x, y)) ∧
    (∀ x y x' y' : Int, modelDiff (x, y) = modelDiff (x', y') ↔
      ∃ g : Int, x' = x + g ∧ y' = y + g) ∧
    (∀ R : Int, R + (84 - R) = 84 ∧ modelDiff (84 - R, 84 - R) = 0)
```

[`LigoSpecious.ligo_modelDifference_commonMode_fibre`](../../RequestProject/LIGO_specious_measures.lean#L170)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L729) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.modelDiff_fibre_witness</code></summary>

```lean
theorem modelDiff_fibre_witness :
    ∃ a₁ a₂ : Int × Int, a₁ ≠ a₂ ∧ modelDiff a₁ = modelDiff a₂
```

[`LigoSpecious.modelDiff_fibre_witness`](../../RequestProject/LIGO_specious_measures.lean#L202)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L730) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modelDifference_not_injective</code></summary>

```lean
theorem ligo_modelDifference_not_injective : ¬ Measure.Injective pairStr diffStr modelDiff
```

[`LigoSpecious.ligo_modelDifference_not_injective`](../../RequestProject/LIGO_specious_measures.lean#L207)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L731) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modelDifference_not_fullSubstitution</code></summary>

```lean
theorem ligo_modelDifference_not_fullSubstitution : ¬ FullSubstitution pairStr diffStr modelDiff
```

[`LigoSpecious.ligo_modelDifference_not_fullSubstitution`](../../RequestProject/LIGO_specious_measures.lean#L211)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L732) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modelDifference_no_exact_calibration</code></summary>

```lean
theorem ligo_modelDifference_no_exact_calibration (Bcal : diffStr.carrier → Prop) :
    ¬ Nonempty (ExactCalibration pairStr diffStr Bcal modelDiff)
```

[`LigoSpecious.ligo_modelDifference_no_exact_calibration`](../../RequestProject/LIGO_specious_measures.lean#L216)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L733) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modelDifference_not_isomorphic_transposition</code></summary>

```lean
theorem ligo_modelDifference_not_isomorphic_transposition :
    ¬ IsomorphicTransposition pairStr diffStr modelDiff
```

[`LigoSpecious.ligo_modelDifference_not_isomorphic_transposition`](../../RequestProject/LIGO_specious_measures.lean#L222)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L734) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.diffSum_preservesOperation</code></summary>

```lean
theorem diffSum_preservesOperation : PreservesOperation pairStr pairStr diffSum
```

[`LigoSpecious.diffSum_preservesOperation`](../../RequestProject/LIGO_specious_measures.lean#L242)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L738) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.diffSum_eq_iff</code></summary>

```lean
theorem diffSum_eq_iff (a₁ a₂ : Int × Int) : a₁ = a₂ ↔ diffSum a₁ = diffSum a₂
```

[`LigoSpecious.diffSum_eq_iff`](../../RequestProject/LIGO_specious_measures.lean#L252)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L739) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.diffSum_lands</code></summary>

```lean
theorem diffSum_lands (a : Int × Int) : parityRange (diffSum a)
```

[`LigoSpecious.diffSum_lands`](../../RequestProject/LIGO_specious_measures.lean#L264)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L740) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.diffSum_recal_spec</code></summary>

```lean
theorem diffSum_recal_spec (b : Int × Int) (hb : parityRange b) :
    diffSum (diffSumRecal b) = b
```

[`LigoSpecious.diffSum_recal_spec`](../../RequestProject/LIGO_specious_measures.lean#L270)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L741) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modelDifference_anchor_isomorphism</code></summary>

```lean
theorem ligo_modelDifference_anchor_isomorphism :
    Isomorphic pairStr (pairStr.restrict parityRange diffSumCalibration.closedRange)
```

[`LigoSpecious.ligo_modelDifference_anchor_isomorphism`](../../RequestProject/LIGO_specious_measures.lean#L288)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L743) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_overall_bias_free_of_difference</code></summary>

```lean
theorem ligo_overall_bias_free_of_difference :
    ∀ d s : Int, (d + s) % 2 = 0 → ∃ e : Int × Int, modelDiff e = d ∧ e.1 + e.2 = s
```

[`LigoSpecious.ligo_overall_bias_free_of_difference`](../../RequestProject/LIGO_specious_measures.lean#L294)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L744) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modelDifference_width_not_reflected</code></summary>

```lean
theorem ligo_modelDifference_width_not_reflected (w g : Int) (hw : 0 ≤ w) (hg : w < g) :
    ¬ FullSubstitution errStr difWStr modelDiff
```

[`LigoSpecious.ligo_modelDifference_width_not_reflected`](../../RequestProject/LIGO_specious_measures.lean#L339)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L751) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modelDifference_q_widths_not_reflected</code></summary>

```lean
theorem ligo_modelDifference_q_widths_not_reflected :
    ((14 : Int) < 15 ∧ modelDiff (15, 15) = 0) ∧ ((20 : Int) < 21 ∧ modelDiff (21, 21) = 0) ∧
    ¬ FullSubstitution errStr difWStr modelDiff
```

[`LigoSpecious.ligo_modelDifference_q_widths_not_reflected`](../../RequestProject/LIGO_specious_measures.lean#L352)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L752) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.maxN_of_le</code></summary>

```lean
theorem maxN_of_le {x y : Nat} (h : x ≤ y) : maxN x y = y
```

[`LigoSpecious.maxN_of_le`](../../RequestProject/LIGO_specious_measures.lean#L397)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L757) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.maxN_of_lt</code></summary>

```lean
theorem maxN_of_lt {x y : Nat} (h : y < x) : maxN x y = x
```

[`LigoSpecious.maxN_of_lt`](../../RequestProject/LIGO_specious_measures.lean#L402)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L758) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.chiPNum_nrInjection</code></summary>

```lean
theorem chiPNum_nrInjection (sinMicro : Int → Nat)
    (h1 : 322265 ≤ sinMicro 188 ∧ sinMicro 188 ≤ 322266)
    (h2 : 509041 ≤ sinMicro 1494 ∧ sinMicro 1494 ≤ 509042) :
    chiPNum sinMicro nrInjection = K2 81 * (67 * sinMicro 1494)
```

[`LigoSpecious.chiPNum_nrInjection`](../../RequestProject/LIGO_specious_measures.lean#L440)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L766) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_chiP_real_values</code></summary>

```lean
theorem ligo_chiP_real_values (sinMicro : Int → Nat)
    (h1 : 322265 ≤ sinMicro 188 ∧ sinMicro 188 ≤ 322266)
    (h2 : 509041 ≤ sinMicro 1494 ∧ sinMicro 1494 ≤ 509042) :
    K1 81 = 64300 ∧ K2 81 = 50544 ∧ chiPDen nrInjection = 6430000000000 ∧
    K1 81 * (34 * sinMicro 188) ≤ K2 81 * (67 * sinMicro 1494) ∧
    chiPNum sinMicro nrInjection = K2 81 * (67 * sinMicro 1494) ∧
    268093 * chiPDen nrInjection ≤ 1000000 * chiPNum sinMicro nrInjection ∧
    1000000 * chiPNum sinMicro nrInjection ≤ 268094 * chiPDen nrInjection ∧
    10957000 ≤ 34 * sinMicro 188 ∧ 34 * sinMicro 188 ≤ 10958000
```

[`LigoSpecious.ligo_chiP_real_values`](../../RequestProject/LIGO_specious_measures.lean#L458)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L767) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_chiP_injected_below_posterior_peak</code></summary>

```lean
theorem ligo_chiP_injected_below_posterior_peak (sinMicro : Int → Nat)
    (h1 : 322265 ≤ sinMicro 188 ∧ sinMicro 188 ≤ 322266)
    (h2 : 509041 ≤ sinMicro 1494 ∧ sinMicro 1494 ≤ 509042) :
    1000000 * chiPNum sinMicro nrInjection < 400000 * chiPDen nrInjection
```

[`LigoSpecious.ligo_chiP_injected_below_posterior_peak`](../../RequestProject/LIGO_specious_measures.lean#L488)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L768) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.sinAtTilts_windows</code></summary>

```lean
theorem sinAtTilts_windows :
    (322265 ≤ sinAtTilts 188 ∧ sinAtTilts 188 ≤ 322266) ∧
    (509041 ≤ sinAtTilts 1494 ∧ sinAtTilts 1494 ≤ 509042)
```

[`LigoSpecious.sinAtTilts_windows`](../../RequestProject/LIGO_specious_measures.lean#L502)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L770) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_chiP_real_values_closed</code></summary>

```lean
theorem ligo_chiP_real_values_closed :
    chiP sinAtTilts nrInjection = (1723840876368, 6430000000000)
```

[`LigoSpecious.ligo_chiP_real_values_closed`](../../RequestProject/LIGO_specious_measures.lean#L509)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L771) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.chiP_azimuth_invariant</code></summary>

```lean
theorem chiP_azimuth_invariant (sinMicro : Int → Nat) (s : SpinState) (p₁ p₂ : Int) :
    chiP sinMicro { s with ph1 := p₁, ph2 := p₂ } = chiP sinMicro s
```

[`LigoSpecious.chiP_azimuth_invariant`](../../RequestProject/LIGO_specious_measures.lean#L514)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L772) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.nrInjectionRot_ne</code></summary>

```lean
theorem nrInjectionRot_ne : nrInjectionRot ≠ nrInjection
```

[`LigoSpecious.nrInjectionRot_ne`](../../RequestProject/LIGO_specious_measures.lean#L519)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L773) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_chiP_azimuth_fibre</code></summary>

```lean
theorem ligo_chiP_azimuth_fibre :
    (∀ (sinMicro : Int → Nat) (s : SpinState) (p₁ p₂ : Int),
      chiP sinMicro { s with ph1 := p₁, ph2 := p₂ } = chiP sinMicro s) ∧
    (∀ sinMicro : Int → Nat, chiP sinMicro nrInjectionRot = chiP sinMicro nrInjection) ∧
    nrInjectionRot ≠ nrInjection ∧
    nrInjectionRot.ph1 - nrInjectionRot.ph2 ≠ nrInjection.ph1 - nrInjection.ph2
```

[`LigoSpecious.ligo_chiP_azimuth_fibre`](../../RequestProject/LIGO_specious_measures.lean#L528)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L774) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.chiP_fibre_witness</code></summary>

```lean
theorem chiP_fibre_witness (sinMicro : Int → Nat) :
    ∃ a₁ a₂ : SpinState, a₁ ≠ a₂ ∧ chiP sinMicro a₁ = chiP sinMicro a₂
```

[`LigoSpecious.chiP_fibre_witness`](../../RequestProject/LIGO_specious_measures.lean#L537)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L775) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_chiP_not_injective</code></summary>

```lean
theorem ligo_chiP_not_injective (sinMicro : Int → Nat) :
    ¬ Measure.Injective spinStr chiPStr (chiP sinMicro)
```

[`LigoSpecious.ligo_chiP_not_injective`](../../RequestProject/LIGO_specious_measures.lean#L542)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L776) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_chiP_not_fullSubstitution</code></summary>

```lean
theorem ligo_chiP_not_fullSubstitution (sinMicro : Int → Nat) :
    ¬ FullSubstitution spinStr chiPStr (chiP sinMicro)
```

[`LigoSpecious.ligo_chiP_not_fullSubstitution`](../../RequestProject/LIGO_specious_measures.lean#L548)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L777) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_chiP_no_exact_calibration</code></summary>

```lean
theorem ligo_chiP_no_exact_calibration (sinMicro : Int → Nat) (Bcal : chiPStr.carrier → Prop) :
    ¬ Nonempty (ExactCalibration spinStr chiPStr Bcal (chiP sinMicro))
```

[`LigoSpecious.ligo_chiP_no_exact_calibration`](../../RequestProject/LIGO_specious_measures.lean#L554)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L778) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_chiP_not_isomorphic_transposition</code></summary>

```lean
theorem ligo_chiP_not_isomorphic_transposition (sinMicro : Int → Nat) :
    ¬ IsomorphicTransposition spinStr chiPStr (chiP sinMicro)
```

[`LigoSpecious.ligo_chiP_not_isomorphic_transposition`](../../RequestProject/LIGO_specious_measures.lean#L560)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L779) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.chiP_primary_fibre</code></summary>

```lean
theorem chiP_primary_fibre (sinMicro : Int → Nat) (s : SpinState) (a : Nat)
    (h : K1 s.q * (s.a1 * sinMicro s.th1) ≤ K2 s.q * (s.a2 * sinMicro s.th2))
    (h' : K1 s.q * (a * sinMicro s.th1) ≤ K2 s.q * (s.a2 * sinMicro s.th2)) :
    chiP sinMicro { s with a1 := a } = chiP sinMicro s
```

[`LigoSpecious.chiP_primary_fibre`](../../RequestProject/LIGO_specious_measures.lean#L571)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L780) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_chiP_primarySpin_fibre</code></summary>

```lean
theorem ligo_chiP_primarySpin_fibre (sinMicro : Int → Nat)
    (h1 : 322265 ≤ sinMicro 188 ∧ sinMicro 188 ≤ 322266)
    (h2 : 509041 ≤ sinMicro 1494 ∧ sinMicro 1494 ≤ 509042) (a : Nat) (ha : a ≤ 83) :
    chiP sinMicro { nrInjection with a1 := a } = chiP sinMicro nrInjection
```

[`LigoSpecious.ligo_chiP_primarySpin_fibre`](../../RequestProject/LIGO_specious_measures.lean#L584)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L781) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_chiP_primarySpin_threshold</code></summary>

```lean
theorem ligo_chiP_primarySpin_threshold (sinMicro : Int → Nat)
    (h1 : 322265 ≤ sinMicro 188 ∧ sinMicro 188 ≤ 322266)
    (h2 : 509041 ≤ sinMicro 1494 ∧ sinMicro 1494 ≤ 509042) (a : Nat) (ha : 84 ≤ a) :
    chiP sinMicro { nrInjection with a1 := a } ≠ chiP sinMicro nrInjection
```

[`LigoSpecious.ligo_chiP_primarySpin_threshold`](../../RequestProject/LIGO_specious_measures.lean#L603)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L782) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_chiP_primarySpin_credible_intervals</code></summary>

```lean
theorem ligo_chiP_primarySpin_credible_intervals (sinMicro : Int → Nat)
    (h1 : 322265 ≤ sinMicro 188 ∧ sinMicro 188 ≤ 322266)
    (h2 : 509041 ≤ sinMicro 1494 ∧ sinMicro 1494 ≤ 509042) :
    (∀ a : Nat, 2 ≤ a → a ≤ 65 →
      chiP sinMicro { nrInjection with a1 := a } = chiP sinMicro nrInjection) ∧
    (∀ a : Nat, 2 ≤ a → a ≤ 78 →
      chiP sinMicro { nrInjection with a1 := a } = chiP sinMicro nrInjection) ∧
    chiP sinMicro { nrInjection with a1 := 85 } ≠ chiP sinMicro nrInjection
```

[`LigoSpecious.ligo_chiP_primarySpin_credible_intervals`](../../RequestProject/LIGO_specious_measures.lean#L631)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L783) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.overall_preservesOperation</code></summary>

```lean
theorem overall_preservesOperation : PreservesOperation post2Str overallStr overall
```

[`LigoSpecious.overall_preservesOperation`](../../RequestProject/LIGO_specious_measures.lean#L685)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L789) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.overall_homomorphic</code></summary>

```lean
theorem overall_homomorphic : HomomorphicAssociation post2Str overallStr overall
```

[`LigoSpecious.overall_homomorphic`](../../RequestProject/LIGO_specious_measures.lean#L695)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L790) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modelAverage_fibre</code></summary>

```lean
theorem ligo_modelAverage_fibre :
    (∀ (P : Post2) (δ : Int),
      overall ⟨P.eob1 + δ, P.eob2 - δ, P.imr1 - δ, P.imr2 + δ⟩ = overall P) ∧
    overall ⟨100, 0, 80, 20⟩ = (180, 20) ∧ overall ⟨90, 10, 90, 10⟩ = (180, 20) ∧
    (∀ fE fP : Int, 90 ≤ fE → fE ≤ 100 → 0 ≤ fP → fP ≤ 90 → fE + fP = 180 →
      overall ⟨fE, 100 - fE, fP, 100 - fP⟩ = (180, 20))
```

[`LigoSpecious.ligo_modelAverage_fibre`](../../RequestProject/LIGO_specious_measures.lean#L704)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L791) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modelAverage_bound_segment</code></summary>

```lean
theorem ligo_modelAverage_bound_segment (FE FP : Int → Int)
    (hE : ∀ x y : Int, x ≤ y → FE x ≤ FE y) (hP : ∀ x y : Int, x ≤ y → FP x ≤ FP y)
    (hEtop : ∀ x : Int, FE x ≤ 100) (hPbot : ∀ x : Int, 0 ≤ FP x)
    (xE xO xP : Int) (hEO : xE < xO) (hOP : xO < xP)
    (hE90 : FE xE = 90) (hP90 : FP xP = 90) (hO90 : FE xO + FP xO = 180) :
    90 ≤ FE xO ∧ FE xO ≤ 100 ∧ 80 ≤ FP xO ∧ FP xO ≤ 90 ∧
    overall ⟨FE xO, 100 - FE xO, FP xO, 100 - FP xO⟩ = (180, 20)
```

[`LigoSpecious.ligo_modelAverage_bound_segment`](../../RequestProject/LIGO_specious_measures.lean#L726)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L792) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.post2_witness_ne</code></summary>

```lean
theorem post2_witness_ne : (⟨100, 0, 80, 20⟩ : Post2) ≠ (⟨90, 10, 90, 10⟩ : Post2)
```

[`LigoSpecious.post2_witness_ne`](../../RequestProject/LIGO_specious_measures.lean#L742)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L793) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.modelAverage_fibre_witness</code></summary>

```lean
theorem modelAverage_fibre_witness :
    ∃ a₁ a₂ : Post2, a₁ ≠ a₂ ∧ overall a₁ = overall a₂
```

[`LigoSpecious.modelAverage_fibre_witness`](../../RequestProject/LIGO_specious_measures.lean#L748)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L794) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modelAverage_not_injective</code></summary>

```lean
theorem ligo_modelAverage_not_injective : ¬ Measure.Injective post2Str overallStr overall
```

[`LigoSpecious.ligo_modelAverage_not_injective`](../../RequestProject/LIGO_specious_measures.lean#L753)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L795) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modelAverage_not_fullSubstitution</code></summary>

```lean
theorem ligo_modelAverage_not_fullSubstitution : ¬ FullSubstitution post2Str overallStr overall
```

[`LigoSpecious.ligo_modelAverage_not_fullSubstitution`](../../RequestProject/LIGO_specious_measures.lean#L758)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L796) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modelAverage_no_exact_calibration</code></summary>

```lean
theorem ligo_modelAverage_no_exact_calibration (Bcal : overallStr.carrier → Prop) :
    ¬ Nonempty (ExactCalibration post2Str overallStr Bcal overall)
```

[`LigoSpecious.ligo_modelAverage_no_exact_calibration`](../../RequestProject/LIGO_specious_measures.lean#L764)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L797) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modelAverage_not_isomorphic_transposition</code></summary>

```lean
theorem ligo_modelAverage_not_isomorphic_transposition :
    ¬ IsomorphicTransposition post2Str overallStr overall
```

[`LigoSpecious.ligo_modelAverage_not_isomorphic_transposition`](../../RequestProject/LIGO_specious_measures.lean#L770)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L798) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.proj22_preservesOperation</code></summary>

```lean
theorem proj22_preservesOperation : PreservesOperation modeStr modeProjStr proj22
```

[`LigoSpecious.proj22_preservesOperation`](../../RequestProject/LIGO_specious_measures.lean#L814)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L804) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.proj22_homomorphic</code></summary>

```lean
theorem proj22_homomorphic : HomomorphicAssociation modeStr modeProjStr proj22
```

[`LigoSpecious.proj22_homomorphic`](../../RequestProject/LIGO_specious_measures.lean#L820)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L805) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.proj22_validMeasurementComparison</code></summary>

```lean
theorem proj22_validMeasurementComparison : ValidMeasurementComparison modeStr modeProjStr proj22
```

[`LigoSpecious.proj22_validMeasurementComparison`](../../RequestProject/LIGO_specious_measures.lean#L825)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L806) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modeProjection_fibre</code></summary>

```lean
theorem ligo_modeProjection_fibre :
    (∀ a b c d c' d' : Int, proj22 ⟨a, b, c, d⟩ = proj22 ⟨a, b, c', d'⟩) ∧
    proj22 ⟨5, 7, 0, 0⟩ = proj22 ⟨5, 7, 3, -3⟩ ∧
    (∀ h : ModeAmps, proj22 h = (0, 0) ↔ h.h22 = 0 ∧ h.h2m2 = 0)
```

[`LigoSpecious.ligo_modeProjection_fibre`](../../RequestProject/LIGO_specious_measures.lean#L832)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L807) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.modeAmps_witness_ne</code></summary>

```lean
theorem modeAmps_witness_ne : (⟨5, 7, 0, 0⟩ : ModeAmps) ≠ (⟨5, 7, 3, -3⟩ : ModeAmps)
```

[`LigoSpecious.modeAmps_witness_ne`](../../RequestProject/LIGO_specious_measures.lean#L845)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L808) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.modeProjection_fibre_witness</code></summary>

```lean
theorem modeProjection_fibre_witness :
    ∃ a₁ a₂ : ModeAmps, a₁ ≠ a₂ ∧ proj22 a₁ = proj22 a₂
```

[`LigoSpecious.modeProjection_fibre_witness`](../../RequestProject/LIGO_specious_measures.lean#L851)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L809) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modeProjection_not_injective</code></summary>

```lean
theorem ligo_modeProjection_not_injective :
    ¬ Measure.Injective modeStr modeProjStr proj22
```

[`LigoSpecious.ligo_modeProjection_not_injective`](../../RequestProject/LIGO_specious_measures.lean#L856)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L810) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modeProjection_not_fullSubstitution</code></summary>

```lean
theorem ligo_modeProjection_not_fullSubstitution :
    ¬ FullSubstitution modeStr modeProjStr proj22
```

[`LigoSpecious.ligo_modeProjection_not_fullSubstitution`](../../RequestProject/LIGO_specious_measures.lean#L862)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L811) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modeProjection_no_exact_calibration</code></summary>

```lean
theorem ligo_modeProjection_no_exact_calibration (Bcal : modeProjStr.carrier → Prop) :
    ¬ Nonempty (ExactCalibration modeStr modeProjStr Bcal proj22)
```

[`LigoSpecious.ligo_modeProjection_no_exact_calibration`](../../RequestProject/LIGO_specious_measures.lean#L868)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L812) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modeProjection_not_isomorphic_transposition</code></summary>

```lean
theorem ligo_modeProjection_not_isomorphic_transposition :
    ¬ IsomorphicTransposition modeStr modeProjStr proj22
```

[`LigoSpecious.ligo_modeProjection_not_isomorphic_transposition`](../../RequestProject/LIGO_specious_measures.lean#L874)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L813) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_modeProjection_linear_not_injective</code></summary>

```lean
theorem ligo_modeProjection_linear_not_injective :
    ValidMeasurementComparison modeStr modeProjStr proj22 ∧
    ¬ Measure.Injective modeStr modeProjStr proj22
```

[`LigoSpecious.ligo_modeProjection_linear_not_injective`](../../RequestProject/LIGO_specious_measures.lean#L881)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L814) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.int_neg_sq</code></summary>

```lean
theorem int_neg_sq (x : Int) : (-x) * (-x) = x * x
```

[`LigoSpecious.int_neg_sq`](../../RequestProject/LIGO_specious_measures.lean#L922)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L820) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.gaussExponent_resNeg</code></summary>

```lean
theorem gaussExponent_resNeg : ∀ r : List Int, gaussExponent (resNeg r) = gaussExponent r
```

[`LigoSpecious.gaussExponent_resNeg`](../../RequestProject/LIGO_specious_measures.lean#L928)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L821) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.exponent_pm_one</code></summary>

```lean
theorem exponent_pm_one : gaussExponent [1] = gaussExponent [-1]
```

[`LigoSpecious.exponent_pm_one`](../../RequestProject/LIGO_specious_measures.lean#L935)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L822) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_likelihood_sign_fibre</code></summary>

```lean
theorem ligo_likelihood_sign_fibre :
    (∀ r : List Int, gaussExponent (resNeg r) = gaussExponent r) ∧
    (∀ (β : Type) (g : Int → β) (r : List Int),
      g (gaussExponent (resNeg r)) = g (gaussExponent r)) ∧
    (∀ (x : Int) (xs : List Int), x ≠ 0 → resNeg (x :: xs) ≠ x :: xs) ∧
    gaussExponent [1, 0, 0, 3] = 10 ∧ gaussExponent [2, 1, 1, 2] = 10 ∧
    ([1, 0, 0, 3] : List Int) ≠ [2, 1, 1, 2]
```

[`LigoSpecious.ligo_likelihood_sign_fibre`](../../RequestProject/LIGO_specious_measures.lean#L943)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L823) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.likelihood_fibre_witness</code></summary>

```lean
theorem likelihood_fibre_witness (β : Type) (g : Int → β) :
    ∃ a₁ a₂ : List Int, a₁ ≠ a₂ ∧ g (gaussExponent a₁) = g (gaussExponent a₂)
```

[`LigoSpecious.likelihood_fibre_witness`](../../RequestProject/LIGO_specious_measures.lean#L961)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L824) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_likelihood_not_injective</code></summary>

```lean
theorem ligo_likelihood_not_injective (β : Type) (g : Int → β) :
    ¬ Measure.Injective resBare (weightBare β) (fun r => g (gaussExponent r))
```

[`LigoSpecious.ligo_likelihood_not_injective`](../../RequestProject/LIGO_specious_measures.lean#L985)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L827) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_likelihood_not_fullSubstitution</code></summary>

```lean
theorem ligo_likelihood_not_fullSubstitution (β : Type) (g : Int → β) :
    ¬ FullSubstitution resBare (weightBare β) (fun r => g (gaussExponent r))
```

[`LigoSpecious.ligo_likelihood_not_fullSubstitution`](../../RequestProject/LIGO_specious_measures.lean#L991)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L828) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_likelihood_no_exact_calibration</code></summary>

```lean
theorem ligo_likelihood_no_exact_calibration (β : Type) (g : Int → β)
    (Bcal : (weightBare β).carrier → Prop) :
    ¬ Nonempty (ExactCalibration resBare (weightBare β) Bcal (fun r => g (gaussExponent r)))
```

[`LigoSpecious.ligo_likelihood_no_exact_calibration`](../../RequestProject/LIGO_specious_measures.lean#L998)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L829) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_likelihood_not_isomorphic_transposition</code></summary>

```lean
theorem ligo_likelihood_not_isomorphic_transposition (β : Type) (g : Int → β) :
    ¬ IsomorphicTransposition resBare (weightBare β) (fun r => g (gaussExponent r))
```

[`LigoSpecious.ligo_likelihood_not_isomorphic_transposition`](../../RequestProject/LIGO_specious_measures.lean#L1005)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L830) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_likelihood_not_additive</code></summary>

```lean
theorem ligo_likelihood_not_additive : ¬ PreservesOperation resStr weightStr gaussExponent
```

[`LigoSpecious.ligo_likelihood_not_additive`](../../RequestProject/LIGO_specious_measures.lean#L1026)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L833) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.residual_weight_not_sameKind</code></summary>

```lean
theorem residual_weight_not_sameKind : ¬ SameKind resStr weightStr
```

[`LigoSpecious.residual_weight_not_sameKind`](../../RequestProject/LIGO_specious_measures.lean#L1031)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L834) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_residual_weight_not_comparable</code></summary>

```lean
theorem ligo_residual_weight_not_comparable :
    ¬ SameKind resStr weightStr ∧
    (∀ T : List Int → Int, ¬ ValidMeasurementComparison resStr weightStr T) ∧
    (∀ (Bcal : Int → Prop) (T : List Int → Int),
      ¬ Nonempty (ExactCalibration resStr weightStr Bcal T)) ∧
    ¬ Isomorphic resStr weightStr
```

[`LigoSpecious.ligo_residual_weight_not_comparable`](../../RequestProject/LIGO_specious_measures.lean#L1040)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L835) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.spin4_congr</code></summary>

```lean
theorem spin4_congr {a b c d a' b' c' d' : Int} (h₁ : a = a') (h₂ : b = b') (h₃ : c = c')
    (h₄ : d = d') : (⟨a, b, c, d⟩ : Spin4) = (⟨a', b', c', d'⟩ : Spin4)
```

[`LigoSpecious.spin4_congr`](../../RequestProject/LIGO_specious_measures.lean#L1104)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L843) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.imrSpin_preservesOperation</code></summary>

```lean
theorem imrSpin_preservesOperation : PreservesOperation spin6Str spin4Str imrSpin
```

[`LigoSpecious.imrSpin_preservesOperation`](../../RequestProject/LIGO_specious_measures.lean#L1113)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L844) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.imrSpin_homomorphic</code></summary>

```lean
theorem imrSpin_homomorphic : HomomorphicAssociation spin6Str spin4Str imrSpin
```

[`LigoSpecious.imrSpin_homomorphic`](../../RequestProject/LIGO_specious_measures.lean#L1125)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L845) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.imrSpin_eq_of</code></summary>

```lean
theorem imrSpin_eq_of {s s' : Spin6} (h1 : s.s1z = s'.s1z) (h2 : s.s2z = s'.s2z)
    (h3 : s.s1x + s.s2x = s'.s1x + s'.s2x) (h4 : s.s1y + s.s2y = s'.s1y + s'.s2y) :
    imrSpin s = imrSpin s'
```

[`LigoSpecious.imrSpin_eq_of`](../../RequestProject/LIGO_specious_measures.lean#L1130)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L846) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.imrSpin_surjective</code></summary>

```lean
theorem imrSpin_surjective : ∀ t : Spin4, ∃ s : Spin6, imrSpin s = t
```

[`LigoSpecious.imrSpin_surjective`](../../RequestProject/LIGO_specious_measures.lean#L1136)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L847) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_imrPhenom_spinCompression_fibre</code></summary>

```lean
theorem ligo_imrPhenom_spinCompression_fibre :
    (∀ s s' : Spin6, s.s1z = s'.s1z → s.s2z = s'.s2z →
      s.s1x + s.s2x = s'.s1x + s'.s2x → s.s1y + s.s2y = s'.s1y + s'.s2y →
      imrSpin s = imrSpin s') ∧
    (∀ u v : Int, imrSpin ⟨u, v, 0, -u, -v, 0⟩ = imrSpin ⟨0, 0, 0, 0, 0, 0⟩) ∧
    imrSpin ⟨1, 0, 0, 0, 0, 0⟩ = imrSpin ⟨0, 0, 0, 1, 0, 0⟩ ∧
    (⟨1, 0, 0, 0, 0, 0⟩ : Spin6) ≠ (⟨0, 0, 0, 1, 0, 0⟩ : Spin6)
```

[`LigoSpecious.ligo_imrPhenom_spinCompression_fibre`](../../RequestProject/LIGO_specious_measures.lean#L1148)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L848) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.imrSpin_fibre_witness</code></summary>

```lean
theorem imrSpin_fibre_witness :
    ∃ a₁ a₂ : Spin6, a₁ ≠ a₂ ∧ imrSpin a₁ = imrSpin a₂
```

[`LigoSpecious.imrSpin_fibre_witness`](../../RequestProject/LIGO_specious_measures.lean#L1165)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L849) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_imrPhenom_spinCompression_not_injective</code></summary>

```lean
theorem ligo_imrPhenom_spinCompression_not_injective :
    ¬ Measure.Injective spin6Str spin4Str imrSpin
```

[`LigoSpecious.ligo_imrPhenom_spinCompression_not_injective`](../../RequestProject/LIGO_specious_measures.lean#L1171)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L850) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_imrPhenom_spinCompression_not_fullSubstitution</code></summary>

```lean
theorem ligo_imrPhenom_spinCompression_not_fullSubstitution :
    ¬ FullSubstitution spin6Str spin4Str imrSpin
```

[`LigoSpecious.ligo_imrPhenom_spinCompression_not_fullSubstitution`](../../RequestProject/LIGO_specious_measures.lean#L1176)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L851) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_imrPhenom_spinCompression_no_exact_calibration</code></summary>

```lean
theorem ligo_imrPhenom_spinCompression_no_exact_calibration (Bcal : spin4Str.carrier → Prop) :
    ¬ Nonempty (ExactCalibration spin6Str spin4Str Bcal imrSpin)
```

[`LigoSpecious.ligo_imrPhenom_spinCompression_no_exact_calibration`](../../RequestProject/LIGO_specious_measures.lean#L1181)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L852) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>

<details>
<summary><code>LigoSpecious.ligo_imrPhenom_spinCompression_not_isomorphic_transposition</code></summary>

```lean
theorem ligo_imrPhenom_spinCompression_not_isomorphic_transposition :
    ¬ IsomorphicTransposition spin6Str spin4Str imrSpin
```

[`LigoSpecious.ligo_imrPhenom_spinCompression_not_isomorphic_transposition`](../../RequestProject/LIGO_specious_measures.lean#L1187)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L853) · [Accepted checker runs](../../verification/evidence/checkers.log#L41)

</details>
