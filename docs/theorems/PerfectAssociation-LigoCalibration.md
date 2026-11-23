# Faithful readings and affine calibration

Theorems distinguish preservation of differences, injectivity and preservation of ordinary addition. Positive tolerance is not transitive. The pair of readings at zero and one recovers affine gain and offset.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [association export roots](../../verification/roots/association.txt)

[Full Lean source](../../PerfectAssociation/LigoCalibration.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>LigoCalibration.faithful_substitutes</code></summary>

```lean
theorem faithful_substitutes {P : Sort u} {R : Sort v} {C : P → R} (h : Faithful C) :
    Substitutes C
```

[`LigoCalibration.faithful_substitutes`](../../PerfectAssociation/LigoCalibration.lean#L38)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L100) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.substitutes_faithful</code></summary>

```lean
theorem substitutes_faithful {P : Sort u} {R : Sort v} {C : P → R} (h : Substitutes C) :
    Faithful C
```

[`LigoCalibration.substitutes_faithful`](../../PerfectAssociation/LigoCalibration.lean#L42)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L101) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.faithful_chains</code></summary>

```lean
theorem faithful_chains {P : Sort u} {R : Sort v} {C : P → R} (h : Faithful C) :
    Chains C
```

[`LigoCalibration.faithful_chains`](../../PerfectAssociation/LigoCalibration.lean#L46)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L102) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.chains_faithful</code></summary>

```lean
theorem chains_faithful {P : Sort u} {R : Sort v} {C : P → R} (h : Chains C) :
    Faithful C
```

[`LigoCalibration.chains_faithful`](../../PerfectAssociation/LigoCalibration.lean#L50)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L103) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.faithful_valid_for_all</code></summary>

```lean
theorem faithful_valid_for_all {P : Sort u} {R : Sort v} {γ : Sort w} {C : P → R}
    (h : Faithful C) (T : P → γ) : LigoCongruence.IsValidFor C T
```

[`LigoCalibration.faithful_valid_for_all`](../../PerfectAssociation/LigoCalibration.lean#L55)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L104) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.faithful_iff_valid_id</code></summary>

```lean
theorem faithful_iff_valid_id {P : Sort u} {R : Sort v} (C : P → R) :
    Faithful C ↔ LigoCongruence.IsValidFor C (fun a : P => a)
```

[`LigoCalibration.faithful_iff_valid_id`](../../PerfectAssociation/LigoCalibration.lean#L60)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L105) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.faithful_characterisation</code></summary>

```lean
theorem faithful_characterisation {P : Sort u} {R : Sort v} (C : P → R) :
    (Faithful C ↔ Substitutes C) ∧ (Faithful C ↔ Chains C) ∧
    (Faithful C ↔ ∀ T : P → P, LigoCongruence.IsValidFor C T)
```

[`LigoCalibration.faithful_characterisation`](../../PerfectAssociation/LigoCalibration.lean#L65)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L106) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.faithful_iff_preserves_ne</code></summary>

```lean
theorem faithful_iff_preserves_ne {P : Sort u} {R : Sort v} [DecidableEq P] (C : P → R) :
    Faithful C ↔ ∀ a b, a ≠ b → C a ≠ C b
```

[`LigoCalibration.faithful_iff_preserves_ne`](../../PerfectAssociation/LigoCalibration.lean#L73)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L107) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.substitution_fails</code></summary>

```lean
theorem substitution_fails {P : Sort u} {R : Sort v} {C : P → R} {a b : P}
    (hC : C a = C b) (hne : a ≠ b) : ¬ Substitutes C
```

[`LigoCalibration.substitution_fails`](../../PerfectAssociation/LigoCalibration.lean#L79)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L108) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.separating_property</code></summary>

```lean
theorem separating_property {P : Sort u} {a b : P} (hne : a ≠ b) :
    ∃ Q : P → Prop, Q a ∧ ¬ Q b
```

[`LigoCalibration.separating_property`](../../PerfectAssociation/LigoCalibration.lean#L84)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L109) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.chain_fails</code></summary>

```lean
theorem chain_fails {P : Sort u} {R : Sort v} {C : P → R} {a b : P}
    (hC : C a = C b) (hne : a ≠ b) : ¬ Chains C
```

[`LigoCalibration.chain_fails`](../../PerfectAssociation/LigoCalibration.lean#L89)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L110) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.merged_pair_invalid</code></summary>

```lean
theorem merged_pair_invalid {P : Sort u} {R : Sort v} {C : P → R} {a b : P}
    (hC : C a = C b) (hne : a ≠ b) : LigoCongruence.IsInvalidFor C (fun t : P => t)
```

[`LigoCalibration.merged_pair_invalid`](../../PerfectAssociation/LigoCalibration.lean#L94)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L111) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.chain_unfaithful</code></summary>

```lean
theorem chain_unfaithful {P : Sort u} {R : Sort v} {S : Sort w} (C₁ : P → R) (C₂ : R → S)
    (h : ¬ Faithful C₁) : ¬ Faithful (fun a => C₂ (C₁ a))
```

[`LigoCalibration.chain_unfaithful`](../../PerfectAssociation/LigoCalibration.lean#L99)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L112) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.faithful_comp</code></summary>

```lean
theorem faithful_comp {P : Sort u} {R : Sort v} {S : Sort w} {C₁ : P → R} {C₂ : R → S}
    (h₁ : Faithful C₁) (h₂ : Faithful C₂) : Faithful (fun a => C₂ (C₁ a))
```

[`LigoCalibration.faithful_comp`](../../PerfectAssociation/LigoCalibration.lean#L103)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L113) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.iso_faithful</code></summary>

```lean
theorem iso_faithful {P : Sort u} {R : Sort v} (e : EqualityBridge.Iso P R) :
    Faithful e.toFun
```

[`LigoCalibration.iso_faithful`](../../PerfectAssociation/LigoCalibration.lean#L109)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L114) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.iso_preserves_ne</code></summary>

```lean
theorem iso_preserves_ne {P : Sort u} {R : Sort v} (e : EqualityBridge.Iso P R) {a b : P}
    (hne : a ≠ b) : e.toFun a ≠ e.toFun b
```

[`LigoCalibration.iso_preserves_ne`](../../PerfectAssociation/LigoCalibration.lean#L113)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L115) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.iso_reflects_ne</code></summary>

```lean
theorem iso_reflects_ne {P : Sort u} {R : Sort v} (e : EqualityBridge.Iso P R) {a b : P}
    (hne : e.toFun a ≠ e.toFun b) : a ≠ b
```

[`LigoCalibration.iso_reflects_ne`](../../PerfectAssociation/LigoCalibration.lean#L117)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L116) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.faithful_iff_carriers_detect_equality</code></summary>

```lean
theorem faithful_iff_carriers_detect_equality {P : Sort u} {R : Sort v} (C : P → R) :
    Faithful C ↔ ∀ a b : P,
      (∀ F : R → Type w, Nonempty (EqualityBridge.Iso (F (C a)) (F (C b)))) → a = b
```

[`LigoCalibration.faithful_iff_carriers_detect_equality`](../../PerfectAssociation/LigoCalibration.lean#L131)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L118) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.carriers_gap</code></summary>

```lean
theorem carriers_gap {P : Sort u} {R : Sort v} (C : P → R) {a b : P}
    (hC : C a = C b) (hne : a ≠ b) :
    (∀ F : R → Type w, Nonempty (EqualityBridge.Iso (F (C a)) (F (C b)))) ∧
    ¬ (∀ F : P → Type w, Nonempty (EqualityBridge.Iso (F a) (F b)))
```

[`LigoCalibration.carriers_gap`](../../PerfectAssociation/LigoCalibration.lean#L138)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L119) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.psi15_not_faithful</code></summary>

```lean
theorem psi15_not_faithful (c : Int) :
    ¬ Faithful (fun s : Int × Int => LigoCongruence.psi15 c s.1 s.2)
```

[`LigoCalibration.psi15_not_faithful`](../../PerfectAssociation/LigoCalibration.lean#L146)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L120) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.waveform_carriers_iso_states_differ</code></summary>

```lean
theorem waveform_carriers_iso_states_differ (c : Int) :
    ∃ s t : Int × Int,
      (∀ F : Int → Type w, Nonempty (EqualityBridge.Iso
        (F (LigoCongruence.psi15 c s.1 s.2)) (F (LigoCongruence.psi15 c t.1 t.2)))) ∧ s ≠ t
```

[`LigoCalibration.waveform_carriers_iso_states_differ`](../../PerfectAssociation/LigoCalibration.lean#L152)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L121) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.affine_unit_gain_faithful</code></summary>

```lean
theorem affine_unit_gain_faithful (b : Int) : Faithful (Affine 1 b)
```

[`LigoCalibration.affine_unit_gain_faithful`](../../PerfectAssociation/LigoCalibration.lean#L163)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L122) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.affine_zero_gain_not_faithful</code></summary>

```lean
theorem affine_zero_gain_not_faithful (b : Int) : ¬ Faithful (Affine 0 b)
```

[`LigoCalibration.affine_zero_gain_not_faithful`](../../PerfectAssociation/LigoCalibration.lean#L169)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L123) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.affine_faithful_iff</code></summary>

```lean
theorem affine_faithful_iff (a b : Int) : Faithful (Affine a b) ↔ a ≠ 0
```

[`LigoCalibration.affine_faithful_iff`](../../PerfectAssociation/LigoCalibration.lean#L175)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L124) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.faithful_hom_independent</code></summary>

```lean
theorem faithful_hom_independent :
    (Faithful (Affine 1 0) ∧ AdditiveHom (Affine 1 0)) ∧
    (Faithful (Affine 1 1) ∧ ¬ AdditiveHom (Affine 1 1)) ∧
    (¬ Faithful (Affine 0 0) ∧ AdditiveHom (Affine 0 0)) ∧
    (¬ Faithful (Affine 0 1) ∧ ¬ AdditiveHom (Affine 0 1))
```

[`LigoCalibration.faithful_hom_independent`](../../PerfectAssociation/LigoCalibration.lean#L181)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L125) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.offset_preserves_differences</code></summary>

```lean
theorem offset_preserves_differences (b x y : Int) :
    Affine 1 b x - Affine 1 b y = x - y
```

[`LigoCalibration.offset_preserves_differences`](../../PerfectAssociation/LigoCalibration.lean#L194)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L126) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.offset_iso_not_hom</code></summary>

```lean
theorem offset_iso_not_hom (c : Int) (hc : c ≠ 0) :
    (∃ e : EqualityBridge.Iso Int Int, e.toFun = Affine 1 c) ∧ ¬ AdditiveHom (Affine 1 c)
```

[`LigoCalibration.offset_iso_not_hom`](../../PerfectAssociation/LigoCalibration.lean#L214)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L128) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.affine_comp</code></summary>

```lean
theorem affine_comp (a₁ b₁ a₂ b₂ z : Int) :
    Affine a₂ b₂ (Affine a₁ b₁ z) = Affine (a₂ * a₁) (a₂ * b₁ + b₂) z
```

[`LigoCalibration.affine_comp`](../../PerfectAssociation/LigoCalibration.lean#L220)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L129) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.hom_comp</code></summary>

```lean
theorem hom_comp {f g : Int → Int} (hf : AdditiveHom f) (hg : AdditiveHom g) :
    AdditiveHom (fun z => g (f z))
```

[`LigoCalibration.hom_comp`](../../PerfectAssociation/LigoCalibration.lean#L226)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L130) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.affine_defect_everywhere</code></summary>

```lean
theorem affine_defect_everywhere (a b u v : Int) (hb : b ≠ 0) :
    Affine a b (u + v) ≠ Affine a b u + Affine a b v
```

[`LigoCalibration.affine_defect_everywhere`](../../PerfectAssociation/LigoCalibration.lean#L232)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L131) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.offset_scale_checkpoint</code></summary>

```lean
theorem offset_scale_checkpoint :
    Affine 1 1 2 = 3 ∧ Affine 1 1 (2 + 2) = 5 ∧ Affine 1 1 2 + Affine 1 1 2 = 6 ∧
    AdditiveDefect (Affine 1 1) 2 2 = -1
```

[`LigoCalibration.offset_scale_checkpoint`](../../PerfectAssociation/LigoCalibration.lean#L243)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L132) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.within_refl</code></summary>

```lean
theorem within_refl (ε a : Nat) : Within ε a a
```

[`LigoCalibration.within_refl`](../../PerfectAssociation/LigoCalibration.lean#L256)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L134) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.within_symm</code></summary>

```lean
theorem within_symm {ε a b : Nat} (h : Within ε a b) : Within ε b a
```

[`LigoCalibration.within_symm`](../../PerfectAssociation/LigoCalibration.lean#L259)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L135) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.within_not_transitive</code></summary>

```lean
theorem within_not_transitive (ε : Nat) (hε : 0 < ε) :
    ¬ ∀ a b c : Nat, Within ε a b → Within ε b c → Within ε a c
```

[`LigoCalibration.within_not_transitive`](../../PerfectAssociation/LigoCalibration.lean#L263)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L136) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.within_not_a_kernel</code></summary>

```lean
theorem within_not_a_kernel (ε : Nat) (hε : 0 < ε) {X : Sort u} :
    ¬ ∃ f : Nat → X, ∀ a b, f a = f b ↔ Within ε a b
```

[`LigoCalibration.within_not_a_kernel`](../../PerfectAssociation/LigoCalibration.lean#L275)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L137) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.perturbation_exact</code></summary>

```lean
theorem perturbation_exact : amPerMm = 500000000000000 * perturbationAm
```

[`LigoCalibration.perturbation_exact`](../../PerfectAssociation/LigoCalibration.lean#L286)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L140) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.margin_chain_at_scale</code></summary>

```lean
theorem margin_chain_at_scale :
    Within 1 0 1 ∧ Within 1 1 perturbationAm ∧ ¬ Within 1 0 perturbationAm
```

[`LigoCalibration.margin_chain_at_scale`](../../PerfectAssociation/LigoCalibration.lean#L290)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L141) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.one_anchor_invalid_for_gain</code></summary>

```lean
theorem one_anchor_invalid_for_gain (z₀ : Int) :
    LigoCongruence.IsInvalidFor (fun p : Int × Int => Affine p.1 p.2 z₀) (fun p => p.1)
```

[`LigoCalibration.one_anchor_invalid_for_gain`](../../PerfectAssociation/LigoCalibration.lean#L298)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L142) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.one_anchor_invalid_for_offset</code></summary>

```lean
theorem one_anchor_invalid_for_offset (z₀ : Int) (hz : z₀ ≠ 0) :
    LigoCongruence.IsInvalidFor (fun p : Int × Int => Affine p.1 p.2 z₀) (fun p => p.2)
```

[`LigoCalibration.one_anchor_invalid_for_offset`](../../PerfectAssociation/LigoCalibration.lean#L307)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L143) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.zero_anchor_identifies_offset</code></summary>

```lean
theorem zero_anchor_identifies_offset :
    LigoCongruence.IsValidFor (fun p : Int × Int => Affine p.1 p.2 0) (fun p => p.2)
```

[`LigoCalibration.zero_anchor_identifies_offset`](../../PerfectAssociation/LigoCalibration.lean#L316)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L144) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCalibration.zero_unit_anchors_valid</code></summary>

```lean
theorem zero_unit_anchors_valid :
    LigoCongruence.IsValidFor
      (fun p : Int × Int => (Affine p.1 p.2 0, Affine p.1 p.2 1)) (fun p => p)
```

[`LigoCalibration.zero_unit_anchors_valid`](../../PerfectAssociation/LigoCalibration.lean#L326)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L145) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>
