# Common errors, reference anchors and statistical tests

The common shift leaves the difference fixed. Linear targets recoverable from a suite annihilate its kernel. The model of source, offset and differential error also supplies prior transport, uncertainty and KS witnesses.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [compression export roots](../../verification/roots/compression.txt)

[Full Lean source](../../PerfectAssociation/LigoNullSpace.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>LigoNullSpace.sd_det</code></summary>

```lean
theorem sd_det : det2 1 1 1 (-1) = -2
```

[`LigoNullSpace.sd_det`](../../PerfectAssociation/LigoNullSpace.lean#L70)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L334) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.sd_inverse</code></summary>

```lean
theorem sd_inverse (x₁ x₂ : Int) :
    2 * x₁ = sumC (x₁, x₂) + difC (x₁, x₂) ∧ 2 * x₂ = sumC (x₁, x₂) - difC (x₁, x₂)
```

[`LigoNullSpace.sd_inverse`](../../PerfectAssociation/LigoNullSpace.lean#L73)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L335) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.sd_injective</code></summary>

```lean
theorem sd_injective : IsValidFor sdMap (fun X : Int × Int => X)
```

[`LigoNullSpace.sd_injective`](../../PerfectAssociation/LigoNullSpace.lean#L79)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L336) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.common_shift</code></summary>

```lean
theorem common_shift (x₁ x₂ g : Int) :
    difC (x₁ + g, x₂ + g) = difC (x₁, x₂) ∧ sumC (x₁ + g, x₂ + g) = sumC (x₁, x₂) + 2 * g
```

[`LigoNullSpace.common_shift`](../../PerfectAssociation/LigoNullSpace.lean#L89)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L337) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.difC_fibre</code></summary>

```lean
theorem difC_fibre (x₁ x₂ y₁ y₂ : Int) :
    difC (x₁, x₂) = difC (y₁, y₂) ↔ ∃ g : Int, y₁ = x₁ + g ∧ y₂ = x₂ + g
```

[`LigoNullSpace.difC_fibre`](../../PerfectAssociation/LigoNullSpace.lean#L95)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L338) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.difC_zero_iff</code></summary>

```lean
theorem difC_zero_iff (x₁ x₂ : Int) : difC (x₁, x₂) = 0 ↔ x₁ = x₂
```

[`LigoNullSpace.difC_zero_iff`](../../PerfectAssociation/LigoNullSpace.lean#L106)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L339) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.agreement_is_not_level</code></summary>

```lean
theorem agreement_is_not_level (P g : Int) :
    difC (P + g, P + g) = 0 ∧ sumC (P + g, P + g) - 2 * P = 2 * g
```

[`LigoNullSpace.agreement_is_not_level`](../../PerfectAssociation/LigoNullSpace.lean#L116)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L340) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.difC_invalid_for_sum</code></summary>

```lean
theorem difC_invalid_for_sum : IsInvalidFor difC sumC
```

[`LigoNullSpace.difC_invalid_for_sum`](../../PerfectAssociation/LigoNullSpace.lean#L122)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L341) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.sum_not_factor</code></summary>

```lean
theorem sum_not_factor : ¬ ∃ w : Int → Int, ∀ X, sumC X = w (difC X)
```

[`LigoNullSpace.sum_not_factor`](../../PerfectAssociation/LigoNullSpace.lean#L126)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L342) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.sum_separates</code></summary>

```lean
theorem sum_separates (X Y : Int × Int) (hD : Ker difC X Y)
    (hne : ¬ Ker (fun Z : Int × Int => Z) X Y) : ¬ Ker sumC X Y
```

[`LigoNullSpace.sum_separates`](../../PerfectAssociation/LigoNullSpace.lean#L130)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L343) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.sum_anchors_difference</code></summary>

```lean
theorem sum_anchors_difference :
    IsValidFor (fun X : Int × Int => (difC X, sumC X)) (fun X : Int × Int => X)
```

[`LigoNullSpace.sum_anchors_difference`](../../PerfectAssociation/LigoNullSpace.lean#L143)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L344) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.hanford_sd</code></summary>

```lean
theorem hanford_sd :
    sdMap (rStar, rStar) = (7938490295413130, 0) ∧
    sdMap (rStar + am, rStar + am) = (9938490295413130, 0) ∧
    sdMap (rStar + 100 * am, rStar + 100 * am) = (207938490295413130, 0) ∧
    sdMap (rStarBig, rStarBig) = (793849029541313000000000000, 0) ∧
    rStarBig = 396 * nm + 924514770656500000000000
```

[`LigoNullSpace.hanford_sd`](../../PerfectAssociation/LigoNullSpace.lean#L165)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L349) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.hanford_levels_merged</code></summary>

```lean
theorem hanford_levels_merged :
    IsInvalidFor difC sumC ∧
    Ker difC (rStar, rStar) (rStar + 100 * am, rStar + 100 * am) ∧
    Ker difC (rStar, rStar) (rStarBig, rStarBig) ∧
    ¬ Ker sumC (rStar, rStar) (rStarBig, rStarBig)
```

[`LigoNullSpace.hanford_levels_merged`](../../PerfectAssociation/LigoNullSpace.lean#L174)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L350) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.tableI_q_common_line</code></summary>

```lean
theorem tableI_q_common_line :
    difC (84, 84) = 0 ∧ sumC (84, 84) = 168 ∧
    ∀ k ∈ List.range 35, difC (64 + Int.ofNat k, 64 + Int.ofNat k) = 0
```

[`LigoNullSpace.tableI_q_common_line`](../../PerfectAssociation/LigoNullSpace.lean#L184)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L351) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.projector_resolution</code></summary>

```lean
theorem projector_resolution (x₁ x₂ : Int) :
    (projP2 (x₁, x₂)).1 + (projM2 (x₁, x₂)).1 = 2 * x₁ ∧
    (projP2 (x₁, x₂)).2 + (projM2 (x₁, x₂)).2 = 2 * x₂
```

[`LigoNullSpace.projector_resolution`](../../PerfectAssociation/LigoNullSpace.lean#L198)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L354) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.projector_squares</code></summary>

```lean
theorem projector_squares (x₁ x₂ : Int) :
    projP2 (projP2 (x₁, x₂)) = (2 * (x₁ + x₂), 2 * (x₁ + x₂)) ∧
    projM2 (projM2 (x₁, x₂)) = (2 * (x₁ - x₂), 2 * (x₂ - x₁)) ∧
    projM2 (projP2 (x₁, x₂)) = (0, 0) ∧ projP2 (projM2 (x₁, x₂)) = (0, 0)
```

[`LigoNullSpace.projector_squares`](../../PerfectAssociation/LigoNullSpace.lean#L205)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L355) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.projM2_common</code></summary>

```lean
theorem projM2_common (c : Int) : projM2 (c, c) = (0, 0)
```

[`LigoNullSpace.projM2_common`](../../PerfectAssociation/LigoNullSpace.lean#L220)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L356) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.linT_shift</code></summary>

```lean
theorem linT_shift (a b x₁ x₂ c : Int) :
    linT a b (x₁ + c, x₂ + c) = linT a b (x₁, x₂) + (a + b) * c
```

[`LigoNullSpace.linT_shift`](../../PerfectAssociation/LigoNullSpace.lean#L230)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L358) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.linT_valid_iff</code></summary>

```lean
theorem linT_valid_iff (a b : Int) : IsValidFor difC (linT a b) ↔ a + b = 0
```

[`LigoNullSpace.linT_valid_iff`](../../PerfectAssociation/LigoNullSpace.lean#L238)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L359) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.sum_not_valid_for_difference</code></summary>

```lean
theorem sum_not_valid_for_difference : ¬ IsValidFor difC (linT 1 1)
```

[`LigoNullSpace.sum_not_valid_for_difference`](../../PerfectAssociation/LigoNullSpace.lean#L256)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L360) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.difference_valid_for_difference</code></summary>

```lean
theorem difference_valid_for_difference : IsValidFor difC (linT 1 (-1))
```

[`LigoNullSpace.difference_valid_for_difference`](../../PerfectAssociation/LigoNullSpace.lean#L260)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L361) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.no_bound_from_difference</code></summary>

```lean
theorem no_bound_from_difference (B : Int → Int) :
    ∃ X : Int × Int, difC X = 0 ∧ B (difC X) < sumC X
```

[`LigoNullSpace.no_bound_from_difference`](../../PerfectAssociation/LigoNullSpace.lean#L267)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L362) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.no_finite_bound</code></summary>

```lean
theorem no_finite_bound : ¬ ∃ B : Int → Int, ∀ X : Int × Int, sumC X ≤ B (difC X)
```

[`LigoNullSpace.no_finite_bound`](../../PerfectAssociation/LigoNullSpace.lean#L284)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L363) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.rule_errs_on_pair</code></summary>

```lean
theorem rule_errs_on_pair {α : Sort u} {β : Sort v} {γ : Sort w} (Φ : α → β) (R : α → γ)
    {a b : α} (hΦ : Φ a = Φ b) (hR : R a ≠ R b) (rule : β → γ) :
    ¬ (rule (Φ a) = R a ∧ rule (Φ b) = R b)
```

[`LigoNullSpace.rule_errs_on_pair`](../../PerfectAssociation/LigoNullSpace.lean#L292)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L364) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.estimate_error_split</code></summary>

```lean
theorem estimate_error_split (e S₁ S₂ : Int) :
    S₂ - S₁ ≤ 2 * (e - S₁) ∨ S₂ - S₁ ≤ 2 * (S₂ - e)
```

[`LigoNullSpace.estimate_error_split`](../../PerfectAssociation/LigoNullSpace.lean#L298)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L365) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.difference_estimator_unbounded</code></summary>

```lean
theorem difference_estimator_unbounded (f : Int → Int) (K : Int) :
    ∃ X : Int × Int, difC X = 0 ∧ (K ≤ f (difC X) - sumC X ∨ K ≤ sumC X - f (difC X))
```

[`LigoNullSpace.difference_estimator_unbounded`](../../PerfectAssociation/LigoNullSpace.lean#L304)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L366) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.obs_formulas</code></summary>

```lean
theorem obs_formulas (θ : PGD) : obsD θ = 2 * θ.d ∧ obsS θ = 2 * (θ.P + θ.g)
```

[`LigoNullSpace.obs_formulas`](../../PerfectAssociation/LigoNullSpace.lean#L341)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L372) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.obsD_level_free</code></summary>

```lean
theorem obsD_level_free (P g d : Int) : obsD ⟨P, g, d⟩ = 2 * d
```

[`LigoNullSpace.obsD_level_free`](../../PerfectAssociation/LigoNullSpace.lean#L347)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L373) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.obsD_kernel</code></summary>

```lean
theorem obsD_kernel :
    (∀ θ θ' : PGD, obsD θ = obsD θ' ↔ θ.d = θ'.d) ∧ obsD ⟨1, 0, 0⟩ = 0 ∧ obsD ⟨0, 1, 0⟩ = 0
```

[`LigoNullSpace.obsD_kernel`](../../PerfectAssociation/LigoNullSpace.lean#L351)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L374) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.obsD_valid_for_d</code></summary>

```lean
theorem obsD_valid_for_d : IsValidFor obsD PGD.d
```

[`LigoNullSpace.obsD_valid_for_d`](../../PerfectAssociation/LigoNullSpace.lean#L364)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L375) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.obsD_invalid_for_P</code></summary>

```lean
theorem obsD_invalid_for_P : IsInvalidFor obsD PGD.P
```

[`LigoNullSpace.obsD_invalid_for_P`](../../PerfectAssociation/LigoNullSpace.lean#L368)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L376) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.obsD_invalid_for_g</code></summary>

```lean
theorem obsD_invalid_for_g : IsInvalidFor obsD PGD.g
```

[`LigoNullSpace.obsD_invalid_for_g`](../../PerfectAssociation/LigoNullSpace.lean#L372)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L377) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.obsD_invalid_for_level</code></summary>

```lean
theorem obsD_invalid_for_level : IsInvalidFor obsD (fun θ : PGD => θ.P + θ.g)
```

[`LigoNullSpace.obsD_invalid_for_level`](../../PerfectAssociation/LigoNullSpace.lean#L376)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L378) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.obsSD_kernel</code></summary>

```lean
theorem obsSD_kernel (θ θ' : PGD) :
    obsSD θ = obsSD θ' ↔ θ.P + θ.g = θ'.P + θ'.g ∧ θ.d = θ'.d
```

[`LigoNullSpace.obsSD_kernel`](../../PerfectAssociation/LigoNullSpace.lean#L380)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L379) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.obsSD_orbit</code></summary>

```lean
theorem obsSD_orbit (P g d c : Int) : obsSD ⟨P + c, g - c, d⟩ = obsSD ⟨P, g, d⟩
```

[`LigoNullSpace.obsSD_orbit`](../../PerfectAssociation/LigoNullSpace.lean#L397)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L380) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.obsSD_invalid_for_P</code></summary>

```lean
theorem obsSD_invalid_for_P : IsInvalidFor obsSD PGD.P
```

[`LigoNullSpace.obsSD_invalid_for_P`](../../PerfectAssociation/LigoNullSpace.lean#L405)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L381) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.obsSD_invalid_for_g</code></summary>

```lean
theorem obsSD_invalid_for_g : IsInvalidFor obsSD PGD.g
```

[`LigoNullSpace.obsSD_invalid_for_g`](../../PerfectAssociation/LigoNullSpace.lean#L409)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L382) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.obsSD_valid_for_level</code></summary>

```lean
theorem obsSD_valid_for_level : IsValidFor obsSD (fun θ : PGD => θ.P + θ.g)
```

[`LigoNullSpace.obsSD_valid_for_level`](../../PerfectAssociation/LigoNullSpace.lean#L413)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L383) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.obsSD_valid_for_d</code></summary>

```lean
theorem obsSD_valid_for_d : IsValidFor obsSD PGD.d
```

[`LigoNullSpace.obsSD_valid_for_d`](../../PerfectAssociation/LigoNullSpace.lean#L417)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L384) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.information_hierarchy</code></summary>

```lean
theorem information_hierarchy :
    (IsValidFor obsD PGD.d ∧ IsInvalidFor obsD PGD.P ∧ IsInvalidFor obsD PGD.g ∧
      IsInvalidFor obsD (fun θ : PGD => θ.P + θ.g)) ∧
    (IsValidFor obsSD (fun θ : PGD => θ.P + θ.g) ∧ IsValidFor obsSD PGD.d ∧
      IsInvalidFor obsSD PGD.P ∧ IsInvalidFor obsSD PGD.g)
```

[`LigoNullSpace.information_hierarchy`](../../PerfectAssociation/LigoNullSpace.lean#L422)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L385) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.hanford_confounding</code></summary>

```lean
theorem hanford_confounding :
    obsSD ⟨rStar, 0, 0⟩ = (7938490295413130, 0) ∧
    obsSD ⟨rStar, 0, 0⟩ = obsSD ⟨rStar - 100 * am, 100 * am, 0⟩ ∧
    obsSD ⟨rStar, 0, 0⟩ = obsSD ⟨rStar - rStarBig, rStarBig, 0⟩
```

[`LigoNullSpace.hanford_confounding`](../../PerfectAssociation/LigoNullSpace.lean#L432)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L386) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.anchor_valid_iff</code></summary>

```lean
theorem anchor_valid_iff (α β : Int) :
    IsValidFor (levelAnchor α β) (fun p : Int × Int => p) ↔ α ≠ β
```

[`LigoNullSpace.anchor_valid_iff`](../../PerfectAssociation/LigoNullSpace.lean#L448)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L389) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.anchor_inversion</code></summary>

```lean
theorem anchor_inversion (α β P g : Int) :
    (α - β) * P = anchorRead α β (P, g) - β * (P + g) ∧
    (α - β) * g = α * (P + g) - anchorRead α β (P, g)
```

[`LigoNullSpace.anchor_inversion`](../../PerfectAssociation/LigoNullSpace.lean#L475)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L390) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.anchor_example</code></summary>

```lean
theorem anchor_example :
    levelAnchor 1 0 (rStar, 100 * am) = (rStar + 100 * am, rStar) ∧
    levelAnchor 1 0 (rStar - 100 * am, 200 * am) ≠ levelAnchor 1 0 (rStar, 100 * am) ∧
    levelAnchor 2 2 (rStar - 100 * am, 200 * am) = levelAnchor 2 2 (rStar, 100 * am)
```

[`LigoNullSpace.anchor_example`](../../PerfectAssociation/LigoNullSpace.lean#L487)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L391) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.fisher_block_det</code></summary>

```lean
theorem fisher_block_det (w α β : Int) :
    (w + α * α) * (w + β * β) - (w + α * β) * (w + α * β) = w * ((α - β) * (α - β))
```

[`LigoNullSpace.fisher_block_det`](../../PerfectAssociation/LigoNullSpace.lean#L495)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L392) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.fisher_singular_iff</code></summary>

```lean
theorem fisher_singular_iff (α β : Int) : 4 * ((α - β) * (α - β)) = 0 ↔ α = β
```

[`LigoNullSpace.fisher_singular_iff`](../../PerfectAssociation/LigoNullSpace.lean#L506)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L393) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.fisher_null</code></summary>

```lean
theorem fisher_null : ∀ (rows : List (Int × Int × Int)) (v : Int × Int × Int),
    (∀ r ∈ rows, dot3 r v = 0) → ∀ u, fisher rows u v = 0
```

[`LigoNullSpace.fisher_null`](../../PerfectAssociation/LigoNullSpace.lean#L532)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L396) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.fisher_difference_channel</code></summary>

```lean
theorem fisher_difference_channel :
    fisher [rowD] eP eP = 0 ∧ fisher [rowD] eG eG = 0 ∧ fisher [rowD] eP eG = 0 ∧
    fisher [rowD] eD eD = 4
```

[`LigoNullSpace.fisher_difference_channel`](../../PerfectAssociation/LigoNullSpace.lean#L550)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L402) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.fisher_sum_difference</code></summary>

```lean
theorem fisher_sum_difference :
    fisher [rowS, rowD] eP eP = 4 ∧ fisher [rowS, rowD] eP eG = 4 ∧
    fisher [rowS, rowD] eG eG = 4 ∧ fisher [rowS, rowD] eD eD = 4 ∧
    fisher [rowS, rowD] (1, -1, 0) (1, -1, 0) = 0 ∧
    fisher [rowS, rowD] eP eP * fisher [rowS, rowD] eG eG -
      fisher [rowS, rowD] eP eG * fisher [rowS, rowD] eP eG = 0
```

[`LigoNullSpace.fisher_sum_difference`](../../PerfectAssociation/LigoNullSpace.lean#L557)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L403) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.fisher_anchored</code></summary>

```lean
theorem fisher_anchored (α β : Int) :
    fisher [rowS, rowD, (α, β, 0)] eP eP = 4 + α * α ∧
    fisher [rowS, rowD, (α, β, 0)] eP eG = 4 + α * β ∧
    fisher [rowS, rowD, (α, β, 0)] eG eG = 4 + β * β
```

[`LigoNullSpace.fisher_anchored`](../../PerfectAssociation/LigoNullSpace.lean#L567)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L404) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.fisher_anchored_det</code></summary>

```lean
theorem fisher_anchored_det (α β : Int) :
    (4 + α * α) * (4 + β * β) - (4 + α * β) * (4 + α * β) = 4 * ((α - β) * (α - β)) ∧
    (4 * ((α - β) * (α - β)) = 0 ↔ α = β) ∧
    (IsValidFor (levelAnchor α β) (fun p : Int × Int => p) ↔ α ≠ β)
```

[`LigoNullSpace.fisher_anchored_det`](../../PerfectAssociation/LigoNullSpace.lean#L597)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L405) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.d_channel_same_law</code></summary>

```lean
theorem d_channel_same_law (noise : Int → Nat) (d y : Int) :
    lawD noise ⟨4 * am, 0, d⟩ y = lawD noise ⟨400 * nm, 0, d⟩ y
```

[`LigoNullSpace.d_channel_same_law`](../../PerfectAssociation/LigoNullSpace.lean#L611)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L407) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.d_channel_hypotheses_differ</code></summary>

```lean
theorem d_channel_hypotheses_differ :
    400 * nm = 100000000000 * (4 * am) ∧ obsD ⟨4 * am, 0, 0⟩ = obsD ⟨400 * nm, 0, 0⟩ ∧
    obsS ⟨4 * am, 0, 0⟩ ≠ obsS ⟨400 * nm, 0, 0⟩
```

[`LigoNullSpace.d_channel_hypotheses_differ`](../../PerfectAssociation/LigoNullSpace.lean#L618)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L408) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.tvNum_of_pointwise</code></summary>

```lean
theorem tvNum_of_pointwise (p q : Int → Nat) (h : ∀ y, p y = q y) :
    ∀ ys : List Int, tvNum p q ys = 0
```

[`LigoNullSpace.tvNum_of_pointwise`](../../PerfectAssociation/LigoNullSpace.lean#L632)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L411) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.acceptMass_congr</code></summary>

```lean
theorem acceptMass_congr (φ : Int → Bool) (p q : Int → Nat) (h : ∀ y, p y = q y) :
    ∀ ys : List Int, acceptMass φ p ys = acceptMass φ q ys
```

[`LigoNullSpace.acceptMass_congr`](../../PerfectAssociation/LigoNullSpace.lean#L647)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L413) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.d_channel_tests_blind</code></summary>

```lean
theorem d_channel_tests_blind (noise : Int → Nat) (d : Int) (ys : List Int)
    (φ : Int → Bool) (y πA πB : Int) :
    tvNum (lawD noise ⟨4 * am, 0, d⟩) (lawD noise ⟨400 * nm, 0, d⟩) ys = 0 ∧
    acceptMass φ (lawD noise ⟨4 * am, 0, d⟩) ys = acceptMass φ (lawD noise ⟨400 * nm, 0, d⟩) ys ∧
    SameRatio (πA * (lawD noise ⟨4 * am, 0, d⟩ y : Int))
      (πB * (lawD noise ⟨400 * nm, 0, d⟩ y : Int)) πA πB
```

[`LigoNullSpace.d_channel_tests_blind`](../../PerfectAssociation/LigoNullSpace.lean#L657)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L414) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.massOver_mul</code></summary>

```lean
theorem massOver_mul (c : Nat) (f : Int → Nat) :
    ∀ ds : List Int, massOver (fun d => c * f d) ds = c * massOver f ds
```

[`LigoNullSpace.massOver_mul`](../../PerfectAssociation/LigoNullSpace.lean#L675)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L416) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.postPG_factor</code></summary>

```lean
theorem postPG_factor (πPG : Int × Int → Nat) (πd : Int → Nat) (lik : Int → Int → Nat)
    (y : Int) (ds : List Int) (p : Int × Int) :
    postPG πPG πd lik y ds p = πPG p * massOver (fun d => πd d * lik y d) ds
```

[`LigoNullSpace.postPG_factor`](../../PerfectAssociation/LigoNullSpace.lean#L689)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L418) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.level_posterior_odds_frozen</code></summary>

```lean
theorem level_posterior_odds_frozen (πPG : Int × Int → Nat) (πd : Int → Nat)
    (lik : Int → Int → Nat) (y : Int) (ds : List Int) (p q : Int × Int) :
    postPG πPG πd lik y ds p * πPG q = postPG πPG πd lik y ds q * πPG p
```

[`LigoNullSpace.level_posterior_odds_frozen`](../../PerfectAssociation/LigoNullSpace.lean#L697)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L419) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.prior_coupling_moves_blind_coordinate</code></summary>

```lean
theorem prior_coupling_moves_blind_coordinate :
    postMassP priorTied 1 = postMassAll priorTied ∧ 0 < postMassAll priorTied ∧
    2 * priorMassP priorTied 1 = priorMassAll priorTied ∧
    2 * postMassP priorFlat 1 = postMassAll priorFlat ∧
    2 * priorMassP priorFlat 1 = priorMassAll priorFlat
```

[`LigoNullSpace.prior_coupling_moves_blind_coordinate`](../../PerfectAssociation/LigoNullSpace.lean#L729)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L427) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.ks_flag_not_function_of_likelihood</code></summary>

```lean
theorem ks_flag_not_function_of_likelihood : IsInvalidFor (fun _ : Bool => likD) ksFlag
```

[`LigoNullSpace.ks_flag_not_function_of_likelihood`](../../PerfectAssociation/LigoNullSpace.lean#L750)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L430) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.likelihood_constant_on_fibre</code></summary>

```lean
theorem likelihood_constant_on_fibre (L : Int → Nat) (P g c : Int) :
    L (P + c + (g - c)) = L (P + g)
```

[`LigoNullSpace.likelihood_constant_on_fibre`](../../PerfectAssociation/LigoNullSpace.lean#L758)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L432) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.calibration_prior_transport</code></summary>

```lean
theorem calibration_prior_transport (πg L : Int → Nat) (c P g : Int) :
    jointW (fun t => πg (t - c)) L P g = jointW πg L (P + c) (g - c)
```

[`LigoNullSpace.calibration_prior_transport`](../../PerfectAssociation/LigoNullSpace.lean#L766)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L433) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.hanford_transport</code></summary>

```lean
theorem hanford_transport :
    jointW (deltaAt 0) (deltaAt rStar) rStar 0 = 1 ∧
    jointW (fun t => deltaAt 0 (t - 100 * am)) (deltaAt rStar) (rStar - 100 * am) (100 * am) = 1 ∧
    jointW (fun t => deltaAt 0 (t - 100 * am)) (deltaAt rStar) rStar 0 = 0
```

[`LigoNullSpace.hanford_transport`](../../PerfectAssociation/LigoNullSpace.lean#L777)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L435) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.difference_blind_to_common_error</code></summary>

```lean
theorem difference_blind_to_common_error (P g e₁ e₂ : Int) :
    difC (P + g + e₁, P + g + e₂) = e₁ - e₂ ∧
    sumC (P + g + e₁, P + g + e₂) - 2 * P = 2 * g + e₁ + e₂
```

[`LigoNullSpace.difference_blind_to_common_error`](../../PerfectAssociation/LigoNullSpace.lean#L787)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L436) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.common_error_variance_family</code></summary>

```lean
theorem common_error_variance_family :
    ∀ t ∈ List.range 101,
      momD1 (samples (Int.ofNat t)) = 0 ∧ momD2 (samples (Int.ofNat t)) = 16 ∧
      momR1 (samples (Int.ofNat t)) = 0 ∧
      momR2 (samples (Int.ofNat t)) = 32 * (Int.ofNat t * Int.ofNat t) + 16
```

[`LigoNullSpace.common_error_variance_family`](../../PerfectAssociation/LigoNullSpace.lean#L824)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L442) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.many_channels_blind</code></summary>

```lean
theorem many_channels_blind (N : Nat) (hN : 0 < N) {β : Sort u} (S : List Int → β)
    (l : List (Nat × Nat)) :
    IsInvalidFor (fun ε : Nat → Int => S (diffs ε l)) (fun ε => sumTo N ε)
```

[`LigoNullSpace.many_channels_blind`](../../PerfectAssociation/LigoNullSpace.lean#L836)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L443) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.two_hundred_thousand_channels_blind</code></summary>

```lean
theorem two_hundred_thousand_channels_blind {β : Sort u} (S : List Int → β)
    (l : List (Nat × Nat)) :
    IsInvalidFor (fun ε : Nat → Int => S (diffs ε l)) (fun ε => sumTo 200000 ε)
```

[`LigoNullSpace.two_hundred_thousand_channels_blind`](../../PerfectAssociation/LigoNullSpace.lean#L842)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L444) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.ev_add</code></summary>

```lean
theorem ev_add (r : Row) (θ v : Latent) : ev r (addL θ v) = ev r θ + ev r v
```

[`LigoNullSpace.ev_add`](../../PerfectAssociation/LigoNullSpace.lean#L894)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L453) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.ev_sub</code></summary>

```lean
theorem ev_sub (r : Row) (θ v : Latent) : ev r (subL θ v) = ev r θ - ev r v
```

[`LigoNullSpace.ev_sub`](../../PerfectAssociation/LigoNullSpace.lean#L904)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L454) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.ev_zero</code></summary>

```lean
theorem ev_zero (r : Row) : ev r zeroL = 0
```

[`LigoNullSpace.ev_zero`](../../PerfectAssociation/LigoNullSpace.lean#L914)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L455) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.map_congr_mem</code></summary>

```lean
theorem map_congr_mem {α β : Type} (f g : α → β) :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.map f = l.map g
```

[`LigoNullSpace.map_congr_mem`](../../PerfectAssociation/LigoNullSpace.lean#L919)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L456) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.eq_of_map_eq_mem</code></summary>

```lean
theorem eq_of_map_eq_mem {α β : Type} (f g : α → β) :
    ∀ l : List α, l.map f = l.map g → ∀ a ∈ l, f a = g a
```

[`LigoNullSpace.eq_of_map_eq_mem`](../../PerfectAssociation/LigoNullSpace.lean#L927)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L457) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.measure_shift</code></summary>

```lean
theorem measure_shift (suite : List Row) (θ v : Latent) (hv : InKernel suite v) :
    measureSuite suite (addL θ v) = measureSuite suite θ
```

[`LigoNullSpace.measure_shift`](../../PerfectAssociation/LigoNullSpace.lean#L937)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L458) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.audit_invalid</code></summary>

```lean
theorem audit_invalid {γ : Sort u} (suite : List Row) (T : Latent → γ) (θ v : Latent)
    (hv : InKernel suite v) (hT : T (addL θ v) ≠ T θ) : IsInvalidFor (measureSuite suite) T
```

[`LigoNullSpace.audit_invalid`](../../PerfectAssociation/LigoNullSpace.lean#L944)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L459) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.audit_exact</code></summary>

```lean
theorem audit_exact (suite : List Row) (t : Row) :
    IsValidFor (measureSuite suite) (ev t) ↔ ∀ v, InKernel suite v → ev t v = 0
```

[`LigoNullSpace.audit_exact`](../../PerfectAssociation/LigoNullSpace.lean#L950)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L460) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.kernel_extend</code></summary>

```lean
theorem kernel_extend (suite extra : List Row) (v : Latent) (h₁ : InKernel suite v)
    (h₂ : InKernel extra v) : InKernel (suite ++ extra) v
```

[`LigoNullSpace.kernel_extend`](../../PerfectAssociation/LigoNullSpace.lean#L972)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L461) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.redundant_rows_no_repair</code></summary>

```lean
theorem redundant_rows_no_repair {γ : Sort u} (suite₁ suite₂ : List Row) (T : Latent → γ)
    (hsub : ∀ r ∈ suite₂, r ∈ suite₁) :
    IsInvalidFor (measureSuite suite₁) T → IsInvalidFor (measureSuite suite₂) T
```

[`LigoNullSpace.redundant_rows_no_repair`](../../PerfectAssociation/LigoNullSpace.lean#L981)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L462) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.mem_replicate_eq</code></summary>

```lean
theorem mem_replicate_eq (r a : Row) : ∀ n : Nat, r ∈ List.replicate n a → r = a
```

[`LigoNullSpace.mem_replicate_eq`](../../PerfectAssociation/LigoNullSpace.lean#L989)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L463) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.agreement_suite_invalid</code></summary>

```lean
theorem agreement_suite_invalid :
    IsInvalidFor (measureSuite agreementSuite) (ev rowP) ∧
    IsInvalidFor (measureSuite agreementSuite) (ev anchorCal) ∧
    IsInvalidFor (measureSuite agreementSuite) (ev anchorTime) ∧
    IsInvalidFor (measureSuite agreementSuite) (ev anchorAct) ∧
    IsInvalidFor (measureSuite agreementSuite) (ev anchorSens)
```

[`LigoNullSpace.agreement_suite_invalid`](../../PerfectAssociation/LigoNullSpace.lean#L1034)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L479) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.level_suite_invalid</code></summary>

```lean
theorem level_suite_invalid :
    IsInvalidFor (measureSuite levelSuite) (ev rowP) ∧
    IsInvalidFor (measureSuite levelSuite) (ev anchorCal) ∧
    IsInvalidFor (measureSuite levelSuite) (ev anchorTime) ∧
    IsInvalidFor (measureSuite levelSuite) (ev anchorAct) ∧
    IsInvalidFor (measureSuite levelSuite) (ev anchorSens)
```

[`LigoNullSpace.level_suite_invalid`](../../PerfectAssociation/LigoNullSpace.lean#L1048)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L480) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.anchored_suite_valid_for_P</code></summary>

```lean
theorem anchored_suite_valid_for_P : IsValidFor (measureSuite anchoredSuite) (ev rowP)
```

[`LigoNullSpace.anchored_suite_valid_for_P`](../../PerfectAssociation/LigoNullSpace.lean#L1061)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L481) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.each_anchor_necessary</code></summary>

```lean
theorem each_anchor_necessary :
    IsInvalidFor (measureSuite [rowDiff, rowSum, anchorTime, anchorAct, anchorSens]) (ev rowP) ∧
    IsInvalidFor (measureSuite [rowDiff, rowSum, anchorCal, anchorAct, anchorSens]) (ev rowP) ∧
    IsInvalidFor (measureSuite [rowDiff, rowSum, anchorCal, anchorTime, anchorSens]) (ev rowP) ∧
    IsInvalidFor (measureSuite [rowDiff, rowSum, anchorCal, anchorTime, anchorAct]) (ev rowP)
```

[`LigoNullSpace.each_anchor_necessary`](../../PerfectAssociation/LigoNullSpace.lean#L1080)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L482) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.repeated_agreement_invalid</code></summary>

```lean
theorem repeated_agreement_invalid (n : Nat) :
    IsInvalidFor (measureSuite (List.replicate n rowDiff)) (ev rowP)
```

[`LigoNullSpace.repeated_agreement_invalid`](../../PerfectAssociation/LigoNullSpace.lean#L1092)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L483) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.hanford_suite_witness</code></summary>

```lean
theorem hanford_suite_witness :
    measureSuite levelSuite ⟨rStar, 0, 0, 0, 0, 0⟩ = [0, 7938490295413130] ∧
    measureSuite levelSuite ⟨rStar, 0, 0, 0, 0, 0⟩ =
      measureSuite levelSuite ⟨rStar - 100 * am, 100 * am, 0, 0, 0, 0⟩ ∧
    measureSuite levelSuite ⟨rStar, 0, 0, 0, 0, 0⟩ =
      measureSuite levelSuite ⟨rStar - rStarBig, rStarBig, 0, 0, 0, 0⟩ ∧
    ev rowP ⟨rStar, 0, 0, 0, 0, 0⟩ ≠ ev rowP ⟨rStar - 100 * am, 100 * am, 0, 0, 0, 0⟩
```

[`LigoNullSpace.hanford_suite_witness`](../../PerfectAssociation/LigoNullSpace.lean#L1104)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L484) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.twoSided_invalid_for_direction</code></summary>

```lean
theorem twoSided_invalid_for_direction {β : Sort u} (f : Nat → β) :
    IsInvalidFor (twoSided f) direction
```

[`LigoNullSpace.twoSided_invalid_for_direction`](../../PerfectAssociation/LigoNullSpace.lean#L1122)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L487) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.threshold_no_repair</code></summary>

```lean
theorem threshold_no_repair (f : Nat → Nat) (α : Nat) :
    IsInvalidFor (fun z => significant α (twoSided f z)) direction
```

[`LigoNullSpace.threshold_no_repair`](../../PerfectAssociation/LigoNullSpace.lean#L1133)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L489) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.zstat_invalid_for_effect</code></summary>

```lean
theorem zstat_invalid_for_effect :
    IsInvalidFor zStat effectSize ∧ SameRatio 200 100 2 1 ∧
    effectSize (200, 100) = 100 * effectSize (2, 1)
```

[`LigoNullSpace.zstat_invalid_for_effect`](../../PerfectAssociation/LigoNullSpace.lean#L1146)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L492) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.neg_sq</code></summary>

```lean
theorem neg_sq (x : Int) : -x * -x = x * x
```

[`LigoNullSpace.neg_sq`](../../PerfectAssociation/LigoNullSpace.lean#L1156)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L494) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.chi2_invalid_for_pattern</code></summary>

```lean
theorem chi2_invalid_for_pattern : IsInvalidFor chi2 (fun v : Int × Int => v)
```

[`LigoNullSpace.chi2_invalid_for_pattern`](../../PerfectAssociation/LigoNullSpace.lean#L1162)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L495) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.chi2_symmetries</code></summary>

```lean
theorem chi2_symmetries (a b : Int) :
    chi2 (b, a) = chi2 (a, b) ∧ chi2 (-a, b) = chi2 (a, b) ∧ chi2 (a, -b) = chi2 (a, b)
```

[`LigoNullSpace.chi2_symmetries`](../../PerfectAssociation/LigoNullSpace.lean#L1166)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L496) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.natAbs_neg_eq</code></summary>

```lean
theorem natAbs_neg_eq (x : Int) : (-x).natAbs = x.natAbs
```

[`LigoNullSpace.natAbs_neg_eq`](../../PerfectAssociation/LigoNullSpace.lean#L1183)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L498) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.ksSup_neg</code></summary>

```lean
theorem ksSup_neg : ∀ xs : List Int, ksSup (xs.map (fun x => -x)) = ksSup xs
```

[`LigoNullSpace.ksSup_neg`](../../PerfectAssociation/LigoNullSpace.lean#L1189)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L499) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.ks_invalid_for_direction</code></summary>

```lean
theorem ks_invalid_for_direction : IsInvalidFor ksSup leading
```

[`LigoNullSpace.ks_invalid_for_direction`](../../PerfectAssociation/LigoNullSpace.lean#L1203)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L501) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.constant_on_varying_set_not_valid</code></summary>

```lean
theorem constant_on_varying_set_not_valid {α : Sort u} {β : Sort v} {γ : Sort w}
    (Φ : α → β) (R : α → γ) (S : α → Prop) (c : β) (hc : ∀ x, S x → Φ x = c)
    (x y : α) (hx : S x) (hy : S y) (hR : R x ≠ R y) : ¬ IsValidFor Φ R
```

[`LigoNullSpace.constant_on_varying_set_not_valid`](../../PerfectAssociation/LigoNullSpace.lean#L1207)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L502) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.statistical_pipeline_invalidations</code></summary>

```lean
theorem statistical_pipeline_invalidations :
    (∀ f : Nat → Nat, IsInvalidFor (twoSided f) direction) ∧
    (∀ (f : Nat → Nat) (α : Nat), IsInvalidFor (fun z => significant α (twoSided f z)) direction) ∧
    IsInvalidFor zStat effectSize ∧
    IsInvalidFor chi2 (fun v : Int × Int => v) ∧
    IsInvalidFor ksSup leading
```

[`LigoNullSpace.statistical_pipeline_invalidations`](../../PerfectAssociation/LigoNullSpace.lean#L1215)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L503) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.difference_proxy_carries_no_common_error</code></summary>

```lean
theorem difference_proxy_carries_no_common_error :
    IsInvalidFor obsD PGD.g ∧ IsInvalidFor obsD (fun θ : PGD => θ.P + θ.g) ∧
    fisher [rowD] eP eP = 0 ∧ fisher [rowD] eG eG = 0 ∧
    (∀ (πPG : Int × Int → Nat) (πd : Int → Nat) (lik : Int → Int → Nat) (y : Int)
      (ds : List Int) (p q : Int × Int),
      postPG πPG πd lik y ds p * πPG q = postPG πPG πd lik y ds q * πPG p) ∧
    (∀ (N : Nat), 0 < N → ∀ (S : List Int → List Int) (l : List (Nat × Nat)),
      IsInvalidFor (fun ε : Nat → Int => S (diffs ε l)) (fun ε => sumTo N ε))
```

[`LigoNullSpace.difference_proxy_carries_no_common_error`](../../PerfectAssociation/LigoNullSpace.lean#L1242)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L504) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.calibration_marginalisation_transports_bias</code></summary>

```lean
theorem calibration_marginalisation_transports_bias :
    (∀ (L : Int → Nat) (P g c : Int), L (P + c + (g - c)) = L (P + g)) ∧
    (∀ (πg L : Int → Nat) (c P g : Int),
      jointW (fun t => πg (t - c)) L P g = jointW πg L (P + c) (g - c)) ∧
    jointW (deltaAt 0) (deltaAt rStar) rStar 0 = 1 ∧
    jointW (fun t => deltaAt 0 (t - 100 * am)) (deltaAt rStar) (rStar - 100 * am) (100 * am) = 1 ∧
    jointW (fun t => deltaAt 0 (t - 100 * am)) (deltaAt rStar) rStar 0 = 0
```

[`LigoNullSpace.calibration_marginalisation_transports_bias`](../../PerfectAssociation/LigoNullSpace.lean#L1259)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L505) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.ks_test_not_informativeness</code></summary>

```lean
theorem ks_test_not_informativeness :
    IsInvalidFor (fun _ : Bool => likD) ksFlag ∧
    postMassP priorTied 1 = postMassAll priorTied ∧
    2 * postMassP priorFlat 1 = postMassAll priorFlat ∧
    IsInvalidFor ksSup leading ∧
    (∀ xs : List Int, ksSup (xs.map (fun x => -x)) = ksSup xs)
```

[`LigoNullSpace.ks_test_not_informativeness`](../../PerfectAssociation/LigoNullSpace.lean#L1273)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L506) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoNullSpace.ligo_null_space_invalidation</code></summary>

```lean
theorem ligo_null_space_invalidation :
    (IsInvalidFor difC sumC ∧ (¬ ∃ B : Int → Int, ∀ X : Int × Int, sumC X ≤ B (difC X)) ∧
      Ker difC (rStar, rStar) (rStarBig, rStarBig) ∧
      ¬ Ker sumC (rStar, rStar) (rStarBig, rStarBig)) ∧
    (∀ a b : Int, IsValidFor difC (linT a b) ↔ a + b = 0) ∧
    (IsInvalidFor obsSD PGD.P ∧ IsValidFor obsSD (fun θ : PGD => θ.P + θ.g) ∧
      (∀ α β : Int, IsValidFor (levelAnchor α β) (fun p : Int × Int => p) ↔ α ≠ β) ∧
      (∀ α β : Int,
        (4 + α * α) * (4 + β * β) - (4 + α * β) * (4 + α * β) = 4 * ((α - β) * (α - β)))) ∧
    (IsInvalidFor obsD PGD.g ∧
      (∀ (πg L : Int → Nat) (c P g : Int),
        jointW (fun t => πg (t - c)) L P g = jointW πg L (P + c) (g - c)) ∧
      IsInvalidFor (fun _ : Bool => likD) ksFlag) ∧
    ((∀ {γ : Type} (suite : List Row) (T : Latent → γ) (θ v : Latent),
        InKernel suite v → T (addL θ v) ≠ T θ → IsInvalidFor (measureSuite suite) T) ∧
      (∀ (suite : List Row) (t : Row),
        IsValidFor (measureSuite suite) (ev t) ↔ ∀ v, InKernel suite v → ev t v = 0) ∧
      IsInvalidFor (measureSuite levelSuite) (ev rowP) ∧
      IsValidFor (measureSuite anchoredSuite) (ev rowP))
```

[`LigoNullSpace.ligo_null_space_invalidation`](../../PerfectAssociation/LigoNullSpace.lean#L1297)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L507) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>
