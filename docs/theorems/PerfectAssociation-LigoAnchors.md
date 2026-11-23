# Reference-relative error and exact likelihood fibres

Adding the same shift to model errors cancels from differences. Moving spin and discrepancy along a coefficient fibre leaves the predicted phase and every likelihood depending only on that phase unchanged.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [association export roots](../../verification/roots/association.txt)

[Full Lean source](../../PerfectAssociation/LigoAnchors.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>LigoAnchors.compare_blind</code></summary>

```lean
theorem compare_blind (eE eP g : Int) : compare (eE + g) (eP + g) = compare eE eP
```

[`LigoAnchors.compare_blind`](../../PerfectAssociation/LigoAnchors.lean#L17)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L66) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.compare_cannot_see_common_mode</code></summary>

```lean
theorem compare_cannot_see_common_mode :
    compare 0 0 = compare 1 1 ∧ (0 : Int) + 0 ≠ 1 + 1
```

[`LigoAnchors.compare_cannot_see_common_mode`](../../PerfectAssociation/LigoAnchors.lean#L22)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L67) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.pointwise_blind</code></summary>

```lean
theorem pointwise_blind (e : Nat → Int) (g : Int) (i j : Nat) :
    (e i + g) - (e j + g) = e i - e j
```

[`LigoAnchors.pointwise_blind`](../../PerfectAssociation/LigoAnchors.lean#L25)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L68) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.any_comparison_statistic_blind</code></summary>

```lean
theorem any_comparison_statistic_blind {β : Sort u} (T : (Nat → Nat → Int) → β)
    (hT : ∀ f f' : Nat → Nat → Int, (∀ i j, f i j = f' i j) → T f = T f')
    (e : Nat → Int) (g : Int) :
    T (fun i j => (e i + g) - (e j + g)) = T (fun i j => e i - e j)
```

[`LigoAnchors.any_comparison_statistic_blind`](../../PerfectAssociation/LigoAnchors.lean#L31)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L69) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.calibration_distance_fibre</code></summary>

```lean
theorem calibration_distance_fibre (kappa delta c : Int) :
    logAmp (kappa + c) (delta + c) = logAmp kappa delta
```

[`LigoAnchors.calibration_distance_fibre`](../../PerfectAssociation/LigoAnchors.lean#L44)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L71) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.psi15_fibre</code></summary>

```lean
theorem psi15_fibre (c beta k : Int) : psi15 c beta (4 * k) = psi15 c (beta + k) 0
```

[`LigoAnchors.psi15_fibre`](../../PerfectAssociation/LigoAnchors.lean#L54)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L73) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.psi15_fibre_all_frequencies</code></summary>

```lean
theorem psi15_fibre_all_frequencies (wt : Int → Int) (c beta k f : Int) :
    wt f * psi15 c beta (4 * k) = wt f * psi15 c (beta + k) 0
```

[`LigoAnchors.psi15_fibre_all_frequencies`](../../PerfectAssociation/LigoAnchors.lean#L59)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L74) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.waveform_cannot_classify_spin</code></summary>

```lean
theorem waveform_cannot_classify_spin :
    psi15 0 0 4 = psi15 0 1 0 ∧ (0 : Int) ≠ 1
```

[`LigoAnchors.waveform_cannot_classify_spin`](../../PerfectAssociation/LigoAnchors.lean#L64)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L75) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.likelihood_fibre</code></summary>

```lean
theorem likelihood_fibre {Θ : Sort u} {H : Sort v} {D : Sort w}
    (logL : D → H → Int) (g : Θ → H) {p q : Θ} (h : g p = g q) (d : D) :
    logL d (g p) = logL d (g q)
```

[`LigoAnchors.likelihood_fibre`](../../PerfectAssociation/LigoAnchors.lean#L69)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L76) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.mixVar4_blind</code></summary>

```lean
theorem mixVar4_blind (m1 m2 v1 v2 b : Int) :
    mixVar4 (m1 + b) (m2 + b) v1 v2 = mixVar4 m1 m2 v1 v2
```

[`LigoAnchors.mixVar4_blind`](../../PerfectAssociation/LigoAnchors.lean#L78)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L78) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.tableI_a1_mixture</code></summary>

```lean
theorem tableI_a1_mixture :
    mixVar4 22 32 529 529 = 2216 ∧
    ∀ b ∈ List.range 41, mixVar4 (22 + Int.ofNat b) (32 + Int.ofNat b) 529 529 = 2216
```

[`LigoAnchors.tableI_a1_mixture`](../../PerfectAssociation/LigoAnchors.lean#L85)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L79) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.eta_swap</code></summary>

```lean
theorem eta_swap (m1 m2 : Int) : etaNum m1 m2 = etaNum m2 m1
```

[`LigoAnchors.eta_swap`](../../PerfectAssociation/LigoAnchors.lean#L94)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L81) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.gw150914_fold</code></summary>

```lean
theorem gw150914_fold :
    4 * etaNum 387 325 = (387 + 325) * (387 + 325) - (387 - 325) * (387 - 325) ∧
    (387 - 325) * (387 - 325) = (3844 : Int) ∧ etaNum 387 325 = etaNum 325 387
```

[`LigoAnchors.gw150914_fold`](../../PerfectAssociation/LigoAnchors.lean#L99)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L82) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.fold_identity_grid</code></summary>

```lean
theorem fold_identity_grid :
    ∀ a ∈ List.range 13, ∀ d ∈ List.range 7,
      4 * ((Int.ofNat a + Int.ofNat d) * (Int.ofNat a - Int.ofNat d)) =
        (2 * Int.ofNat a) * (2 * Int.ofNat a) - 4 * (Int.ofNat d * Int.ofNat d)
```

[`LigoAnchors.fold_identity_grid`](../../PerfectAssociation/LigoAnchors.lean#L104)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L83) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.paper_prior_certainty</code></summary>

```lean
theorem paper_prior_certainty : massBeta priorPaper 1 = massTotal priorPaper
```

[`LigoAnchors.paper_prior_certainty`](../../PerfectAssociation/LigoAnchors.lean#L128)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L89) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.open_prior_half</code></summary>

```lean
theorem open_prior_half : 2 * massBeta priorOpen 1 = massTotal priorOpen
```

[`LigoAnchors.open_prior_half`](../../PerfectAssociation/LigoAnchors.lean#L131)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L90) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.same_data_different_beta</code></summary>

```lean
theorem same_data_different_beta :
    massBeta priorPaper 1 * massTotal priorOpen ≠
      massBeta priorOpen 1 * massTotal priorPaper
```

[`LigoAnchors.same_data_different_beta`](../../PerfectAssociation/LigoAnchors.lean#L134)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L91) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.fibre_prior_echo</code></summary>

```lean
theorem fibre_prior_echo (prior : Int → Int → Nat) (L : Int → Nat) (uu b l b' l' : Int)
    (hfib : b + l * uu = b' + l' * uu) :
    post prior L uu b l * prior b' l' = post prior L uu b' l' * prior b l
```

[`LigoAnchors.fibre_prior_echo`](../../PerfectAssociation/LigoAnchors.lean#L142)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L93) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.reference_shift_invisible</code></summary>

```lean
theorem reference_shift_invisible (m1 m2 r c : Int) :
    err m1 (r + c) - err m2 (r + c) = err m1 r - err m2 r
```

[`LigoAnchors.reference_shift_invisible`](../../PerfectAssociation/LigoAnchors.lean#L157)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L95) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoAnchors.anchor_identifies</code></summary>

```lean
theorem anchor_identifies (m truth c c' : Int)
    (h : err m (truth + c) = err m (truth + c')) : c = c'
```

[`LigoAnchors.anchor_identifies`](../../PerfectAssociation/LigoAnchors.lean#L162)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L96) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>
