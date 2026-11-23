# Observation fibres and inference

A pair of states with equal readings and unequal targets rules out a recovery function. The phase coefficient, spin exchange, common shifts, equal likelihoods, and model detection labels instantiate the argument.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [association export roots](../../verification/roots/association.txt)

[Full Lean source](../../PerfectAssociation/LigoCongruence.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>LigoCongruence.invalid_not_valid</code></summary>

```lean
theorem invalid_not_valid {α : Sort u} {β : Sort v} {γ : Sort w}
    (Φ : α → β) (R : α → γ) : IsInvalidFor Φ R → ¬ IsValidFor Φ R
```

[`LigoCongruence.invalid_not_valid`](../../PerfectAssociation/LigoCongruence.lean#L22)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L255) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.valid_iff_not_invalid</code></summary>

```lean
theorem valid_iff_not_invalid {α : Sort u} {β : Sort v} {γ : Sort w} [DecidableEq γ]
    (Φ : α → β) (R : α → γ) : IsValidFor Φ R ↔ ¬ IsInvalidFor Φ R
```

[`LigoCongruence.valid_iff_not_invalid`](../../PerfectAssociation/LigoCongruence.lean#L27)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L256) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.factor_valid</code></summary>

```lean
theorem factor_valid {α : Sort u} {β : Sort v} {γ : Sort w}
    (Φ : α → β) (R : α → γ) (w : β → γ) (h : ∀ a, R a = w (Φ a)) :
    IsValidFor Φ R
```

[`LigoCongruence.factor_valid`](../../PerfectAssociation/LigoCongruence.lean#L33)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L257) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.invalid_no_factor</code></summary>

```lean
theorem invalid_no_factor {α : Sort u} {β : Sort v} {γ : Sort w}
    (Φ : α → β) (R : α → γ) (h : IsInvalidFor Φ R) :
    ¬ ∃ w : β → γ, ∀ a, R a = w (Φ a)
```

[`LigoCongruence.invalid_no_factor`](../../PerfectAssociation/LigoCongruence.lean#L39)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L258) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.valid_factor</code></summary>

```lean
theorem valid_factor {α : Sort u} {β : Sort v} {γ : Sort w}
    (Φ : α → β) (R : α → γ) (s : β → α) (hs : ∀ b, Φ (s b) = b)
    (hv : IsValidFor Φ R) : ∃ w : β → γ, ∀ a, R a = w (Φ a)
```

[`LigoCongruence.valid_factor`](../../PerfectAssociation/LigoCongruence.lean#L45)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L259) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.valid_iff_factor</code></summary>

```lean
theorem valid_iff_factor {α : Sort u} {β : Sort v} {γ : Sort w}
    (Φ : α → β) (R : α → γ) (s : β → α) (hs : ∀ b, Φ (s b) = b) :
    IsValidFor Φ R ↔ ∃ w : β → γ, ∀ a, R a = w (Φ a)
```

[`LigoCongruence.valid_iff_factor`](../../PerfectAssociation/LigoCongruence.lean#L50)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L260) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.no_repair</code></summary>

```lean
theorem no_repair {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x}
    (Φ : α → β) (Q : α → δ) (R : α → γ)
    (hsub : ∀ a b, Ker Φ a b → Ker Q a b) : IsInvalidFor Φ R → IsInvalidFor Q R
```

[`LigoCongruence.no_repair`](../../PerfectAssociation/LigoCongruence.lean#L56)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L261) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.invalid_postcompose</code></summary>

```lean
theorem invalid_postcompose {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x}
    (Φ : α → β) (g : β → δ) (R : α → γ) :
    IsInvalidFor Φ R → IsInvalidFor (fun a => g (Φ a)) R
```

[`LigoCongruence.invalid_postcompose`](../../PerfectAssociation/LigoCongruence.lean#L62)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L262) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.chain_blind</code></summary>

```lean
theorem chain_blind {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x}
    {ε : Sort y} {ζ : Sort z}
    (W : α → β) (C : β → γ) (L : γ → δ) (B : δ → ε) (R : α → ζ) :
    IsInvalidFor W R → IsInvalidFor (fun a => B (L (C (W a)))) R
```

[`LigoCongruence.chain_blind`](../../PerfectAssociation/LigoCongruence.lean#L68)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L263) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.ker_pair</code></summary>

```lean
theorem ker_pair {α : Sort u} {β : Type v} {δ : Type x} (Φ : α → β) (A : α → δ) (a b : α) :
    Ker (fun t => (Φ t, A t)) a b ↔ Ker Φ a b ∧ Ker A a b
```

[`LigoCongruence.ker_pair`](../../PerfectAssociation/LigoCongruence.lean#L76)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L264) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.anchor_valid</code></summary>

```lean
theorem anchor_valid {α : Sort u} {β : Type v} {γ : Sort w} {δ : Type x} [DecidableEq γ]
    (Φ : α → β) (A : α → δ) (R : α → γ) :
    IsValidFor (fun t => (Φ t, A t)) R ↔
      ∀ a b, Ker Φ a b → ¬ Ker R a b → ¬ Ker A a b
```

[`LigoCongruence.anchor_valid`](../../PerfectAssociation/LigoCongruence.lean#L83)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L265) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.posterior_odds_frozen</code></summary>

```lean
theorem posterior_odds_frozen (π₁ π₂ ℓ : Int) : SameRatio (π₁ * ℓ) (π₂ * ℓ) π₁ π₂
```

[`LigoCongruence.posterior_odds_frozen`](../../PerfectAssociation/LigoCongruence.lean#L97)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L267) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.within_class_prior_echo</code></summary>

```lean
theorem within_class_prior_echo (π₁ π₂ ℓ : Int) :
    SameRatio (π₁ * ℓ) (π₁ * ℓ + π₂ * ℓ) π₁ (π₁ + π₂)
```

[`LigoCongruence.within_class_prior_echo`](../../PerfectAssociation/LigoCongruence.lean#L102)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L268) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.within_class_prior_echo_norm</code></summary>

```lean
theorem within_class_prior_echo_norm (π₁ π₂ ℓ k : Int) :
    SameRatio (π₁ * ℓ * k) (π₁ * ℓ * k + π₂ * ℓ * k) π₁ (π₁ + π₂)
```

[`LigoCongruence.within_class_prior_echo_norm`](../../PerfectAssociation/LigoCongruence.lean#L108)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L269) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.psi15_fibre</code></summary>

```lean
theorem psi15_fibre (c β k : Int) : psi15 c β (4 * k) = psi15 c (β + k) 0
```

[`LigoCongruence.psi15_fibre`](../../PerfectAssociation/LigoCongruence.lean#L123)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L272) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.psi15_orbit</code></summary>

```lean
theorem psi15_orbit (c β δ t : Int) : psi15 c (β + t) (δ - 4 * t) = psi15 c β δ
```

[`LigoCongruence.psi15_orbit`](../../PerfectAssociation/LigoCongruence.lean#L128)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L273) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.psi15_eq_iff</code></summary>

```lean
theorem psi15_eq_iff (c β δ β' δ' : Int) :
    psi15 c β δ = psi15 c β' δ' ↔ 4 * β + δ = 4 * β' + δ'
```

[`LigoCongruence.psi15_eq_iff`](../../PerfectAssociation/LigoCongruence.lean#L134)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L274) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.phase15_fibre</code></summary>

```lean
theorem phase15_fibre (pref c β k : Int) :
    phase15 pref c (β, 4 * k) = phase15 pref c (β + k, 0)
```

[`LigoCongruence.phase15_fibre`](../../PerfectAssociation/LigoCongruence.lean#L144)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L275) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.waveform_invalid_for_spin</code></summary>

```lean
theorem waveform_invalid_for_spin (pref c : Int) :
    IsInvalidFor (phase15 pref c) (fun s : Int × Int => s.1)
```

[`LigoCongruence.waveform_invalid_for_spin`](../../PerfectAssociation/LigoCongruence.lean#L149)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L276) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.psi15_invalid_for_spin</code></summary>

```lean
theorem psi15_invalid_for_spin (c : Int) :
    IsInvalidFor (fun s : Int × Int => psi15 c s.1 s.2) (fun s => s.1)
```

[`LigoCongruence.psi15_invalid_for_spin`](../../PerfectAssociation/LigoCongruence.lean#L154)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L277) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.sumTo_zero_fn</code></summary>

```lean
theorem sumTo_zero_fn : ∀ n : Nat, sumTo n (fun _ => 0) = 0
```

[`LigoCongruence.sumTo_zero_fn`](../../PerfectAssociation/LigoCongruence.lean#L163)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L279) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.sumTo_one_fn</code></summary>

```lean
theorem sumTo_one_fn : ∀ n : Nat, sumTo n (fun _ => 1) = (n : Int)
```

[`LigoCongruence.sumTo_one_fn`](../../PerfectAssociation/LigoCongruence.lean#L167)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L280) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.cons_congr</code></summary>

```lean
theorem cons_congr {α : Type u} {a b : α} {l m : List α} (h₁ : a = b) (h₂ : l = m) :
    a :: l = b :: m
```

[`LigoCongruence.cons_congr`](../../PerfectAssociation/LigoCongruence.lean#L171)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L281) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.diffs_shift</code></summary>

```lean
theorem diffs_shift (ε : Nat → Int) (g : Int) :
    ∀ l : List (Nat × Nat), diffs (fun i => ε i + g) l = diffs ε l
```

[`LigoCongruence.diffs_shift`](../../PerfectAssociation/LigoCongruence.lean#L182)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L283) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.pairwise_blind_list</code></summary>

```lean
theorem pairwise_blind_list {β : Sort u} (S : List Int → β) (ε : Nat → Int) (g : Int)
    (l : List (Nat × Nat)) :
    S (diffs (fun i => ε i + g) l) = S (diffs ε l)
```

[`LigoCongruence.pairwise_blind_list`](../../PerfectAssociation/LigoCongruence.lean#L189)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L284) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.diffs_const</code></summary>

```lean
theorem diffs_const (a b : Int) :
    ∀ l : List (Nat × Nat), diffs (fun _ => a) l = diffs (fun _ => b) l
```

[`LigoCongruence.diffs_const`](../../PerfectAssociation/LigoCongruence.lean#L194)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L285) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.pairwise_invalid_for_common_mode_list</code></summary>

```lean
theorem pairwise_invalid_for_common_mode_list (N : Nat) (hN : 0 < N) {β : Sort u}
    (S : List Int → β) (l : List (Nat × Nat)) :
    IsInvalidFor (fun ε : Nat → Int => S (diffs ε l)) (fun ε => sumTo N ε)
```

[`LigoCongruence.pairwise_invalid_for_common_mode_list`](../../PerfectAssociation/LigoCongruence.lean#L200)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L286) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.pairwise_blind</code></summary>

```lean
theorem pairwise_blind {β : Sort u} (S : (Nat → Nat → Int) → β)
    (hS : ∀ f f' : Nat → Nat → Int, (∀ i j, f i j = f' i j) → S f = S f')
    (ε : Nat → Int) (g : Int) :
    S (fun i j => (ε i + g) - (ε j + g)) = S (fun i j => ε i - ε j)
```

[`LigoCongruence.pairwise_blind`](../../PerfectAssociation/LigoCongruence.lean#L209)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L287) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.pairwise_invalid_for_common_mode</code></summary>

```lean
theorem pairwise_invalid_for_common_mode (N : Nat) (hN : 0 < N) {β : Sort u}
    (S : (Nat → Nat → Int) → β) :
    IsInvalidFor (fun ε : Nat → Int => S (fun i j => ε i - ε j))
                 (fun ε => sumTo N ε)
```

[`LigoCongruence.pairwise_invalid_for_common_mode`](../../PerfectAssociation/LigoCongruence.lean#L215)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L288) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.mixVar4_blind</code></summary>

```lean
theorem mixVar4_blind (m1 m2 v1 v2 b : Int) :
    mixVar4 (m1 + b) (m2 + b) v1 v2 = mixVar4 m1 m2 v1 v2
```

[`LigoCongruence.mixVar4_blind`](../../PerfectAssociation/LigoCongruence.lean#L226)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L290) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.mixVar4_invalid_for_location</code></summary>

```lean
theorem mixVar4_invalid_for_location (v1 v2 : Int) :
    IsInvalidFor (fun m : Int × Int => mixVar4 m.1 m.2 v1 v2) (fun m => m.1)
```

[`LigoCongruence.mixVar4_invalid_for_location`](../../PerfectAssociation/LigoCongruence.lean#L232)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L291) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.parallelogram</code></summary>

```lean
theorem parallelogram (a b : Int) :
    (a + b) * (a + b) + (a - b) * (a - b) = 2 * (a * a + b * b)
```

[`LigoCongruence.parallelogram`](../../PerfectAssociation/LigoCongruence.lean#L237)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L292) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.mixVar4_from_moments</code></summary>

```lean
theorem mixVar4_from_moments (m1 m2 v1 v2 : Int) :
    2 * ((v1 + m1 * m1) + (v2 + m2 * m2)) - (m1 + m2) * (m1 + m2) = mixVar4 m1 m2 v1 v2
```

[`LigoCongruence.mixVar4_from_moments`](../../PerfectAssociation/LigoCongruence.lean#L250)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L293) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.eta_swap</code></summary>

```lean
theorem eta_swap (m1 m2 : Int) : etaNum m1 m2 = etaNum m2 m1
```

[`LigoCongruence.eta_swap`](../../PerfectAssociation/LigoCongruence.lean#L262)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L295) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.prod_mk_congr</code></summary>

```lean
theorem prod_mk_congr {α : Type u} {β : Type v} {a a' : α} {b b' : β}
    (h₁ : a = a') (h₂ : b = b') : (a, b) = (a', b')
```

[`LigoCongruence.prod_mk_congr`](../../PerfectAssociation/LigoCongruence.lean#L267)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L297) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.etaPair_swap</code></summary>

```lean
theorem etaPair_swap (m1 m2 : Int) : etaPair (m1, m2) = etaPair (m2, m1)
```

[`LigoCongruence.etaPair_swap`](../../PerfectAssociation/LigoCongruence.lean#L273)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L298) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.eta_invalid_for_q</code></summary>

```lean
theorem eta_invalid_for_q : IsInvalidFor etaPair (fun m : Int × Int => m.1)
```

[`LigoCongruence.eta_invalid_for_q`](../../PerfectAssociation/LigoCongruence.lean#L277)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L299) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.eta_invalid_of_ne</code></summary>

```lean
theorem eta_invalid_of_ne (a b : Int) (h : a ≠ b) :
    IsInvalidFor etaPair (fun m : Int × Int => m.1)
```

[`LigoCongruence.eta_invalid_of_ne`](../../PerfectAssociation/LigoCongruence.lean#L281)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L300) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.four_mul_eq</code></summary>

```lean
theorem four_mul_eq (x : Int) : 4 * x = x + x + x + x
```

[`LigoCongruence.four_mul_eq`](../../PerfectAssociation/LigoCongruence.lean#L285)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L301) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.sq_diff_core</code></summary>

```lean
theorem sq_diff_core (p q r : Int) :
    p + q + (q + r) - (p - q - (q - r)) = q + q + q + q
```

[`LigoCongruence.sq_diff_core`](../../PerfectAssociation/LigoCongruence.lean#L289)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L302) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.eta_fold</code></summary>

```lean
theorem eta_fold (m1 m2 : Int) :
    4 * etaNum m1 m2 = (m1 + m2) * (m1 + m2) - (m1 - m2) * (m1 - m2)
```

[`LigoCongruence.eta_fold`](../../PerfectAssociation/LigoCongruence.lean#L299)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L303) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.sysVar2_blind</code></summary>

```lean
theorem sysVar2_blind (xE xP xO g : Int) :
    sysVar2 (xE + g) (xP + g) (xO + g) = sysVar2 xE xP xO
```

[`LigoCongruence.sysVar2_blind`](../../PerfectAssociation/LigoCongruence.lean#L312)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L305) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.uncertainty_triple_invalid_for_shared_error</code></summary>

```lean
theorem uncertainty_triple_invalid_for_shared_error (μE μP vE vP xE xP xO : Int) :
    IsInvalidFor
      (fun g : Int => (mixVar4 (μE + g) (μP + g) vE vP,
                       (sysVar2 (xE + g) (xP + g) (xO + g), (μE + g) - (μP + g))))
      (fun g => g)
```

[`LigoCongruence.uncertainty_triple_invalid_for_shared_error`](../../PerfectAssociation/LigoCongruence.lean#L320)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L306) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.spin_triangle</code></summary>

```lean
theorem spin_triangle (c β δ d : Int) :
    (psi15 c β (δ + d) - c) - (psi15 c β (δ - d) - c) = d + d ∧
    ((psi15 c β (δ + d) - c) + (psi15 c β (δ - d) - c)) - (4 * β + 4 * β) = δ + δ
```

[`LigoCongruence.spin_triangle`](../../PerfectAssociation/LigoCongruence.lean#L334)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L307) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.spin_gap_invalid_for_bias</code></summary>

```lean
theorem spin_gap_invalid_for_bias (c β d : Int) :
    IsInvalidFor (fun δ : Int => (psi15 c β (δ + d) - c) - (psi15 c β (δ - d) - c))
                 (fun δ => ((psi15 c β (δ + d) - c) + (psi15 c β (δ - d) - c)) - (4 * β + 4 * β))
```

[`LigoCongruence.spin_gap_invalid_for_bias`](../../PerfectAssociation/LigoCongruence.lean#L341)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L308) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.fold_shift</code></summary>

```lean
theorem fold_shift (M Δ e : Int) :
    (M * M - Δ * Δ) - (M * M - (Δ + e) * (Δ + e)) = e * (Δ + Δ + e)
```

[`LigoCongruence.fold_shift`](../../PerfectAssociation/LigoCongruence.lean#L350)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L309) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.fold_flat_at_equal_mass</code></summary>

```lean
theorem fold_flat_at_equal_mass (M e : Int) :
    (M * M - 0 * 0) - (M * M - (0 + e) * (0 + e)) = e * e
```

[`LigoCongruence.fold_flat_at_equal_mass`](../../PerfectAssociation/LigoCongruence.lean#L356)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L310) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.gw150914_fold_shift</code></summary>

```lean
theorem gw150914_fold_shift :
    (712 * 712 - 62 * 62) - (712 * 712 - 72 * 72) = (1340 : Int) ∧
    4 * etaNum 387 325 = 503100
```

[`LigoCongruence.gw150914_fold_shift`](../../PerfectAssociation/LigoCongruence.lean#L362)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L311) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.lockpoint_any_symmetric</code></summary>

```lean
theorem lockpoint_any_symmetric {β : Sort u} (F : (Int × Int) × (Int × Int) → β)
    (hF : ∀ p q, F (p, q) = F (q, p)) (a x y : Int) (h : x ≠ y) :
    IsInvalidFor F (fun s => s.1.2)
```

[`LigoCongruence.lockpoint_any_symmetric`](../../PerfectAssociation/LigoCongruence.lean#L375)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L313) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.massSpinObs_symm</code></summary>

```lean
theorem massSpinObs_symm (p q : Int × Int) :
    (p.1 + q.1, (etaNum p.1 q.1, effNum p.1 q.1 p.2 q.2)) =
      (q.1 + p.1, (etaNum q.1 p.1, effNum q.1 p.1 q.2 p.2))
```

[`LigoCongruence.massSpinObs_symm`](../../PerfectAssociation/LigoCongruence.lean#L381)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L314) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.lockpoint_invalid_for_primary_spin</code></summary>

```lean
theorem lockpoint_invalid_for_primary_spin (a x y : Int) (h : x ≠ y) :
    IsInvalidFor (fun s : (Int × Int) × (Int × Int) =>
        (s.1.1 + s.2.1, (etaNum s.1.1 s.2.1, effNum s.1.1 s.2.1 s.1.2 s.2.2)))
      (fun s => s.1.2)
```

[`LigoCongruence.lockpoint_invalid_for_primary_spin`](../../PerfectAssociation/LigoCongruence.lean#L388)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L315) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.spin_attribution_signal</code></summary>

```lean
theorem spin_attribution_signal (a b x y : Int) :
    effNum a b x y - effNum a b y x = (a - b) * (x - y)
```

[`LigoCongruence.spin_attribution_signal`](../../PerfectAssociation/LigoCongruence.lean#L396)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L316) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.gw150914_attribution_weight</code></summary>

```lean
theorem gw150914_attribution_weight :
    effNum 387 325 10 0 - effNum 387 325 0 10 = (620 : Int) ∧
    effNum 387 325 10 10 - effNum 387 325 0 0 = (7120 : Int)
```

[`LigoCongruence.gw150914_attribution_weight`](../../PerfectAssociation/LigoCongruence.lean#L405)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L317) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.strain_statistic_invalid_for_cause</code></summary>

```lean
theorem strain_statistic_invalid_for_cause {D : Type} {β : Sort u} (S : D → β) (d : D) :
    IsInvalidFor (fun s : D × Cause => S s.1) (fun s => s.2)
```

[`LigoCongruence.strain_statistic_invalid_for_cause`](../../PerfectAssociation/LigoCongruence.lean#L418)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L319) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.detection_odds_frozen</code></summary>

```lean
theorem detection_odds_frozen (πgw πcorr ℓ : Int) :
    SameRatio (πgw * ℓ) (πcorr * ℓ) πgw πcorr
```

[`LigoCongruence.detection_odds_frozen`](../../PerfectAssociation/LigoCongruence.lean#L424)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L320) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.pem_fails_on_uncoupled</code></summary>

```lean
theorem pem_fails_on_uncoupled {D : Type} (d : D) :
    IsInvalidFor (fun s : D × (Cause × Bool) => (s.1, pem s.2)) (fun s => s.2.1)
```

[`LigoCongruence.pem_fails_on_uncoupled`](../../PerfectAssociation/LigoCongruence.lean#L435)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L322) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.pem_repairs_when_coupled</code></summary>

```lean
theorem pem_repairs_when_coupled {D : Type} :
    IsValidFor
      (fun s : {s : D × (Cause × Bool) // s.2.1 = Cause.corr → s.2.2 = true} =>
        (s.1.1, pem s.1.2))
      (fun s => s.1.2.1)
```

[`LigoCongruence.pem_repairs_when_coupled`](../../PerfectAssociation/LigoCongruence.lean#L440)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L323) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.every_procedure_errs</code></summary>

```lean
theorem every_procedure_errs {α : Sort u} {β : Sort v} {γ : Sort w}
    (Φ : α → β) (R : α → γ) {a b : α} (hΦ : Φ a = Φ b) (hR : R a ≠ R b) (w : β → γ) :
    ¬ (w (Φ a) = R a ∧ w (Φ b) = R b)
```

[`LigoCongruence.every_procedure_errs`](../../PerfectAssociation/LigoCongruence.lean#L456)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L324) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.conservation_of_distinction</code></summary>

```lean
theorem conservation_of_distinction {α : Sort u} {β : Sort v} {δ : Sort x}
    (Φ : α → β) (P : β → δ) {a b : α} (h : Φ a = Φ b) : P (Φ a) = P (Φ b)
```

[`LigoCongruence.conservation_of_distinction`](../../PerfectAssociation/LigoCongruence.lean#L462)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L325) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.detection_pipeline_blind</code></summary>

```lean
theorem detection_pipeline_blind {D Y₁ Y₂ Y₃ : Type} (C : D → Y₁) (L : Y₁ → Y₂) (B : Y₂ → Y₃)
    (d : D) :
    IsInvalidFor (fun s : D × Cause => B (L (C s.1))) (fun s => s.2)
```

[`LigoCongruence.detection_pipeline_blind`](../../PerfectAssociation/LigoCongruence.lean#L469)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L326) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.detection_rule_errs</code></summary>

```lean
theorem detection_rule_errs {D Y : Type} (P : D → Y) (rule : Y → Cause) (d : D) :
    ¬ (rule (P d) = Cause.gw ∧ rule (P d) = Cause.corr)
```

[`LigoCongruence.detection_rule_errs`](../../PerfectAssociation/LigoCongruence.lean#L476)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L327) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.pe_pipeline_blind</code></summary>

```lean
theorem pe_pipeline_blind {Y : Sort u} (B : Int × (Int × Int) → Y) (μE μP vE vP xE xP xO : Int) :
    IsInvalidFor
      (fun g : Int => B (mixVar4 (μE + g) (μP + g) vE vP,
                         (sysVar2 (xE + g) (xP + g) (xO + g), (μE + g) - (μP + g))))
      (fun g => g)
```

[`LigoCongruence.pe_pipeline_blind`](../../PerfectAssociation/LigoCongruence.lean#L482)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L328) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>LigoCongruence.lockpoint_pipeline_blind</code></summary>

```lean
theorem lockpoint_pipeline_blind {β : Sort u} {Y : Sort v} (F : (Int × Int) × (Int × Int) → β)
    (hF : ∀ p q, F (p, q) = F (q, p)) (P : β → Y) (a x y : Int) (h : x ≠ y) :
    IsInvalidFor (fun s => P (F s)) (fun s => s.1.2)
```

[`LigoCongruence.lockpoint_pipeline_blind`](../../PerfectAssociation/LigoCongruence.lean#L491)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L329) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>
