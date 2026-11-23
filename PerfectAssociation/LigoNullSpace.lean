import PerfectAssociation.LigoCongruence

/-!
# LIGO null-space audit: sum and difference, the common mode, anchors and the update

Core Lean 4 only.  Every definition is computable.  Closed certificates are kernel evaluations
(`decide`); general statements are proved from core `Int`, `Nat` and `List` lemmas.

We use the calculus of `LigoCongruence`: an observable `Φ` is valid for a target `R` when
`Ker Φ ⊆ Ker R`, and invalid for `R` when two states with the same `Φ`-image have different
`R`-images.  Validity is the factorisation of `R` through `Φ`; invalidity forbids every
factorisation, every post-processing and every downstream inference.

Displacements are integers in the unit `10⁻¹⁵ am = 10⁻³³ m`.  The reconstructed Hanford
resultant of GW150914, converted from strain to differential displacement, is
`R⋆ = 3.969245147706565 am`, the integer `3969245147706565`.

* §1 Sum and difference.  `(S, D) = (X₁ + X₂, X₁ − X₂)` has determinant `−2` and loses nothing.
  `D` alone annihilates the common direction `(1, 1)`; `S` is exactly the anchor that restores it.
  At `R⋆` the common levels `3.969 am`, `103.969 am` and `396.9 nm` share `D = 0`.
* §2 The projectors `2P₊` and `2P₋`: resolution of the identity, idempotence, orthogonality.
* §3 Factorisation: the linear target `aX₁ + bX₂` is a function of `D` exactly when `a + b = 0`.
* §4 No function of `D` bounds `S`; every estimate of `S` from `D` has unbounded error.
* §5 The model `X₁ = P + g + d`, `X₂ = P + g − d`.  `D` determines `d` alone; `(S, D)`
  determines `P + g` and `d` and leaves the line `(P + c, g − c, d)`.
* §6 The anchor `A = αP + βg`: `(P + g, A)` determines `(P, g)` exactly when `α ≠ β`, with the
  inversion formulas, and the Fisher determinant of the anchored system is `4 (α − β)²`.
* §7 Fisher information: every kernel direction carries zero information, for every number of
  observations.
* §8 Tests on `D`: the hypotheses `P + g = 4 am` and `P + g = 400 nm` have one law; their total
  variation is `0`, their likelihood ratio is `1`, every test accepts both with equal mass.
* §9 The Bayesian update.  Posterior odds of two common levels equal their prior odds.  A prior
  coupling moves the posterior of a coordinate absent from the likelihood.  The
  Kolmogorov–Smirnov deviation of a posterior from its prior is not a function of the
  likelihood.  A calibration prior is transported into the source value along the fibre.
* §10 Common error and apparent precision: `Var D = 2σ²` for every `τ`, while
  `Var (R⋆ − P) = τ² + σ²/2`.
* §11 Any number of channels.
* §12 The null-space audit of a validation suite: the criterion `ker M ⊄ ker T`, its exactness,
  redundancy, and a six-coordinate architecture with shared calibration, timing, actuation and
  sensing offsets.
* §13 Two-sided statistics: direction, effect size, cell pattern, the KS supremum, thresholds.
* §14 The invalidations of the methodology of Abbott et al., *Improved analysis of GW150914
  using a fully spin-precessing waveform model*, Phys. Rev. X 6, 041014 (2016).
-/

namespace LigoNullSpace

open LigoCongruence (Ker IsValidFor IsInvalidFor invalid_not_valid invalid_no_factor no_repair
  invalid_postcompose anchor_valid SameRatio posterior_odds_frozen cons_congr prod_mk_congr
  diffs sumTo pairwise_invalid_for_common_mode_list)

universe u v w

/-! ## §1 Sum and difference -/

/-- The sum coordinate `S = X₁ + X₂`. -/
def sumC (X : Int × Int) : Int := X.1 + X.2

/-- The difference coordinate `D = X₁ − X₂`. -/
def difC (X : Int × Int) : Int := X.1 - X.2

/-- The change of variables `(X₁, X₂) ↦ (S, D)`. -/
def sdMap (X : Int × Int) : Int × Int := (sumC X, difC X)

/-- The determinant of the integer matrix `[[a, b], [c, d]]`. -/
def det2 (a b c d : Int) : Int := a * d - b * c

/-- The matrix `[[1, 1], [1, −1]]` of `(S, D)` has determinant `−2`. -/
theorem sd_det : det2 1 1 1 (-1) = -2 := by decide

/-- The inverse of `(S, D)`, cleared of the factor `2`: `2X₁ = S + D` and `2X₂ = S − D`. -/
theorem sd_inverse (x₁ x₂ : Int) :
    2 * x₁ = sumC (x₁, x₂) + difC (x₁, x₂) ∧ 2 * x₂ = sumC (x₁, x₂) - difC (x₁, x₂) := by
  show 2 * x₁ = x₁ + x₂ + (x₁ - x₂) ∧ 2 * x₂ = x₁ + x₂ - (x₁ - x₂)
  constructor <;> omega

/-- `(S, D)` is injective: the change of variables loses nothing. -/
theorem sd_injective : IsValidFor sdMap (fun X : Int × Int => X) := by
  intro X Y h
  obtain ⟨x₁, x₂⟩ := X
  obtain ⟨y₁, y₂⟩ := Y
  have hS : x₁ + x₂ = y₁ + y₂ := congrArg Prod.fst h
  have hD : x₁ - x₂ = y₁ - y₂ := congrArg Prod.snd h
  show (x₁, x₂) = (y₁, y₂)
  exact prod_mk_congr (by omega) (by omega)

/-- **The two symmetries.**  A common shift `g` leaves `D` unchanged and moves `S` by `2g`. -/
theorem common_shift (x₁ x₂ g : Int) :
    difC (x₁ + g, x₂ + g) = difC (x₁, x₂) ∧ sumC (x₁ + g, x₂ + g) = sumC (x₁, x₂) + 2 * g := by
  show x₁ + g - (x₂ + g) = x₁ - x₂ ∧ x₁ + g + (x₂ + g) = x₁ + x₂ + 2 * g
  constructor <;> omega

/-- The fibre of `D` through `(x₁, x₂)` is the common-mode line `(x₁ + g, x₂ + g)`. -/
theorem difC_fibre (x₁ x₂ y₁ y₂ : Int) :
    difC (x₁, x₂) = difC (y₁, y₂) ↔ ∃ g : Int, y₁ = x₁ + g ∧ y₂ = x₂ + g := by
  show x₁ - x₂ = y₁ - y₂ ↔ ∃ g : Int, y₁ = x₁ + g ∧ y₂ = x₂ + g
  constructor
  · intro h
    exact ⟨y₁ - x₁, by omega, by omega⟩
  · intro hg
    obtain ⟨g, h1, h2⟩ := hg
    omega

/-- `D = 0` certifies the equality of the two values. -/
theorem difC_zero_iff (x₁ x₂ : Int) : difC (x₁, x₂) = 0 ↔ x₁ = x₂ := by
  show x₁ - x₂ = 0 ↔ x₁ = x₂
  constructor
  · intro h
    omega
  · intro h
    omega

/-- **Equality is not level.**  `D = 0` holds at every common level `P + g`; the common error `g`
is recorded by `S` alone. -/
theorem agreement_is_not_level (P g : Int) :
    difC (P + g, P + g) = 0 ∧ sumC (P + g, P + g) - 2 * P = 2 * g := by
  show P + g - (P + g) = 0 ∧ P + g + (P + g) - 2 * P = 2 * g
  constructor <;> omega

/-- `D` is invalid for `S`: the states `(0, 0)` and `(1, 1)`. -/
theorem difC_invalid_for_sum : IsInvalidFor difC sumC :=
  ⟨(0, 0), (1, 1), by decide, by decide⟩

/-- `S` is no function of `D`. -/
theorem sum_not_factor : ¬ ∃ w : Int → Int, ∀ X, sumC X = w (difC X) :=
  invalid_no_factor difC sumC difC_invalid_for_sum

/-- `S` separates every pair of states that `D` merges. -/
theorem sum_separates (X Y : Int × Int) (hD : Ker difC X Y)
    (hne : ¬ Ker (fun Z : Int × Int => Z) X Y) : ¬ Ker sumC X Y := by
  intro hS
  apply hne
  obtain ⟨x₁, x₂⟩ := X
  obtain ⟨y₁, y₂⟩ := Y
  have hD' : x₁ - x₂ = y₁ - y₂ := hD
  have hS' : x₁ + x₂ = y₁ + y₂ := hS
  show (x₁, x₂) = (y₁, y₂)
  exact prod_mk_congr (by omega) (by omega)

/-- **`S` is the anchor of `D`.**  By the anchor criterion, adjoining `S` to `D` determines the
state. -/
theorem sum_anchors_difference :
    IsValidFor (fun X : Int × Int => (difC X, sumC X)) (fun X : Int × Int => X) :=
  (anchor_valid difC sumC (fun X : Int × Int => X)).mpr sum_separates

/-! ### The Hanford resultant -/

/-- One attometre, `10⁻¹⁸ m`, in the unit `10⁻¹⁵ am`. -/
def am : Int := 1000000000000000

/-- One nanometre, `10⁹ am`. -/
def nm : Int := 1000000000 * am

/-- The reconstructed Hanford resultant `R⋆ = 3.969245147706565 am`. -/
def rStar : Int := 3969245147706565

/-- `R⋆ · 10¹¹ = 3.969245147706565 × 10¹¹ am = 396.9245147706565 nm`. -/
def rStarBig : Int := rStar * 100000000000

/-- **The coordinates at `R⋆`.**  With `X₁ = X₂ = R⋆`: `S = 7.93849029541313 am` and `D = 0`.
The common levels `R⋆ + 1 am`, `R⋆ + 100 am` and `R⋆ · 10¹¹` give
`S = 9.93849029541313 am`, `207.93849029541313 am` and `793.849029541313 nm`, all with `D = 0`;
the last level is `396.9245147706565 nm`. -/
theorem hanford_sd :
    sdMap (rStar, rStar) = (7938490295413130, 0) ∧
    sdMap (rStar + am, rStar + am) = (9938490295413130, 0) ∧
    sdMap (rStar + 100 * am, rStar + 100 * am) = (207938490295413130, 0) ∧
    sdMap (rStarBig, rStarBig) = (793849029541313000000000000, 0) ∧
    rStarBig = 396 * nm + 924514770656500000000000 := by
  decide

/-- **`D` cannot separate `3.969 am` from `396.9 nm`.** -/
theorem hanford_levels_merged :
    IsInvalidFor difC sumC ∧
    Ker difC (rStar, rStar) (rStar + 100 * am, rStar + 100 * am) ∧
    Ker difC (rStar, rStar) (rStarBig, rStarBig) ∧
    ¬ Ker sumC (rStar, rStar) (rStarBig, rStarBig) :=
  ⟨⟨(rStar, rStar), (rStarBig, rStarBig), by decide, by decide⟩, by decide, by decide,
    by decide⟩

/-- The published median of the mass ratio is `0.84` for both precessing models (Table I).  The
common-mode line through it sweeps the published 90% interval `[0.64, 0.98]` at `D = 0`. -/
theorem tableI_q_common_line :
    difC (84, 84) = 0 ∧ sumC (84, 84) = 168 ∧
    ∀ k ∈ List.range 35, difC (64 + Int.ofNat k, 64 + Int.ofNat k) = 0 := by
  decide

/-! ## §2 The common and differential projectors -/

/-- Twice the common-mode projector, `2P₊ = [[1, 1], [1, 1]]`. -/
def projP2 (X : Int × Int) : Int × Int := (X.1 + X.2, X.1 + X.2)

/-- Twice the differential projector, `2P₋ = [[1, −1], [−1, 1]]`. -/
def projM2 (X : Int × Int) : Int × Int := (X.1 - X.2, X.2 - X.1)

/-- `2P₊ + 2P₋ = 2I`. -/
theorem projector_resolution (x₁ x₂ : Int) :
    (projP2 (x₁, x₂)).1 + (projM2 (x₁, x₂)).1 = 2 * x₁ ∧
    (projP2 (x₁, x₂)).2 + (projM2 (x₁, x₂)).2 = 2 * x₂ := by
  show x₁ + x₂ + (x₁ - x₂) = 2 * x₁ ∧ x₁ + x₂ + (x₂ - x₁) = 2 * x₂
  constructor <;> omega

/-- `(2P₊)² = 2 · 2P₊`, `(2P₋)² = 2 · 2P₋`, and `2P₋ · 2P₊ = 2P₊ · 2P₋ = 0`. -/
theorem projector_squares (x₁ x₂ : Int) :
    projP2 (projP2 (x₁, x₂)) = (2 * (x₁ + x₂), 2 * (x₁ + x₂)) ∧
    projM2 (projM2 (x₁, x₂)) = (2 * (x₁ - x₂), 2 * (x₂ - x₁)) ∧
    projM2 (projP2 (x₁, x₂)) = (0, 0) ∧ projP2 (projM2 (x₁, x₂)) = (0, 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (x₁ + x₂ + (x₁ + x₂), x₁ + x₂ + (x₁ + x₂)) = (2 * (x₁ + x₂), 2 * (x₁ + x₂))
    exact prod_mk_congr (by omega) (by omega)
  · show (x₁ - x₂ - (x₂ - x₁), x₂ - x₁ - (x₁ - x₂)) = (2 * (x₁ - x₂), 2 * (x₂ - x₁))
    exact prod_mk_congr (by omega) (by omega)
  · show (x₁ + x₂ - (x₁ + x₂), x₁ + x₂ - (x₁ + x₂)) = ((0 : Int), (0 : Int))
    exact prod_mk_congr (by omega) (by omega)
  · show (x₁ - x₂ + (x₂ - x₁), x₁ - x₂ + (x₂ - x₁)) = ((0 : Int), (0 : Int))
    exact prod_mk_congr (by omega) (by omega)

/-- `2P₋` annihilates the common direction `(c, c)`. -/
theorem projM2_common (c : Int) : projM2 (c, c) = (0, 0) := by
  show (c - c, c - c) = ((0 : Int), (0 : Int))
  exact prod_mk_congr (Int.sub_self c) (Int.sub_self c)

/-! ## §3 The factorisation criterion -/

/-- The linear target `T(X) = aX₁ + bX₂`. -/
def linT (a b : Int) (X : Int × Int) : Int := a * X.1 + b * X.2

/-- A common shift by `c` moves `aX₁ + bX₂` by `(a + b) c`. -/
theorem linT_shift (a b x₁ x₂ c : Int) :
    linT a b (x₁ + c, x₂ + c) = linT a b (x₁, x₂) + (a + b) * c := by
  show a * (x₁ + c) + b * (x₂ + c) = a * x₁ + b * x₂ + (a + b) * c
  simp only [Int.mul_add, Int.add_mul]
  omega

/-- **Factorisation criterion.**  The linear target `aX₁ + bX₂` is a function of `D` exactly when
`a + b = 0`. -/
theorem linT_valid_iff (a b : Int) : IsValidFor difC (linT a b) ↔ a + b = 0 := by
  constructor
  · intro hv
    have h : linT a b (0, 0) = linT a b (1, 1) := hv (0, 0) (1, 1) (by decide)
    have h' : a * 0 + b * 0 = a * 1 + b * 1 := h
    omega
  · intro hab X Y hD
    obtain ⟨x₁, x₂⟩ := X
    obtain ⟨y₁, y₂⟩ := Y
    have hD' : x₁ - x₂ = y₁ - y₂ := hD
    have h1 : (a + b) * x₂ = 0 * x₂ := congrArg (fun t => t * x₂) hab
    have h2 : (a + b) * y₂ = 0 * y₂ := congrArg (fun t => t * y₂) hab
    have hm : a * (x₁ - x₂) = a * (y₁ - y₂) := congrArg (fun t => a * t) hD'
    simp only [Int.add_mul, Int.zero_mul, Int.mul_sub] at h1 h2 hm
    show a * x₁ + b * x₂ = a * y₁ + b * y₂
    omega

/-- The sum, and with it the resultant `(X₁ + X₂)/2`, is no function of `D`: `1 + 1 ≠ 0`. -/
theorem sum_not_valid_for_difference : ¬ IsValidFor difC (linT 1 1) :=
  fun h => absurd ((linT_valid_iff 1 1).mp h) (by decide)

/-- The difference itself is a function of `D`: `1 + (−1) = 0`. -/
theorem difference_valid_for_difference : IsValidFor difC (linT 1 (-1)) :=
  (linT_valid_iff 1 (-1)).mpr (by decide)

/-! ## §4 Agreement bounds nothing -/

/-- **No bound from agreement.**  For every function `B` there is a state with `D = 0` and
`S > B(D)`. -/
theorem no_bound_from_difference (B : Int → Int) :
    ∃ X : Int × Int, difC X = 0 ∧ B (difC X) < sumC X := by
  refine if h : 0 ≤ B 0 then ?_ else ?_
  · have hd : difC (B 0 + 1, B 0 + 1) = 0 := by
      show B 0 + 1 - (B 0 + 1) = 0
      omega
    refine ⟨(B 0 + 1, B 0 + 1), hd, ?_⟩
    rw [hd]
    show B 0 < B 0 + 1 + (B 0 + 1)
    omega
  · have hd : difC (0, 0) = 0 := by decide
    refine ⟨(0, 0), hd, ?_⟩
    rw [hd]
    show B 0 < 0 + 0
    omega

/-- No function of `D` bounds `S` from above. -/
theorem no_finite_bound : ¬ ∃ B : Int → Int, ∀ X : Int × Int, sumC X ≤ B (difC X) := by
  intro hex
  obtain ⟨B, hB⟩ := hex
  obtain ⟨X, _, hX⟩ := no_bound_from_difference B
  have h := hB X
  omega

/-- A rule applied to equal observations cannot return two different targets. -/
theorem rule_errs_on_pair {α : Sort u} {β : Sort v} {γ : Sort w} (Φ : α → β) (R : α → γ)
    {a b : α} (hΦ : Φ a = Φ b) (hR : R a ≠ R b) (rule : β → γ) :
    ¬ (rule (Φ a) = R a ∧ rule (Φ b) = R b) :=
  fun ⟨ha, hb⟩ => hR (ha.symm.trans ((congrArg rule hΦ).trans hb))

/-- An estimate `e` of two values `S₁` and `S₂` misses one of them by at least half their gap. -/
theorem estimate_error_split (e S₁ S₂ : Int) :
    S₂ - S₁ ≤ 2 * (e - S₁) ∨ S₂ - S₁ ≤ 2 * (S₂ - e) :=
  if h : S₂ - S₁ ≤ 2 * (e - S₁) then Or.inl h else Or.inr (by omega)

/-- **Unbounded worst-case error.**  For every estimate `f` of `S` from `D` and every `K` there is
a state with `D = 0` on which `f` misses `S` by at least `K`. -/
theorem difference_estimator_unbounded (f : Int → Int) (K : Int) :
    ∃ X : Int × Int, difC X = 0 ∧ (K ≤ f (difC X) - sumC X ∨ K ≤ sumC X - f (difC X)) := by
  refine if h : K ≤ f 0 then ?_ else ?_
  · have hd : difC (0, 0) = 0 := by decide
    refine ⟨(0, 0), hd, Or.inl ?_⟩
    rw [hd]
    show K ≤ f 0 - (0 + 0)
    omega
  · have hd : difC (K, K) = 0 := by
      show K - K = 0
      omega
    refine ⟨(K, K), hd, Or.inr ?_⟩
    rw [hd]
    show K ≤ K + K - f 0
    omega

/-! ## §5 Truth, common error and differential error -/

/-- The source value `P`, the common reconstruction error `g` and the differential error `d`. -/
structure PGD where
  P : Int
  g : Int
  d : Int

/-- The two reconstructions `X₁ = P + g + d` and `X₂ = P + g − d`. -/
def recon (θ : PGD) : Int × Int := (θ.P + θ.g + θ.d, θ.P + θ.g - θ.d)

/-- The difference channel `D = X₁ − X₂`. -/
def obsD (θ : PGD) : Int := difC (recon θ)

/-- The sum channel `S = X₁ + X₂`. -/
def obsS (θ : PGD) : Int := sumC (recon θ)

/-- The pair `(S, D)`. -/
def obsSD (θ : PGD) : Int × Int := (obsS θ, obsD θ)

/-- `D = 2d` and `S = 2(P + g)`. -/
theorem obs_formulas (θ : PGD) : obsD θ = 2 * θ.d ∧ obsS θ = 2 * (θ.P + θ.g) := by
  show θ.P + θ.g + θ.d - (θ.P + θ.g - θ.d) = 2 * θ.d ∧
    θ.P + θ.g + θ.d + (θ.P + θ.g - θ.d) = 2 * (θ.P + θ.g)
  constructor <;> omega

/-- `D` does not contain `P` or `g`. -/
theorem obsD_level_free (P g d : Int) : obsD ⟨P, g, d⟩ = 2 * d :=
  (obs_formulas ⟨P, g, d⟩).1

/-- `D` reads `d` alone; the directions `(1, 0, 0)` and `(0, 1, 0)` lie in its kernel. -/
theorem obsD_kernel :
    (∀ θ θ' : PGD, obsD θ = obsD θ' ↔ θ.d = θ'.d) ∧ obsD ⟨1, 0, 0⟩ = 0 ∧ obsD ⟨0, 1, 0⟩ = 0 := by
  refine ⟨?_, by decide, by decide⟩
  intro θ θ'
  have h := (obs_formulas θ).1
  have h' := (obs_formulas θ').1
  constructor
  · intro e
    omega
  · intro e
    omega

/-- `D` determines `d`. -/
theorem obsD_valid_for_d : IsValidFor obsD PGD.d :=
  fun θ θ' h => (obsD_kernel.1 θ θ').mp h

/-- `D` is invalid for the source value `P`. -/
theorem obsD_invalid_for_P : IsInvalidFor obsD PGD.P :=
  ⟨⟨0, 0, 0⟩, ⟨1, 0, 0⟩, by decide, by decide⟩

/-- `D` is invalid for the common error `g`. -/
theorem obsD_invalid_for_g : IsInvalidFor obsD PGD.g :=
  ⟨⟨0, 0, 0⟩, ⟨0, 1, 0⟩, by decide, by decide⟩

/-- `D` is invalid for the common level `P + g`. -/
theorem obsD_invalid_for_level : IsInvalidFor obsD (fun θ : PGD => θ.P + θ.g) :=
  ⟨⟨0, 0, 0⟩, ⟨1, 0, 0⟩, by decide, by decide⟩

/-- The fibres of `(S, D)`: equal common level and equal differential error. -/
theorem obsSD_kernel (θ θ' : PGD) :
    obsSD θ = obsSD θ' ↔ θ.P + θ.g = θ'.P + θ'.g ∧ θ.d = θ'.d := by
  have hD := (obs_formulas θ).1
  have hS := (obs_formulas θ).2
  have hD' := (obs_formulas θ').1
  have hS' := (obs_formulas θ').2
  constructor
  · intro e
    have e1 : obsS θ = obsS θ' := congrArg Prod.fst e
    have e2 : obsD θ = obsD θ' := congrArg Prod.snd e
    constructor <;> omega
  · intro e
    obtain ⟨e1, e2⟩ := e
    show (obsS θ, obsD θ) = (obsS θ', obsD θ')
    exact prod_mk_congr (by omega) (by omega)

/-- **The confounding line.**  `(P + c, g − c, d)` and `(P, g, d)` have the same `(S, D)`. -/
theorem obsSD_orbit (P g d c : Int) : obsSD ⟨P + c, g - c, d⟩ = obsSD ⟨P, g, d⟩ := by
  apply (obsSD_kernel ⟨P + c, g - c, d⟩ ⟨P, g, d⟩).mpr
  constructor
  · show P + c + (g - c) = P + g
    omega
  · rfl

/-- `(S, D)` is invalid for `P`. -/
theorem obsSD_invalid_for_P : IsInvalidFor obsSD PGD.P :=
  ⟨⟨0, 0, 0⟩, ⟨1, -1, 0⟩, by decide, by decide⟩

/-- `(S, D)` is invalid for `g`. -/
theorem obsSD_invalid_for_g : IsInvalidFor obsSD PGD.g :=
  ⟨⟨0, 0, 0⟩, ⟨1, -1, 0⟩, by decide, by decide⟩

/-- `(S, D)` determines the common level `P + g`. -/
theorem obsSD_valid_for_level : IsValidFor obsSD (fun θ : PGD => θ.P + θ.g) :=
  fun θ θ' h => ((obsSD_kernel θ θ').mp h).1

/-- `(S, D)` determines `d`. -/
theorem obsSD_valid_for_d : IsValidFor obsSD PGD.d :=
  fun θ θ' h => ((obsSD_kernel θ θ').mp h).2

/-- **The information hierarchy.**  `D` determines `d` and is invalid for `P`, `g` and `P + g`;
`(S, D)` determines `P + g` and `d` and is invalid for `P` and `g`. -/
theorem information_hierarchy :
    (IsValidFor obsD PGD.d ∧ IsInvalidFor obsD PGD.P ∧ IsInvalidFor obsD PGD.g ∧
      IsInvalidFor obsD (fun θ : PGD => θ.P + θ.g)) ∧
    (IsValidFor obsSD (fun θ : PGD => θ.P + θ.g) ∧ IsValidFor obsSD PGD.d ∧
      IsInvalidFor obsSD PGD.P ∧ IsInvalidFor obsSD PGD.g) :=
  ⟨⟨obsD_valid_for_d, obsD_invalid_for_P, obsD_invalid_for_g, obsD_invalid_for_level⟩,
   ⟨obsSD_valid_for_level, obsSD_valid_for_d, obsSD_invalid_for_P, obsSD_invalid_for_g⟩⟩

/-- **At the Hanford resultant.**  The truth `P = R⋆` with `g = 0`, the truth `R⋆ − 100 am` with
`g = 100 am`, and the truth `R⋆ − 396.9 nm` with `g = 396.9 nm` have the same `(S, D)`. -/
theorem hanford_confounding :
    obsSD ⟨rStar, 0, 0⟩ = (7938490295413130, 0) ∧
    obsSD ⟨rStar, 0, 0⟩ = obsSD ⟨rStar - 100 * am, 100 * am, 0⟩ ∧
    obsSD ⟨rStar, 0, 0⟩ = obsSD ⟨rStar - rStarBig, rStarBig, 0⟩ := by
  decide

/-! ## §6 The anchor -/

/-- The anchor reading `A = αP + βg` of the pair `p = (P, g)`. -/
def anchorRead (α β : Int) (p : Int × Int) : Int := α * p.1 + β * p.2

/-- The level and the anchor: `(P + g, αP + βg)`. -/
def levelAnchor (α β : Int) (p : Int × Int) : Int × Int := (p.1 + p.2, anchorRead α β p)

/-- **The anchor criterion.**  `(P + g, αP + βg)` determines `(P, g)` exactly when `α ≠ β`:
the anchor must couple differently to the source value and to the common error. -/
theorem anchor_valid_iff (α β : Int) :
    IsValidFor (levelAnchor α β) (fun p : Int × Int => p) ↔ α ≠ β := by
  constructor
  · intro hv hαβ
    have hk : Ker (levelAnchor α β) (0, 0) (1, -1) := by
      show ((0 : Int) + 0, α * 0 + β * 0) = (1 + -1, α * 1 + β * -1)
      exact prod_mk_congr (by omega) (by omega)
    have h0 : ((0 : Int), (0 : Int)) = (1, -1) := hv (0, 0) (1, -1) hk
    have h1 : (0 : Int) = 1 := congrArg Prod.fst h0
    omega
  · intro hne p p' h
    obtain ⟨P, g⟩ := p
    obtain ⟨P', g'⟩ := p'
    have h1 : P + g = P' + g' := congrArg Prod.fst h
    have h2 : α * P + β * g = α * P' + β * g' := congrArg Prod.snd h
    have h3 : β * (P + g) = β * (P' + g') := congrArg (fun t => β * t) h1
    simp only [Int.mul_add] at h3
    have h4 : (α - β) * P = (α - β) * P' := by
      simp only [Int.sub_mul]
      omega
    have h5 : α - β ≠ 0 := by omega
    have hP : P = P' := Int.eq_of_mul_eq_mul_left h5 h4
    show (P, g) = (P', g')
    exact prod_mk_congr hP (by omega)

/-- **The inversion formulas**, cleared of `α − β`:
`(α − β) P = A − β (P + g)` and `(α − β) g = α (P + g) − A`. -/
theorem anchor_inversion (α β P g : Int) :
    (α - β) * P = anchorRead α β (P, g) - β * (P + g) ∧
    (α - β) * g = α * (P + g) - anchorRead α β (P, g) := by
  show (α - β) * P = α * P + β * g - β * (P + g) ∧ (α - β) * g = α * (P + g) - (α * P + β * g)
  constructor
  · simp only [Int.sub_mul, Int.mul_add]
    omega
  · simp only [Int.sub_mul, Int.mul_add]
    omega

/-- Another reading of the level is no anchor.  With `α = β = 2` the confounded pairs at the
Hanford resultant stay merged; with `α = 1`, `β = 0` the anchor reads `P` and separates them. -/
theorem anchor_example :
    levelAnchor 1 0 (rStar, 100 * am) = (rStar + 100 * am, rStar) ∧
    levelAnchor 1 0 (rStar - 100 * am, 200 * am) ≠ levelAnchor 1 0 (rStar, 100 * am) ∧
    levelAnchor 2 2 (rStar - 100 * am, 200 * am) = levelAnchor 2 2 (rStar, 100 * am) := by
  decide

/-- **The Fisher determinant of the level block.**
`(w + α²)(w + β²) − (w + αβ)² = w (α − β)²`. -/
theorem fisher_block_det (w α β : Int) :
    (w + α * α) * (w + β * β) - (w + α * β) * (w + α * β) = w * ((α - β) * (α - β)) := by
  have hAB : α * α * (β * β) = α * β * (α * β) := by
    simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  have hwA : α * α * w = w * (α * α) := Int.mul_comm (α * α) w
  have hwC : α * β * w = w * (α * β) := Int.mul_comm (α * β) w
  have hwBA : w * (β * α) = w * (α * β) := congrArg (fun t => w * t) (Int.mul_comm β α)
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
  omega

/-- The anchored determinant vanishes exactly when `α = β`. -/
theorem fisher_singular_iff (α β : Int) : 4 * ((α - β) * (α - β)) = 0 ↔ α = β := by
  constructor
  · intro h
    refine if hab : α = β then hab else ?_
    exfalso
    have hne : α - β ≠ 0 := by omega
    have h2 : (α - β) * (α - β) = (α - β) * 0 := by
      rw [Int.mul_zero]
      omega
    exact hne (Int.eq_of_mul_eq_mul_left hne h2)
  · intro h
    have h' : α - β = 0 := by omega
    simp only [h', Int.mul_zero]

/-! ## §7 Fisher information on the kernel -/

/-- The product of a row `(r_P, r_g, r_d)` with a direction `(v_P, v_g, v_d)`. -/
def dot3 (r v : Int × Int × Int) : Int := r.1 * v.1 + r.2.1 * v.2.1 + r.2.2 * v.2.2

/-- The Fisher form `Σₖ (rₖ · u)(rₖ · v)` of a list of Jacobian rows, for unit noise. -/
def fisher : List (Int × Int × Int) → Int × Int × Int → Int × Int × Int → Int
  | [], _, _ => 0
  | r :: rs, u, v => dot3 r u * dot3 r v + fisher rs u v

/-- **Zero information on the kernel.**  A direction annihilated by every row has Fisher form
`0` against every direction, for every list of rows: repetition of the rows adds nothing. -/
theorem fisher_null : ∀ (rows : List (Int × Int × Int)) (v : Int × Int × Int),
    (∀ r ∈ rows, dot3 r v = 0) → ∀ u, fisher rows u v = 0
  | [], _, _, _ => rfl
  | r :: rs, v, h, u => by
    have h0 : dot3 r v = 0 := h r (List.Mem.head _)
    have h1 : fisher rs u v = 0 :=
      fisher_null rs v (fun r' hr' => h r' (List.Mem.tail _ hr')) u
    show dot3 r u * dot3 r v + fisher rs u v = 0
    rw [h0, h1, Int.mul_zero, Int.add_zero]

/-- The coordinate directions and the rows of `D = 2d` and `S = 2(P + g)`. -/
def eP : Int × Int × Int := (1, 0, 0)
def eG : Int × Int × Int := (0, 1, 0)
def eD : Int × Int × Int := (0, 0, 1)
def rowD : Int × Int × Int := (0, 0, 2)
def rowS : Int × Int × Int := (2, 2, 0)

/-- **The difference channel.**  `I_PP = I_gg = I_Pg = 0` and `I_dd = 4`. -/
theorem fisher_difference_channel :
    fisher [rowD] eP eP = 0 ∧ fisher [rowD] eG eG = 0 ∧ fisher [rowD] eP eG = 0 ∧
    fisher [rowD] eD eD = 4 := by
  decide

/-- **The pair `(S, D)`.**  The level block `[[4, 4], [4, 4]]` is singular, with null direction
`(1, −1, 0)`. -/
theorem fisher_sum_difference :
    fisher [rowS, rowD] eP eP = 4 ∧ fisher [rowS, rowD] eP eG = 4 ∧
    fisher [rowS, rowD] eG eG = 4 ∧ fisher [rowS, rowD] eD eD = 4 ∧
    fisher [rowS, rowD] (1, -1, 0) (1, -1, 0) = 0 ∧
    fisher [rowS, rowD] eP eP * fisher [rowS, rowD] eG eG -
      fisher [rowS, rowD] eP eG * fisher [rowS, rowD] eP eG = 0 := by
  decide

/-- **The anchored system.**  With the anchor row `(α, β, 0)` the level block is
`[[4 + α², 4 + αβ], [4 + αβ, 4 + β²]]`. -/
theorem fisher_anchored (α β : Int) :
    fisher [rowS, rowD, (α, β, 0)] eP eP = 4 + α * α ∧
    fisher [rowS, rowD, (α, β, 0)] eP eG = 4 + α * β ∧
    fisher [rowS, rowD, (α, β, 0)] eG eG = 4 + β * β := by
  have sP : dot3 rowS eP = 2 := by decide
  have sG : dot3 rowS eG = 2 := by decide
  have dP : dot3 rowD eP = 0 := by decide
  have dG : dot3 rowD eG = 0 := by decide
  have aP : dot3 (α, β, 0) eP = α := by
    show α * 1 + β * 0 + 0 * 0 = α
    omega
  have aG : dot3 (α, β, 0) eG = β := by
    show α * 0 + β * 1 + 0 * 0 = β
    omega
  refine ⟨?_, ?_, ?_⟩
  · show dot3 rowS eP * dot3 rowS eP +
        (dot3 rowD eP * dot3 rowD eP + (dot3 (α, β, 0) eP * dot3 (α, β, 0) eP + 0)) = 4 + α * α
    rw [sP, dP, aP]
    omega
  · show dot3 rowS eP * dot3 rowS eG +
        (dot3 rowD eP * dot3 rowD eG + (dot3 (α, β, 0) eP * dot3 (α, β, 0) eG + 0)) = 4 + α * β
    rw [sP, sG, dP, dG, aP, aG]
    omega
  · show dot3 rowS eG * dot3 rowS eG +
        (dot3 rowD eG * dot3 rowD eG + (dot3 (α, β, 0) eG * dot3 (α, β, 0) eG + 0)) = 4 + β * β
    rw [sG, dG, aG]
    omega

/-- **Consilience of the kernel and the Fisher determinant.**  The determinant of the anchored
level block is `4 (α − β)²`, which vanishes exactly when the anchor fails. -/
theorem fisher_anchored_det (α β : Int) :
    (4 + α * α) * (4 + β * β) - (4 + α * β) * (4 + α * β) = 4 * ((α - β) * (α - β)) ∧
    (4 * ((α - β) * (α - β)) = 0 ↔ α = β) ∧
    (IsValidFor (levelAnchor α β) (fun p : Int × Int => p) ↔ α ≠ β) :=
  ⟨fisher_block_det 4 α β, fisher_singular_iff α β, anchor_valid_iff α β⟩

/-! ## §8 Tests on the difference channel -/

/-- The law of the observed difference: the weight of the deviation of the observation `y`
from the mean `2d`, for a noise weight function `noise`. -/
def lawD (noise : Int → Nat) (θ : PGD) (y : Int) : Nat := noise (y - obsD θ)

/-- **One law for `4 am` and `400 nm`.**  The hypotheses `P + g = 4 am` and `P + g = 400 nm`,
with the same `d`, give the difference channel the same law. -/
theorem d_channel_same_law (noise : Int → Nat) (d y : Int) :
    lawD noise ⟨4 * am, 0, d⟩ y = lawD noise ⟨400 * nm, 0, d⟩ y := by
  show noise (y - obsD ⟨4 * am, 0, d⟩) = noise (y - obsD ⟨400 * nm, 0, d⟩)
  rw [obsD_level_free, obsD_level_free]

/-- The two hypotheses differ in level by the factor `10¹¹`; `D` merges them and `S`
separates them. -/
theorem d_channel_hypotheses_differ :
    400 * nm = 100000000000 * (4 * am) ∧ obsD ⟨4 * am, 0, 0⟩ = obsD ⟨400 * nm, 0, 0⟩ ∧
    obsS ⟨4 * am, 0, 0⟩ ≠ obsS ⟨400 * nm, 0, 0⟩ := by
  decide

/-- The absolute difference of two weights. -/
def absDiff (a b : Nat) : Nat := (a - b) + (b - a)

/-- Twice the total variation of two weight functions over a finite list of outcomes. -/
def tvNum (p q : Int → Nat) : List Int → Nat
  | [] => 0
  | y :: ys => absDiff (p y) (q y) + tvNum p q ys

/-- Pointwise equal weights have total variation `0`. -/
theorem tvNum_of_pointwise (p q : Int → Nat) (h : ∀ y, p y = q y) :
    ∀ ys : List Int, tvNum p q ys = 0
  | [] => rfl
  | y :: ys => by
    have h1 : tvNum p q ys = 0 := tvNum_of_pointwise p q h ys
    have h2 : p y = q y := h y
    show (p y - q y) + (q y - p y) + tvNum p q ys = 0
    omega

/-- The weight that a test `φ` accepts. -/
def acceptMass (φ : Int → Bool) (p : Int → Nat) : List Int → Nat
  | [] => 0
  | y :: ys => (if φ y = true then p y else 0) + acceptMass φ p ys

/-- Pointwise equal weights are accepted with equal weight by every test. -/
theorem acceptMass_congr (φ : Int → Bool) (p q : Int → Nat) (h : ∀ y, p y = q y) :
    ∀ ys : List Int, acceptMass φ p ys = acceptMass φ q ys
  | [] => rfl
  | y :: ys => by
    show (if φ y = true then p y else 0) + acceptMass φ p ys =
      (if φ y = true then q y else 0) + acceptMass φ q ys
    rw [h y, acceptMass_congr φ p q h ys]

/-- **No test on `D` separates `4 am` from `400 nm`.**  Total variation `0`, equal acceptance by
every test, and posterior odds equal to prior odds for every pair of prior weights. -/
theorem d_channel_tests_blind (noise : Int → Nat) (d : Int) (ys : List Int)
    (φ : Int → Bool) (y πA πB : Int) :
    tvNum (lawD noise ⟨4 * am, 0, d⟩) (lawD noise ⟨400 * nm, 0, d⟩) ys = 0 ∧
    acceptMass φ (lawD noise ⟨4 * am, 0, d⟩) ys = acceptMass φ (lawD noise ⟨400 * nm, 0, d⟩) ys ∧
    SameRatio (πA * (lawD noise ⟨4 * am, 0, d⟩ y : Int))
      (πB * (lawD noise ⟨400 * nm, 0, d⟩ y : Int)) πA πB := by
  refine ⟨tvNum_of_pointwise _ _ (d_channel_same_law noise d) ys,
    acceptMass_congr φ _ _ (d_channel_same_law noise d) ys, ?_⟩
  rw [← d_channel_same_law noise d y]
  exact posterior_odds_frozen πA πB _

/-! ## §9 The Bayesian update -/

/-- A finite sum `Σ_{d ∈ ds} f d`. -/
def massOver (f : Int → Nat) : List Int → Nat
  | [] => 0
  | d :: ds => f d + massOver f ds

theorem massOver_mul (c : Nat) (f : Int → Nat) :
    ∀ ds : List Int, massOver (fun d => c * f d) ds = c * massOver f ds
  | [] => (Nat.mul_zero c).symm
  | d :: ds => by
    show c * f d + massOver (fun d => c * f d) ds = c * (f d + massOver f ds)
    rw [massOver_mul c f ds, Nat.mul_add]

/-- Unnormalised posterior mass of the level pair `p = (P, g)`: prior `πPG` on the level pair,
prior `πd` on `d`, and a likelihood `lik y d` of the observation `y` that reads `d` alone. -/
def postPG (πPG : Int × Int → Nat) (πd : Int → Nat) (lik : Int → Int → Nat) (y : Int)
    (ds : List Int) (p : Int × Int) : Nat :=
  massOver (fun d => πPG p * (πd d * lik y d)) ds

/-- The posterior mass of a level pair is its prior mass times a constant. -/
theorem postPG_factor (πPG : Int × Int → Nat) (πd : Int → Nat) (lik : Int → Int → Nat)
    (y : Int) (ds : List Int) (p : Int × Int) :
    postPG πPG πd lik y ds p = πPG p * massOver (fun d => πd d * lik y d) ds :=
  massOver_mul (πPG p) (fun d => πd d * lik y d) ds

/-- **Posterior odds equal prior odds.**  For a likelihood that reads `d` alone and a factorised
prior, the posterior odds of any two level pairs `(P, g)` equal their prior odds, for every
observation and every finite range of `d`: the data do not update the common level. -/
theorem level_posterior_odds_frozen (πPG : Int × Int → Nat) (πd : Int → Nat)
    (lik : Int → Int → Nat) (y : Int) (ds : List Int) (p q : Int × Int) :
    postPG πPG πd lik y ds p * πPG q = postPG πPG πd lik y ds q * πPG p := by
  rw [postPG_factor, postPG_factor, Nat.mul_right_comm (πPG p), Nat.mul_right_comm (πPG q),
    Nat.mul_comm (πPG p) (πPG q)]

/-- A prior on `(P, d)` that ties `P` to `d`. -/
def priorTied (P d : Int) : Nat := if P = d then 1 else 0

/-- The flat prior on `(P, d)`. -/
def priorFlat (_P _d : Int) : Nat := 1

/-- A likelihood that reads `d` alone and selects `d = 1`. -/
def likD (d : Int) : Nat := if d = 1 then 1 else 0

/-- Posterior mass of the value `P` over `d ∈ {0, 1}`. -/
def postMassP (prior : Int → Int → Nat) (P : Int) : Nat :=
  massOver (fun d => prior P d * likD d) [0, 1]

/-- Total posterior mass over `P ∈ {0, 1}`. -/
def postMassAll (prior : Int → Int → Nat) : Nat := postMassP prior 0 + postMassP prior 1

/-- Prior mass of the value `P` over `d ∈ {0, 1}`. -/
def priorMassP (prior : Int → Int → Nat) (P : Int) : Nat := massOver (fun d => prior P d) [0, 1]

/-- Total prior mass over `P ∈ {0, 1}`. -/
def priorMassAll (prior : Int → Int → Nat) : Nat := priorMassP prior 0 + priorMassP prior 1

/-- **Prior coupling, not data.**  The likelihood never contains `P`.  Under the tied prior the
posterior gives `P = 1` probability `1` from the prior probability `1/2`; under the flat prior the
posterior probability of `P = 1` is its prior probability `1/2`.  A narrow posterior on `P` is
here produced by the prior alone. -/
theorem prior_coupling_moves_blind_coordinate :
    postMassP priorTied 1 = postMassAll priorTied ∧ 0 < postMassAll priorTied ∧
    2 * priorMassP priorTied 1 = priorMassAll priorTied ∧
    2 * postMassP priorFlat 1 = postMassAll priorFlat ∧
    2 * priorMassP priorFlat 1 = priorMassAll priorFlat := by
  decide

/-- The two prior configurations. -/
def priorOf : Bool → Int → Int → Nat
  | true => priorTied
  | false => priorFlat

/-- The Kolmogorov–Smirnov flag at `P = 0`: the posterior probability of `P = 0` differs from its
prior probability, in cross-multiplied form. -/
def ksFlag (b : Bool) : Bool :=
  decide (postMassP (priorOf b) 0 * priorMassAll (priorOf b) ≠
    priorMassP (priorOf b) 0 * postMassAll (priorOf b))

/-- **The KS deviation from the prior is not a function of the likelihood.**  Both configurations
have the same likelihood, which does not contain `P`; the deviation of the posterior of `P` from
its prior is present in one and absent in the other. -/
theorem ks_flag_not_function_of_likelihood : IsInvalidFor (fun _ : Bool => likD) ksFlag :=
  ⟨true, false, rfl, by decide⟩

/-- Joint posterior weight of `(P, g)`: flat prior on `P`, prior `πg` on the calibration offset
`g`, likelihood `L` of the reconstructed level `P + g`. -/
def jointW (πg : Int → Nat) (L : Int → Nat) (P g : Int) : Nat := πg g * L (P + g)

/-- The likelihood of the level is constant on the line `(P + c, g − c)`. -/
theorem likelihood_constant_on_fibre (L : Int → Nat) (P g c : Int) :
    L (P + c + (g - c)) = L (P + g) := by
  have h : P + c + (g - c) = P + g := by omega
  rw [h]

/-- **Calibration-prior transport.**  A calibration prior displaced by `c` gives, at every point,
the joint posterior weight of the original prior at the point moved by `(c, −c)`: the posterior
of the source value is displaced by `−c`, with the same likelihood. -/
theorem calibration_prior_transport (πg L : Int → Nat) (c P g : Int) :
    jointW (fun t => πg (t - c)) L P g = jointW πg L (P + c) (g - c) := by
  show πg (g - c) * L (P + g) = πg (g - c) * L (P + c + (g - c))
  rw [likelihood_constant_on_fibre L P g c]

/-- The point mass at `x`. -/
def deltaAt (x t : Int) : Nat := if t = x then 1 else 0

/-- **At the Hanford resultant.**  With the data selecting the level `R⋆`, the calibration prior
at `0` puts the posterior of `P` at `R⋆`; the calibration prior at `100 am` puts it at
`R⋆ − 100 am` and removes it from `R⋆`. -/
theorem hanford_transport :
    jointW (deltaAt 0) (deltaAt rStar) rStar 0 = 1 ∧
    jointW (fun t => deltaAt 0 (t - 100 * am)) (deltaAt rStar) (rStar - 100 * am) (100 * am) = 1 ∧
    jointW (fun t => deltaAt 0 (t - 100 * am)) (deltaAt rStar) rStar 0 = 0 := by
  decide

/-! ## §10 Common error and apparent precision -/

/-- With `X₁ = P + g + e₁` and `X₂ = P + g + e₂`: `D = e₁ − e₂` contains no `g`, and
`S − 2P = 2g + e₁ + e₂`. -/
theorem difference_blind_to_common_error (P g e₁ e₂ : Int) :
    difC (P + g + e₁, P + g + e₂) = e₁ - e₂ ∧
    sumC (P + g + e₁, P + g + e₂) - 2 * P = 2 * g + e₁ + e₂ := by
  show P + g + e₁ - (P + g + e₂) = e₁ - e₂ ∧
    P + g + e₁ + (P + g + e₂) - 2 * P = 2 * g + e₁ + e₂
  constructor <;> omega

/-- Eight equally weighted samples `(g, e₁, e₂)`: the common error `g = ±t` and independent
errors `e₁, e₂ = ±1`. -/
def samples (t : Int) : List (Int × Int × Int) :=
  [(t, 1, 1), (t, 1, -1), (t, -1, 1), (t, -1, -1),
   (-t, 1, 1), (-t, 1, -1), (-t, -1, 1), (-t, -1, -1)]

/-- First moment of `D = e₁ − e₂`. -/
def momD1 : List (Int × Int × Int) → Int
  | [] => 0
  | s :: ss => (s.2.1 - s.2.2) + momD1 ss

/-- Second moment of `D`. -/
def momD2 : List (Int × Int × Int) → Int
  | [] => 0
  | s :: ss => (s.2.1 - s.2.2) * (s.2.1 - s.2.2) + momD2 ss

/-- First moment of `2(R⋆ − P) = 2g + e₁ + e₂`. -/
def momR1 : List (Int × Int × Int) → Int
  | [] => 0
  | s :: ss => (2 * s.1 + s.2.1 + s.2.2) + momR1 ss

/-- Second moment of `2(R⋆ − P)`. -/
def momR2 : List (Int × Int × Int) → Int
  | [] => 0
  | s :: ss => (2 * s.1 + s.2.1 + s.2.2) * (2 * s.1 + s.2.1 + s.2.2) + momR2 ss

/-- **Agreement as tight as the noise, common error unbounded.**  For every common spread
`τ = t ∈ {0, …, 100}`, over the eight samples: `Σ D = 0` and `Σ D² = 16`, so `Var D = 2 = 2σ²`
with `σ² = 1`, for every `τ`; `Σ 2(R⋆ − P) = 0` and `Σ (2(R⋆ − P))² = 32 t² + 16`, so
`Var (R⋆ − P) = t² + 1/2 = τ² + σ²/2`. -/
theorem common_error_variance_family :
    ∀ t ∈ List.range 101,
      momD1 (samples (Int.ofNat t)) = 0 ∧ momD2 (samples (Int.ofNat t)) = 16 ∧
      momR1 (samples (Int.ofNat t)) = 0 ∧
      momR2 (samples (Int.ofNat t)) = 32 * (Int.ofNat t * Int.ofNat t) + 16 := by
  decide

/-! ## §11 Any number of channels -/

/-- **Many channels.**  For `N ≥ 1` channels, every statistic of any list of pairwise
differences is invalid for the summed error: two hundred thousand mutually agreeing channels
see the orthogonal complement of the common direction and nothing of the common direction. -/
theorem many_channels_blind (N : Nat) (hN : 0 < N) {β : Sort u} (S : List Int → β)
    (l : List (Nat × Nat)) :
    IsInvalidFor (fun ε : Nat → Int => S (diffs ε l)) (fun ε => sumTo N ε) :=
  pairwise_invalid_for_common_mode_list N hN S l

/-- The case of `200000` channels. -/
theorem two_hundred_thousand_channels_blind {β : Sort u} (S : List Int → β)
    (l : List (Nat × Nat)) :
    IsInvalidFor (fun ε : Nat → Int => S (diffs ε l)) (fun ε => sumTo 200000 ε) :=
  many_channels_blind 200000 (by decide) S l

/-! ## §12 The null-space audit of a validation suite

Every validation or calibration observable is a row `r` of a measurement matrix `M` acting on the
latent coordinates `θ = (P, g_cal, g_time, g_act, g_sens, d)`.  A direction `v` with `M v = 0` is
a deformation invisible to the whole suite.  The suite is invalid for a target `T` as soon as `T`
moves along one such direction, and for a linear target this is also necessary. -/

/-- Latent coordinates: the source value `P`, four shared offsets and a differential term `d`. -/
structure Latent where
  P : Int
  gCal : Int
  gTime : Int
  gAct : Int
  gSens : Int
  d : Int

/-- A validation observable: one row of integer coefficients. -/
structure Row where
  cP : Int
  cCal : Int
  cTime : Int
  cAct : Int
  cSens : Int
  cD : Int

/-- The reading of a row. -/
def ev (r : Row) (θ : Latent) : Int :=
  r.cP * θ.P + r.cCal * θ.gCal + r.cTime * θ.gTime + r.cAct * θ.gAct + r.cSens * θ.gSens +
    r.cD * θ.d

/-- Coordinatewise sum. -/
def addL (θ v : Latent) : Latent :=
  ⟨θ.P + v.P, θ.gCal + v.gCal, θ.gTime + v.gTime, θ.gAct + v.gAct, θ.gSens + v.gSens, θ.d + v.d⟩

/-- Coordinatewise difference. -/
def subL (θ v : Latent) : Latent :=
  ⟨θ.P - v.P, θ.gCal - v.gCal, θ.gTime - v.gTime, θ.gAct - v.gAct, θ.gSens - v.gSens, θ.d - v.d⟩

/-- The zero state. -/
def zeroL : Latent := ⟨0, 0, 0, 0, 0, 0⟩

/-- The readings of a suite of rows. -/
def measureSuite (suite : List Row) (θ : Latent) : List Int := suite.map (fun r => ev r θ)

/-- `v` lies in the kernel of every row of the suite. -/
abbrev InKernel (suite : List Row) (v : Latent) : Prop := ∀ r ∈ suite, ev r v = 0

theorem ev_add (r : Row) (θ v : Latent) : ev r (addL θ v) = ev r θ + ev r v := by
  show r.cP * (θ.P + v.P) + r.cCal * (θ.gCal + v.gCal) + r.cTime * (θ.gTime + v.gTime) +
      r.cAct * (θ.gAct + v.gAct) + r.cSens * (θ.gSens + v.gSens) + r.cD * (θ.d + v.d) =
    r.cP * θ.P + r.cCal * θ.gCal + r.cTime * θ.gTime + r.cAct * θ.gAct + r.cSens * θ.gSens +
        r.cD * θ.d +
      (r.cP * v.P + r.cCal * v.gCal + r.cTime * v.gTime + r.cAct * v.gAct + r.cSens * v.gSens +
        r.cD * v.d)
  simp only [Int.mul_add]
  omega

theorem ev_sub (r : Row) (θ v : Latent) : ev r (subL θ v) = ev r θ - ev r v := by
  show r.cP * (θ.P - v.P) + r.cCal * (θ.gCal - v.gCal) + r.cTime * (θ.gTime - v.gTime) +
      r.cAct * (θ.gAct - v.gAct) + r.cSens * (θ.gSens - v.gSens) + r.cD * (θ.d - v.d) =
    r.cP * θ.P + r.cCal * θ.gCal + r.cTime * θ.gTime + r.cAct * θ.gAct + r.cSens * θ.gSens +
        r.cD * θ.d -
      (r.cP * v.P + r.cCal * v.gCal + r.cTime * v.gTime + r.cAct * v.gAct + r.cSens * v.gSens +
        r.cD * v.d)
  simp only [Int.mul_sub]
  omega

theorem ev_zero (r : Row) : ev r zeroL = 0 := by
  show r.cP * 0 + r.cCal * 0 + r.cTime * 0 + r.cAct * 0 + r.cSens * 0 + r.cD * 0 = 0
  omega

/-- Maps that agree on the members of a list agree on the list. -/
theorem map_congr_mem {α β : Type} (f g : α → β) :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.map f = l.map g
  | [], _ => rfl
  | a :: l, h =>
    cons_congr (h a (List.Mem.head _))
      (map_congr_mem f g l (fun b hb => h b (List.Mem.tail _ hb)))

/-- Maps that agree on a list agree on its members. -/
theorem eq_of_map_eq_mem {α β : Type} (f g : α → β) :
    ∀ l : List α, l.map f = l.map g → ∀ a ∈ l, f a = g a
  | [], _, _, ha => nomatch ha
  | b :: l, h, a, ha => by
    have hh : f b = g b ∧ l.map f = l.map g := List.cons.inj h
    cases ha with
    | head => exact hh.1
    | tail _ ha' => exact eq_of_map_eq_mem f g l hh.2 a ha'

/-- A kernel direction does not change the readings of the suite. -/
theorem measure_shift (suite : List Row) (θ v : Latent) (hv : InKernel suite v) :
    measureSuite suite (addL θ v) = measureSuite suite θ :=
  map_congr_mem (fun r => ev r (addL θ v)) (fun r => ev r θ) suite
    (fun r hr => (ev_add r θ v).trans (by rw [hv r hr, Int.add_zero]))

/-- **The null-space audit.**  If `v ∈ ker M` and the target moves along `v`, the suite is
invalid for the target. -/
theorem audit_invalid {γ : Sort u} (suite : List Row) (T : Latent → γ) (θ v : Latent)
    (hv : InKernel suite v) (hT : T (addL θ v) ≠ T θ) : IsInvalidFor (measureSuite suite) T :=
  ⟨addL θ v, θ, measure_shift suite θ v hv, hT⟩

/-- **Exactness of the audit.**  A suite determines the linear target `t` exactly when every
direction of its kernel lies in the kernel of `t`: `ker M ⊆ ker t`. -/
theorem audit_exact (suite : List Row) (t : Row) :
    IsValidFor (measureSuite suite) (ev t) ↔ ∀ v, InKernel suite v → ev t v = 0 := by
  constructor
  · intro hval v hv
    have h1 : measureSuite suite v = measureSuite suite zeroL :=
      map_congr_mem (fun r => ev r v) (fun r => ev r zeroL) suite
        (fun r hr => (hv r hr).trans (ev_zero r).symm)
    have h2 : ev t v = ev t zeroL := hval v zeroL h1
    rw [h2]
    exact ev_zero t
  · intro hker θ θ' h
    have hrow : ∀ r ∈ suite, ev r θ = ev r θ' :=
      eq_of_map_eq_mem (fun r => ev r θ) (fun r => ev r θ') suite h
    have hv : InKernel suite (subL θ θ') := by
      intro r hr
      rw [ev_sub, hrow r hr, Int.sub_self]
    have h0 : ev t (subL θ θ') = 0 := hker (subL θ θ') hv
    rw [ev_sub] at h0
    show ev t θ = ev t θ'
    omega

/-- Rows that vanish on a kernel direction leave it in the kernel of the enlarged suite. -/
theorem kernel_extend (suite extra : List Row) (v : Latent) (h₁ : InKernel suite v)
    (h₂ : InKernel extra v) : InKernel (suite ++ extra) v := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · exact h₁ r h
  · exact h₂ r h

/-- **No repair by repetition.**  A suite whose rows all occur in an invalid suite is invalid:
repeating, reordering or duplicating the same observables adds no information. -/
theorem redundant_rows_no_repair {γ : Sort u} (suite₁ suite₂ : List Row) (T : Latent → γ)
    (hsub : ∀ r ∈ suite₂, r ∈ suite₁) :
    IsInvalidFor (measureSuite suite₁) T → IsInvalidFor (measureSuite suite₂) T :=
  no_repair (measureSuite suite₁) (measureSuite suite₂) T (fun θ θ' h =>
    map_congr_mem (fun r => ev r θ) (fun r => ev r θ') suite₂
      (fun r hr => eq_of_map_eq_mem (fun r => ev r θ) (fun r => ev r θ') suite₁ h r (hsub r hr)))

/-- Every member of `List.replicate n a` is `a`. -/
theorem mem_replicate_eq (r a : Row) : ∀ n : Nat, r ∈ List.replicate n a → r = a
  | 0, h => by
    have h' : r ∈ ([] : List Row) := h
    cases h'
  | n + 1, h => by
    have h' : r ∈ a :: List.replicate n a := h
    cases h' with
    | head => rfl
    | tail _ h'' => exact mem_replicate_eq r a n h''

/-! ### A six-coordinate validation architecture -/

/-- The difference channel `X₁ − X₂ = 2d`. -/
def rowDiff : Row := ⟨0, 0, 0, 0, 0, 2⟩

/-- The sum channel `X₁ + X₂ = 2(P + g_cal + g_time + g_act + g_sens)`. -/
def rowSum : Row := ⟨2, 2, 2, 2, 2, 0⟩

/-- The source value `P`, the target. -/
def rowP : Row := ⟨1, 0, 0, 0, 0, 0⟩

/-- Anchors that read one shared offset each. -/
def anchorCal : Row := ⟨0, 1, 0, 0, 0, 0⟩
def anchorTime : Row := ⟨0, 0, 1, 0, 0, 0⟩
def anchorAct : Row := ⟨0, 0, 0, 1, 0, 0⟩
def anchorSens : Row := ⟨0, 0, 0, 0, 1, 0⟩

/-- Agreement alone. -/
def agreementSuite : List Row := [rowDiff]

/-- Agreement and level. -/
def levelSuite : List Row := [rowDiff, rowSum]

/-- Agreement, level and one anchor per shared offset. -/
def anchoredSuite : List Row := [rowDiff, rowSum, anchorCal, anchorTime, anchorAct, anchorSens]

/-- Kernel directions: `P` alone; `P` up with one shared offset down. -/
def vP : Latent := ⟨1, 0, 0, 0, 0, 0⟩
def vCal : Latent := ⟨1, -1, 0, 0, 0, 0⟩
def vTime : Latent := ⟨1, 0, -1, 0, 0, 0⟩
def vAct : Latent := ⟨1, 0, 0, -1, 0, 0⟩
def vSens : Latent := ⟨1, 0, 0, 0, -1, 0⟩

/-- **Agreement alone.**  The difference channel is invalid for the source value and for every
shared offset. -/
theorem agreement_suite_invalid :
    IsInvalidFor (measureSuite agreementSuite) (ev rowP) ∧
    IsInvalidFor (measureSuite agreementSuite) (ev anchorCal) ∧
    IsInvalidFor (measureSuite agreementSuite) (ev anchorTime) ∧
    IsInvalidFor (measureSuite agreementSuite) (ev anchorAct) ∧
    IsInvalidFor (measureSuite agreementSuite) (ev anchorSens) :=
  ⟨audit_invalid agreementSuite (ev rowP) zeroL vP (by decide) (by decide),
   audit_invalid agreementSuite (ev anchorCal) zeroL vCal (by decide) (by decide),
   audit_invalid agreementSuite (ev anchorTime) zeroL vTime (by decide) (by decide),
   audit_invalid agreementSuite (ev anchorAct) zeroL vAct (by decide) (by decide),
   audit_invalid agreementSuite (ev anchorSens) zeroL vSens (by decide) (by decide)⟩

/-- **Agreement and level.**  Adding the sum channel leaves four kernel directions, one per shared
offset; the suite is invalid for the source value and for every shared offset. -/
theorem level_suite_invalid :
    IsInvalidFor (measureSuite levelSuite) (ev rowP) ∧
    IsInvalidFor (measureSuite levelSuite) (ev anchorCal) ∧
    IsInvalidFor (measureSuite levelSuite) (ev anchorTime) ∧
    IsInvalidFor (measureSuite levelSuite) (ev anchorAct) ∧
    IsInvalidFor (measureSuite levelSuite) (ev anchorSens) :=
  ⟨audit_invalid levelSuite (ev rowP) zeroL vCal (by decide) (by decide),
   audit_invalid levelSuite (ev anchorCal) zeroL vCal (by decide) (by decide),
   audit_invalid levelSuite (ev anchorTime) zeroL vTime (by decide) (by decide),
   audit_invalid levelSuite (ev anchorAct) zeroL vAct (by decide) (by decide),
   audit_invalid levelSuite (ev anchorSens) zeroL vSens (by decide) (by decide)⟩

/-- **The anchored suite determines the source value.** -/
theorem anchored_suite_valid_for_P : IsValidFor (measureSuite anchoredSuite) (ev rowP) := by
  apply (audit_exact anchoredSuite rowP).mpr
  intro v hv
  have hS : ev rowSum v = 0 := hv rowSum (.tail _ (.head _))
  have hC : ev anchorCal v = 0 := hv anchorCal (.tail _ (.tail _ (.head _)))
  have hT : ev anchorTime v = 0 := hv anchorTime (.tail _ (.tail _ (.tail _ (.head _))))
  have hA : ev anchorAct v = 0 := hv anchorAct (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  have hN : ev anchorSens v = 0 :=
    hv anchorSens (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have hS' : 2 * v.P + 2 * v.gCal + 2 * v.gTime + 2 * v.gAct + 2 * v.gSens + 0 * v.d = 0 := hS
  have hC' : 0 * v.P + 1 * v.gCal + 0 * v.gTime + 0 * v.gAct + 0 * v.gSens + 0 * v.d = 0 := hC
  have hT' : 0 * v.P + 0 * v.gCal + 1 * v.gTime + 0 * v.gAct + 0 * v.gSens + 0 * v.d = 0 := hT
  have hA' : 0 * v.P + 0 * v.gCal + 0 * v.gTime + 1 * v.gAct + 0 * v.gSens + 0 * v.d = 0 := hA
  have hN' : 0 * v.P + 0 * v.gCal + 0 * v.gTime + 0 * v.gAct + 1 * v.gSens + 0 * v.d = 0 := hN
  show 1 * v.P + 0 * v.gCal + 0 * v.gTime + 0 * v.gAct + 0 * v.gSens + 0 * v.d = 0
  omega

/-- **Each anchor is necessary.**  Removing any one anchor reopens the kernel direction of its
shared offset, and the suite is invalid for the source value. -/
theorem each_anchor_necessary :
    IsInvalidFor (measureSuite [rowDiff, rowSum, anchorTime, anchorAct, anchorSens]) (ev rowP) ∧
    IsInvalidFor (measureSuite [rowDiff, rowSum, anchorCal, anchorAct, anchorSens]) (ev rowP) ∧
    IsInvalidFor (measureSuite [rowDiff, rowSum, anchorCal, anchorTime, anchorSens]) (ev rowP) ∧
    IsInvalidFor (measureSuite [rowDiff, rowSum, anchorCal, anchorTime, anchorAct]) (ev rowP) :=
  ⟨audit_invalid _ (ev rowP) zeroL vCal (by decide) (by decide),
   audit_invalid _ (ev rowP) zeroL vTime (by decide) (by decide),
   audit_invalid _ (ev rowP) zeroL vAct (by decide) (by decide),
   audit_invalid _ (ev rowP) zeroL vSens (by decide) (by decide)⟩

/-- **Repetition of agreement.**  Any number of copies of the difference channel is invalid for
the source value. -/
theorem repeated_agreement_invalid (n : Nat) :
    IsInvalidFor (measureSuite (List.replicate n rowDiff)) (ev rowP) :=
  redundant_rows_no_repair agreementSuite (List.replicate n rowDiff) (ev rowP)
    (fun r hr => by
      have he : r = rowDiff := mem_replicate_eq r rowDiff n hr
      subst he
      exact List.Mem.head _)
    agreement_suite_invalid.1

/-- **At the Hanford resultant.**  The truth `P = R⋆` with no shared offset and the truth
`R⋆ − 100 am` with a calibration offset of `100 am`, or `R⋆ − 396.9 nm` with a calibration offset
of `396.9 nm`, give the agreement-and-level suite the same readings. -/
theorem hanford_suite_witness :
    measureSuite levelSuite ⟨rStar, 0, 0, 0, 0, 0⟩ = [0, 7938490295413130] ∧
    measureSuite levelSuite ⟨rStar, 0, 0, 0, 0, 0⟩ =
      measureSuite levelSuite ⟨rStar - 100 * am, 100 * am, 0, 0, 0, 0⟩ ∧
    measureSuite levelSuite ⟨rStar, 0, 0, 0, 0, 0⟩ =
      measureSuite levelSuite ⟨rStar - rStarBig, rStarBig, 0, 0, 0, 0⟩ ∧
    ev rowP ⟨rStar, 0, 0, 0, 0, 0⟩ ≠ ev rowP ⟨rStar - 100 * am, 100 * am, 0, 0, 0, 0⟩ := by
  decide

/-! ## §13 Two-sided statistics -/

/-- The two-sided reading of a statistic: any function of `|z|`. -/
def twoSided {β : Sort u} (f : Nat → β) (z : Int) : β := f z.natAbs

/-- The direction of a statistic: `1`, `−1` or `0`. -/
def direction (z : Int) : Int := if 0 < z then 1 else if z < 0 then -1 else 0

/-- **Direction.**  Every two-sided reading is invalid for the direction: `z = 2` and `z = −2`. -/
theorem twoSided_invalid_for_direction {β : Sort u} (f : Nat → β) :
    IsInvalidFor (twoSided f) direction := by
  refine ⟨2, -2, ?_, by decide⟩
  show f (Int.natAbs 2) = f (Int.natAbs (-2))
  exact congrArg f (by decide)

/-- The significance flag `p ≤ α`. -/
def significant (α p : Nat) : Bool := decide (p ≤ α)

/-- **Thresholds repair nothing.**  The significance flag of a two-sided p-value is invalid for
the direction. -/
theorem threshold_no_repair (f : Nat → Nat) (α : Nat) :
    IsInvalidFor (fun z => significant α (twoSided f z)) direction :=
  invalid_postcompose (twoSided f) (significant α) direction (twoSided_invalid_for_direction f)

/-- The z-statistic `δ / SE`, in a unit in which the standard error divides the effect. -/
def zStat (p : Int × Int) : Int := p.1 / p.2

/-- The effect size `|δ|`. -/
def effectSize (p : Int × Int) : Nat := p.1.natAbs

/-- **Effect size.**  In the unit `0.005`, `(δ, SE) = (1, 0.5)` is `(200, 100)` and
`(0.01, 0.005)` is `(2, 1)`: both have `z = 2`, the ratios agree cross-multiplied, and the
effects differ by the factor `100`. -/
theorem zstat_invalid_for_effect :
    IsInvalidFor zStat effectSize ∧ SameRatio 200 100 2 1 ∧
    effectSize (200, 100) = 100 * effectSize (2, 1) :=
  ⟨⟨(200, 100), (2, 1), by decide, by decide⟩, (by decide : (200 : Int) * 1 = 2 * 100),
    by decide⟩

/-- The statistic `χ² = v₁² + v₂²` of two standardised cells. -/
def chi2 (v : Int × Int) : Int := v.1 * v.1 + v.2 * v.2

/-- `(−x)(−x) = x x`. -/
theorem neg_sq (x : Int) : -x * -x = x * x := by
  first
  | exact Int.neg_mul_neg x x
  | rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]

/-- **Cell pattern.**  `χ²` is invalid for the pattern of the cells: `(1, −1)` and `(−1, 1)`. -/
theorem chi2_invalid_for_pattern : IsInvalidFor chi2 (fun v : Int × Int => v) :=
  ⟨(1, -1), (-1, 1), by decide, by decide⟩

/-- The signed permutations of the two cells act inside every fibre of `χ²`. -/
theorem chi2_symmetries (a b : Int) :
    chi2 (b, a) = chi2 (a, b) ∧ chi2 (-a, b) = chi2 (a, b) ∧ chi2 (a, -b) = chi2 (a, b) := by
  refine ⟨?_, ?_, ?_⟩
  · show b * b + a * a = a * a + b * b
    exact Int.add_comm (b * b) (a * a)
  · show -a * -a + b * b = a * a + b * b
    rw [neg_sq a]
  · show a * a + -b * -b = a * a + b * b
    rw [neg_sq b]

/-- The Kolmogorov–Smirnov statistic of a list of differences of two cumulative distributions:
the largest absolute difference. -/
def ksSup : List Int → Nat
  | [] => 0
  | x :: xs => max x.natAbs (ksSup xs)

/-- `|−x| = |x|`. -/
theorem natAbs_neg_eq (x : Int) : (-x).natAbs = x.natAbs := by
  cases x with
  | ofNat n => cases n <;> rfl
  | negSucc m => rfl

/-- **The KS supremum is sign-blind.**  Reversing every difference leaves it unchanged. -/
theorem ksSup_neg : ∀ xs : List Int, ksSup (xs.map (fun x => -x)) = ksSup xs
  | [] => rfl
  | x :: xs => by
    show max (-x).natAbs (ksSup (xs.map (fun x => -x))) = max x.natAbs (ksSup xs)
    rw [natAbs_neg_eq x, ksSup_neg xs]

/-- The direction of a list of differences: the sign of its first entry. -/
def leading : List Int → Int
  | [] => 0
  | x :: _ => direction x

/-- **The KS supremum is invalid for the direction of the shift.**  The difference profiles
`(3, 1)` and `(−3, −1)`, a posterior shifted to one side of its prior and to the other side, have
the same KS statistic. -/
theorem ks_invalid_for_direction : IsInvalidFor ksSup leading :=
  ⟨[3, 1], [-3, -1], by decide, by decide⟩

/-- A map constant on a set on which the target varies is not valid for the target. -/
theorem constant_on_varying_set_not_valid {α : Sort u} {β : Sort v} {γ : Sort w}
    (Φ : α → β) (R : α → γ) (S : α → Prop) (c : β) (hc : ∀ x, S x → Φ x = c)
    (x y : α) (hx : S x) (hy : S y) (hR : R x ≠ R y) : ¬ IsValidFor Φ R :=
  fun hv => hR (hv x y ((hc x hx).trans (hc y hy).symm))

/-- **The statistical pipeline.**  Two-sided readings are invalid for direction, thresholds of
them as well, the z-statistic for effect size, `χ²` for the cell pattern, and the KS supremum
for the direction of a shift. -/
theorem statistical_pipeline_invalidations :
    (∀ f : Nat → Nat, IsInvalidFor (twoSided f) direction) ∧
    (∀ (f : Nat → Nat) (α : Nat), IsInvalidFor (fun z => significant α (twoSided f z)) direction) ∧
    IsInvalidFor zStat effectSize ∧
    IsInvalidFor chi2 (fun v : Int × Int => v) ∧
    IsInvalidFor ksSup leading :=
  ⟨fun f => twoSided_invalid_for_direction f, threshold_no_repair, zstat_invalid_for_effect.1,
    chi2_invalid_for_pattern, ks_invalid_for_direction⟩

/-! ## §14 The invalidations of the methodology

Three steps of Abbott et al., Phys. Rev. X 6, 041014 (2016), against the structures above.

* Sec. V uses the difference between two precessing waveform models as the proxy for the
  systematic error, and Sec. I records that multiple models could be wrong in the same way and
  that the absence of observed inconsistencies increases confidence in the models.
* Sec. III marginalises over the calibration uncertainty of the data and states that this
  broadens the posteriors but reduces calibration biases.
* Sec. III assesses whether the data are informative about a source parameter by a
  Kolmogorov–Smirnov test of its posterior against its prior. -/

/-- **The difference proxy carries no common error.**  For two models `X₁ = P + g + d` and
`X₂ = P + g − d` wrong in the same way by `g`: the proxy `D` is invalid for `g` and for `P + g`;
its Fisher form vanishes on `P` and on `g`; for every factorised prior the posterior odds of any two
common levels equal their prior odds; and every statistic of any number of pairwise model
differences is invalid for the common error.  The agreement of the models carries no information
about the error they share. -/
theorem difference_proxy_carries_no_common_error :
    IsInvalidFor obsD PGD.g ∧ IsInvalidFor obsD (fun θ : PGD => θ.P + θ.g) ∧
    fisher [rowD] eP eP = 0 ∧ fisher [rowD] eG eG = 0 ∧
    (∀ (πPG : Int × Int → Nat) (πd : Int → Nat) (lik : Int → Int → Nat) (y : Int)
      (ds : List Int) (p q : Int × Int),
      postPG πPG πd lik y ds p * πPG q = postPG πPG πd lik y ds q * πPG p) ∧
    (∀ (N : Nat), 0 < N → ∀ (S : List Int → List Int) (l : List (Nat × Nat)),
      IsInvalidFor (fun ε : Nat → Int => S (diffs ε l)) (fun ε => sumTo N ε)) :=
  ⟨obsD_invalid_for_g, obsD_invalid_for_level, fisher_difference_channel.1,
    fisher_difference_channel.2.1, level_posterior_odds_frozen,
    fun N hN S l => many_channels_blind N hN S l⟩

/-- **Marginalisation over calibration transports the bias.**  When the calibration offset `g`
enters the likelihood through the reconstructed level `P + g`, the likelihood is constant on the
line `(P + c, g − c)`, and a calibration prior displaced by `c` displaces the posterior of the
source value by `−c` with the same data.  At the Hanford resultant a calibration prior at `100 am`
moves the posterior of `P` from `R⋆` to `R⋆ − 100 am`. -/
theorem calibration_marginalisation_transports_bias :
    (∀ (L : Int → Nat) (P g c : Int), L (P + c + (g - c)) = L (P + g)) ∧
    (∀ (πg L : Int → Nat) (c P g : Int),
      jointW (fun t => πg (t - c)) L P g = jointW πg L (P + c) (g - c)) ∧
    jointW (deltaAt 0) (deltaAt rStar) rStar 0 = 1 ∧
    jointW (fun t => deltaAt 0 (t - 100 * am)) (deltaAt rStar) (rStar - 100 * am) (100 * am) = 1 ∧
    jointW (fun t => deltaAt 0 (t - 100 * am)) (deltaAt rStar) rStar 0 = 0 :=
  ⟨likelihood_constant_on_fibre, calibration_prior_transport, hanford_transport.1,
    hanford_transport.2.1, hanford_transport.2.2⟩

/-- **The KS test does not measure informativeness.**  The deviation of a posterior from its prior
is not a function of the likelihood: a likelihood that does not contain `P` leaves the posterior
of `P` at its prior under one prior and drives it to certainty under another.  The KS supremum
is moreover blind to the direction of the deviation. -/
theorem ks_test_not_informativeness :
    IsInvalidFor (fun _ : Bool => likD) ksFlag ∧
    postMassP priorTied 1 = postMassAll priorTied ∧
    2 * postMassP priorFlat 1 = postMassAll priorFlat ∧
    IsInvalidFor ksSup leading ∧
    (∀ xs : List Int, ksSup (xs.map (fun x => -x)) = ksSup xs) :=
  ⟨ks_flag_not_function_of_likelihood, prior_coupling_moves_blind_coordinate.1,
    prior_coupling_moves_blind_coordinate.2.2.2.1, ks_invalid_for_direction, ksSup_neg⟩

/-! ## Synthesis -/

/-- **The null-space invalidation of the methodology.**

1. `D` is invalid for `S`; no function of `D` bounds `S`; at the Hanford resultant `D` merges
   `3.969 am` with `396.9 nm`.
2. A linear target factors through `D` exactly when its coefficients sum to `0`.
3. `(S, D)` is invalid for the source value `P` and valid for the common level `P + g`; an anchor
   `αP + βg` repairs it exactly when `α ≠ β`, and the Fisher determinant is `4 (α − β)²`.
4. The difference proxy carries no common error, marginalisation over calibration transports a
   calibration bias into the source value, and the KS deviation is not a function of the
   likelihood.
5. A validation suite is invalid for every target that moves along its kernel, and determines a
   linear target exactly when its kernel lies in the kernel of the target; agreement and level
   leave one kernel direction per shared offset, and each anchor is necessary. -/
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
      IsValidFor (measureSuite anchoredSuite) (ev rowP)) :=
  ⟨⟨difC_invalid_for_sum, no_finite_bound, hanford_levels_merged.2.2.1,
     hanford_levels_merged.2.2.2⟩,
   linT_valid_iff,
   ⟨obsSD_invalid_for_P, obsSD_valid_for_level, anchor_valid_iff,
     fun α β => fisher_block_det 4 α β⟩,
   ⟨obsD_invalid_for_g, calibration_prior_transport, ks_flag_not_function_of_likelihood⟩,
   ⟨fun suite T θ v hv hT => audit_invalid suite T θ v hv hT, audit_exact,
     level_suite_invalid.1, anchored_suite_valid_for_P⟩⟩

#print axioms sd_injective
#print axioms sum_anchors_difference
#print axioms hanford_sd
#print axioms hanford_levels_merged
#print axioms tableI_q_common_line
#print axioms projector_squares
#print axioms linT_valid_iff
#print axioms no_bound_from_difference
#print axioms no_finite_bound
#print axioms difference_estimator_unbounded
#print axioms information_hierarchy
#print axioms hanford_confounding
#print axioms anchor_valid_iff
#print axioms anchor_inversion
#print axioms fisher_block_det
#print axioms fisher_singular_iff
#print axioms fisher_null
#print axioms fisher_anchored
#print axioms d_channel_tests_blind
#print axioms level_posterior_odds_frozen
#print axioms prior_coupling_moves_blind_coordinate
#print axioms ks_flag_not_function_of_likelihood
#print axioms calibration_prior_transport
#print axioms hanford_transport
#print axioms common_error_variance_family
#print axioms many_channels_blind
#print axioms audit_invalid
#print axioms audit_exact
#print axioms redundant_rows_no_repair
#print axioms anchored_suite_valid_for_P
#print axioms each_anchor_necessary
#print axioms repeated_agreement_invalid
#print axioms hanford_suite_witness
#print axioms statistical_pipeline_invalidations
#print axioms difference_proxy_carries_no_common_error
#print axioms calibration_marginalisation_transports_bias
#print axioms ks_test_not_informativeness
#print axioms ligo_null_space_invalidation

end LigoNullSpace
