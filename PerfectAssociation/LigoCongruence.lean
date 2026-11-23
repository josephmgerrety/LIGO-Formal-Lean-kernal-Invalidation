/-!
# LIGO congruence: kernels, validity, anchors, and the no-repair theorem
-/
namespace LigoCongruence

universe u v w x y z

/-! ## Layer 0: kernel and validity -/

/-- The kernel relation of `f`: `a` and `b` have the same image. -/
abbrev Ker {α : Sort u} {β : Sort v} (f : α → β) (a b : α) : Prop := f a = f b

/-- `Φ` is valid for the target `R`: every pair identified by `Φ` is identified by `R`. -/
def IsValidFor {α : Sort u} {β : Sort v} {γ : Sort w} (Φ : α → β) (R : α → γ) : Prop :=
  ∀ a b, Ker Φ a b → Ker R a b

/-- `Φ` is invalid for `R`: some pair has equal `Φ`-images and different `R`-images. -/
def IsInvalidFor {α : Sort u} {β : Sort v} {γ : Sort w} (Φ : α → β) (R : α → γ) : Prop :=
  ∃ a b, Ker Φ a b ∧ ¬ Ker R a b

/-- Invalidity contradicts validity. -/
theorem invalid_not_valid {α : Sort u} {β : Sort v} {γ : Sort w}
    (Φ : α → β) (R : α → γ) : IsInvalidFor Φ R → ¬ IsValidFor Φ R :=
  fun ⟨a, b, h₁, h₂⟩ hv => h₂ (hv a b h₁)

/-- With decidable equality on the target, validity is exactly the absence of an invalid pair. -/
theorem valid_iff_not_invalid {α : Sort u} {β : Sort v} {γ : Sort w} [DecidableEq γ]
    (Φ : α → β) (R : α → γ) : IsValidFor Φ R ↔ ¬ IsInvalidFor Φ R :=
  ⟨fun hv ⟨a, b, h₁, h₂⟩ => h₂ (hv a b h₁),
   fun hn a b h₁ => Decidable.byContradiction fun h₂ => hn ⟨a, b, h₁, h₂⟩⟩

/-- A target that factors through `Φ` is valid for `Φ`. -/
theorem factor_valid {α : Sort u} {β : Sort v} {γ : Sort w}
    (Φ : α → β) (R : α → γ) (w : β → γ) (h : ∀ a, R a = w (Φ a)) :
    IsValidFor Φ R :=
  fun a b hab => (h a).trans ((congrArg w hab).trans (h b).symm)

/-- No map applied after an invalid `Φ` can recover the target. -/
theorem invalid_no_factor {α : Sort u} {β : Sort v} {γ : Sort w}
    (Φ : α → β) (R : α → γ) (h : IsInvalidFor Φ R) :
    ¬ ∃ w : β → γ, ∀ a, R a = w (Φ a) :=
  fun ⟨w, hw⟩ => invalid_not_valid Φ R h (factor_valid Φ R w hw)

/-- Factorisation through `Φ`, with `s` an explicit right inverse of `Φ`. -/
theorem valid_factor {α : Sort u} {β : Sort v} {γ : Sort w}
    (Φ : α → β) (R : α → γ) (s : β → α) (hs : ∀ b, Φ (s b) = b)
    (hv : IsValidFor Φ R) : ∃ w : β → γ, ∀ a, R a = w (Φ a) :=
  ⟨fun b => R (s b), fun a => (hv (s (Φ a)) a (hs (Φ a))).symm⟩

theorem valid_iff_factor {α : Sort u} {β : Sort v} {γ : Sort w}
    (Φ : α → β) (R : α → γ) (s : β → α) (hs : ∀ b, Φ (s b) = b) :
    IsValidFor Φ R ↔ ∃ w : β → γ, ∀ a, R a = w (Φ a) :=
  ⟨valid_factor Φ R s hs, fun ⟨w, hw⟩ => factor_valid Φ R w hw⟩

/-- No-repair: if `Φ` identifies more pairs than `Q`, an invalid `Φ` forces an invalid `Q`. -/
theorem no_repair {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x}
    (Φ : α → β) (Q : α → δ) (R : α → γ)
    (hsub : ∀ a b, Ker Φ a b → Ker Q a b) : IsInvalidFor Φ R → IsInvalidFor Q R :=
  fun ⟨a, b, hΦ, hR⟩ => ⟨a, b, hsub a b hΦ, hR⟩

/-- Post-processing an invalid observable stays invalid. -/
theorem invalid_postcompose {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x}
    (Φ : α → β) (g : β → δ) (R : α → γ) :
    IsInvalidFor Φ R → IsInvalidFor (fun a => g (Φ a)) R :=
  no_repair Φ (fun a => g (Φ a)) R (fun _ _ h => congrArg g h)

/-- The chain `W`, `C`, `L`, `B`: blindness of `W` survives calibration, likelihood and update. -/
theorem chain_blind {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x}
    {ε : Sort y} {ζ : Sort z}
    (W : α → β) (C : β → γ) (L : γ → δ) (B : δ → ε) (R : α → ζ) :
    IsInvalidFor W R → IsInvalidFor (fun a => B (L (C (W a)))) R :=
  fun h => invalid_postcompose (fun a => L (C (W a))) B R
    (invalid_postcompose (fun a => C (W a)) L R (invalid_postcompose W C R h))

/-- The kernel of the pair `(Φ, A)` is the intersection of the kernels of `Φ` and `A`. -/
theorem ker_pair {α : Sort u} {β : Type v} {δ : Type x} (Φ : α → β) (A : α → δ) (a b : α) :
    Ker (fun t => (Φ t, A t)) a b ↔ Ker Φ a b ∧ Ker A a b :=
  ⟨fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩,
   fun ⟨h₁, h₂⟩ => congr (congrArg Prod.mk h₁) h₂⟩

/-- Anchor criterion: adjoining `A` makes `Φ` valid for `R` exactly when `A` separates every
pair that `Φ` merges and `R` separates. -/
theorem anchor_valid {α : Sort u} {β : Type v} {γ : Sort w} {δ : Type x} [DecidableEq γ]
    (Φ : α → β) (A : α → δ) (R : α → γ) :
    IsValidFor (fun t => (Φ t, A t)) R ↔
      ∀ a b, Ker Φ a b → ¬ Ker R a b → ¬ Ker A a b :=
  ⟨fun hv a b h₁ h₂ h₃ => h₂ (hv a b ((ker_pair Φ A a b).mpr ⟨h₁, h₃⟩)),
   fun h a b hab => Decidable.byContradiction fun hR =>
     h a b ((ker_pair Φ A a b).mp hab).1 hR ((ker_pair Φ A a b).mp hab).2⟩

/-! ## Layer 1: Bayes' rule on a likelihood-congruent pair -/

/-- The ratios `a : b` and `c : d` agree, in cross-multiplied form. -/
def SameRatio (a b c d : Int) : Prop := a * d = c * b

/-- Equal likelihood `ℓ` leaves the odds `π₁ : π₂` unchanged. -/
theorem posterior_odds_frozen (π₁ π₂ ℓ : Int) : SameRatio (π₁ * ℓ) (π₂ * ℓ) π₁ π₂ := by
  unfold SameRatio
  rw [Int.mul_assoc, Int.mul_comm ℓ π₂]

/-- Within a likelihood-congruent class the posterior conditional equals the prior conditional. -/
theorem within_class_prior_echo (π₁ π₂ ℓ : Int) :
    SameRatio (π₁ * ℓ) (π₁ * ℓ + π₂ * ℓ) π₁ (π₁ + π₂) := by
  unfold SameRatio
  rw [← Int.add_mul, Int.mul_comm (π₁ + π₂) ℓ, ← Int.mul_assoc]

/-- The same with a common normaliser `k` on both posteriors (`k` stands for `1 / Z`). -/
theorem within_class_prior_echo_norm (π₁ π₂ ℓ k : Int) :
    SameRatio (π₁ * ℓ * k) (π₁ * ℓ * k + π₂ * ℓ * k) π₁ (π₁ + π₂) := by
  unfold SameRatio
  rw [← Int.add_mul, ← Int.add_mul]
  simp only [Int.mul_left_comm, Int.mul_comm]

/-! ## Layer 2: LIGO witnesses -/

/-- (a) Waveform fibre. TaylorF2 1.5PN coefficient `c + 4β + δ`, with spin-orbit
coupling `β` and a coefficient error `δ` shared by both models. -/
def psi15 (c β δ : Int) : Int := c + 4 * β + δ

/-- Phase as a function of the frequency weight `w` (the value of the basis function `v³`). -/
def phase15 (pref c : Int) (s : Int × Int) (w : Int) : Int := pref * psi15 c s.1 s.2 * w

theorem psi15_fibre (c β k : Int) : psi15 c β (4 * k) = psi15 c (β + k) 0 := by
  unfold psi15
  rw [Int.add_zero, Int.mul_add, Int.add_assoc]

/-- The orbit of the dark direction: shifting `β` by `t` and `δ` by `-4t` leaves `ψ` fixed. -/
theorem psi15_orbit (c β δ t : Int) : psi15 c (β + t) (δ - 4 * t) = psi15 c β δ := by
  unfold psi15
  rw [Int.mul_add, ← Int.add_assoc, Int.add_assoc (c + 4 * β) (4 * t),
    Int.add_comm (4 * t), Int.sub_add_cancel]

/-- The fibre of `ψ` through `(β, δ)` is exactly the line `4β + δ = const`. -/
theorem psi15_eq_iff (c β δ β' δ' : Int) :
    psi15 c β δ = psi15 c β' δ' ↔ 4 * β + δ = 4 * β' + δ' := by
  unfold psi15
  constructor
  · intro h
    exact Int.add_left_cancel ((Int.add_assoc c _ _).symm.trans (h.trans (Int.add_assoc c _ _)))
  · intro h
    exact (Int.add_assoc c _ _).trans ((congrArg (c + ·) h).trans (Int.add_assoc c _ _).symm)

/-- `(β, 4k)` and `(β + k, 0)` give the same waveform at every frequency weight. -/
theorem phase15_fibre (pref c β k : Int) :
    phase15 pref c (β, 4 * k) = phase15 pref c (β + k, 0) :=
  congrArg (fun t : Int => fun w : Int => pref * t * w) (psi15_fibre c β k)

/-- The waveform, at all frequencies at once, is invalid for the spin `β`. -/
theorem waveform_invalid_for_spin (pref c : Int) :
    IsInvalidFor (phase15 pref c) (fun s : Int × Int => s.1) :=
  ⟨(0, 4), (1, 0), phase15_fibre pref c 0 1, by decide⟩

/-- The 1.5PN coefficient is invalid for the spin `β`. -/
theorem psi15_invalid_for_spin (c : Int) :
    IsInvalidFor (fun s : Int × Int => psi15 c s.1 s.2) (fun s => s.1) :=
  ⟨(0, 4), (1, 0), psi15_fibre c 0 1, by decide⟩

/-- (b) Dark port. Sum of the first `n` terms of `f`. -/
def sumTo : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumTo n f + f n

theorem sumTo_zero_fn : ∀ n : Nat, sumTo n (fun _ => 0) = 0
  | 0 => rfl
  | n + 1 => (congrArg (fun t => t + 0) (sumTo_zero_fn n)).trans rfl

theorem sumTo_one_fn : ∀ n : Nat, sumTo n (fun _ => 1) = (n : Int)
  | 0 => rfl
  | n + 1 => (congrArg (fun t => t + 1) (sumTo_one_fn n)).trans rfl

theorem cons_congr {α : Type u} {a b : α} {l m : List α} (h₁ : a = b) (h₂ : l = m) :
    a :: l = b :: m := by
  cases h₁
  cases h₂
  rfl

/-- The differences `ε i - ε j` over a list of index pairs: the inter-model comparisons. -/
def diffs (ε : Nat → Int) : List (Nat × Nat) → List Int
  | [] => []
  | p :: ps => (ε p.1 - ε p.2) :: diffs ε ps

theorem diffs_shift (ε : Nat → Int) (g : Int) :
    ∀ l : List (Nat × Nat), diffs (fun i => ε i + g) l = diffs ε l
  | [] => rfl
  | p :: ps =>
    cons_congr (Int.add_sub_add_right (ε p.1) g (ε p.2)) (diffs_shift ε g ps)

/-- Any statistic of any list of inter-model differences is blind to a common shift `g`. -/
theorem pairwise_blind_list {β : Sort u} (S : List Int → β) (ε : Nat → Int) (g : Int)
    (l : List (Nat × Nat)) :
    S (diffs (fun i => ε i + g) l) = S (diffs ε l) :=
  congrArg S (diffs_shift ε g l)

theorem diffs_const (a b : Int) :
    ∀ l : List (Nat × Nat), diffs (fun _ => a) l = diffs (fun _ => b) l
  | [] => rfl
  | _ :: ps => cons_congr ((Int.sub_self a).trans (Int.sub_self b).symm) (diffs_const a b ps)

/-- ... so it cannot classify the summed error of any `N ≥ 1` models. -/
theorem pairwise_invalid_for_common_mode_list (N : Nat) (hN : 0 < N) {β : Sort u}
    (S : List Int → β) (l : List (Nat × Nat)) :
    IsInvalidFor (fun ε : Nat → Int => S (diffs ε l)) (fun ε => sumTo N ε) :=
  ⟨fun _ => 0, fun _ => 1, congrArg S (diffs_const 0 1 l),
   fun h => Nat.ne_of_lt hN
     (Int.ofNat.inj ((sumTo_zero_fn N).symm.trans (h.trans (sumTo_one_fn N))))⟩

/-- The same for tables `Nat → Nat → Int` of differences; `hS` says that `S` reads the table
only through its values. -/
theorem pairwise_blind {β : Sort u} (S : (Nat → Nat → Int) → β)
    (hS : ∀ f f' : Nat → Nat → Int, (∀ i j, f i j = f' i j) → S f = S f')
    (ε : Nat → Int) (g : Int) :
    S (fun i j => (ε i + g) - (ε j + g)) = S (fun i j => ε i - ε j) :=
  hS _ _ (fun i j => Int.add_sub_add_right (ε i) g (ε j))

theorem pairwise_invalid_for_common_mode (N : Nat) (hN : 0 < N) {β : Sort u}
    (S : (Nat → Nat → Int) → β) :
    IsInvalidFor (fun ε : Nat → Int => S (fun i j => ε i - ε j))
                 (fun ε => sumTo N ε) :=
  ⟨fun _ => 0, fun _ => 1, rfl,
   fun h => Nat.ne_of_lt hN
     (Int.ofNat.inj ((sumTo_zero_fn N).symm.trans (h.trans (sumTo_one_fn N))))⟩

/-- (c) The equal-weight mixture variance, times four. -/
def mixVar4 (m1 m2 v1 v2 : Int) : Int := 2 * (v1 + v2) + (m1 - m2) * (m1 - m2)

theorem mixVar4_blind (m1 m2 v1 v2 b : Int) :
    mixVar4 (m1 + b) (m2 + b) v1 v2 = mixVar4 m1 m2 v1 v2 := by
  unfold mixVar4
  rw [Int.add_sub_add_right]

/-- The mixture variance is invalid for the common location of the two medians. -/
theorem mixVar4_invalid_for_location (v1 v2 : Int) :
    IsInvalidFor (fun m : Int × Int => mixVar4 m.1 m.2 v1 v2) (fun m => m.1) :=
  ⟨(0, 0), (1, 1), (mixVar4_blind 0 0 v1 v2 1).symm, by decide⟩

/-- The parallelogram law. -/
theorem parallelogram (a b : Int) :
    (a + b) * (a + b) + (a - b) * (a - b) = 2 * (a * a + b * b) := by
  rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_sub,
    Int.mul_comm b a, Int.two_mul]
  simp only [Int.sub_eq_add_neg, Int.neg_add, Int.neg_neg]
  calc a * a + a * b + (a * b + b * b) + (a * a + -(a * b) + (-(a * b) + b * b))
      = (a * b + -(a * b)) + (a * b + -(a * b)) + (a * a + b * b + (a * a + b * b)) := by
        simp only [Int.add_assoc, Int.add_left_comm, Int.add_comm]
    _ = a * a + b * b + (a * a + b * b) := by
        rw [Int.add_right_neg, Int.add_zero, Int.zero_add]

/-- Law of total variance for the equal-weight mixture, times four:
`4 (E[x²] - E[x]²) = 2 ((v₁ + μ₁²) + (v₂ + μ₂²)) - (μ₁ + μ₂)²`. -/
theorem mixVar4_from_moments (m1 m2 v1 v2 : Int) :
    2 * ((v1 + m1 * m1) + (v2 + m2 * m2)) - (m1 + m2) * (m1 + m2) = mixVar4 m1 m2 v1 v2 := by
  unfold mixVar4
  have h1 : (v1 + m1 * m1) + (v2 + m2 * m2) = (v1 + v2) + (m1 * m1 + m2 * m2) := by
    simp only [Int.add_assoc, Int.add_left_comm]
  rw [h1, Int.mul_add 2 (v1 + v2) (m1 * m1 + m2 * m2), ← parallelogram m1 m2,
    Int.add_left_comm (2 * (v1 + v2)),
    Int.add_comm ((m1 + m2) * (m1 + m2)), Int.add_sub_cancel]

/-- (d) Lock point. `etaNum m1 m2 = m₁m₂`, the numerator of `η = m₁m₂ / (m₁ + m₂)²`. -/
def etaNum (m1 m2 : Int) : Int := m1 * m2

theorem eta_swap (m1 m2 : Int) : etaNum m1 m2 = etaNum m2 m1 := Int.mul_comm m1 m2

/-- Total mass together with the numerator of `η`. -/
def etaPair (m : Int × Int) : Int × Int := (m.1 + m.2, etaNum m.1 m.2)

theorem prod_mk_congr {α : Type u} {β : Type v} {a a' : α} {b b' : β}
    (h₁ : a = a') (h₂ : b = b') : (a, b) = (a', b') := by
  cases h₁
  cases h₂
  rfl

theorem etaPair_swap (m1 m2 : Int) : etaPair (m1, m2) = etaPair (m2, m1) :=
  prod_mk_congr (Int.add_comm m1 m2) (eta_swap m1 m2)

/-- `η` and the total mass cannot classify which component is the heavier one. -/
theorem eta_invalid_for_q : IsInvalidFor etaPair (fun m : Int × Int => m.1) :=
  ⟨(2, 1), (1, 2), by decide, by decide⟩

/-- For every pair of distinct masses, the swapped pair has the same `η` and total mass. -/
theorem eta_invalid_of_ne (a b : Int) (h : a ≠ b) :
    IsInvalidFor etaPair (fun m : Int × Int => m.1) :=
  ⟨(a, b), (b, a), etaPair_swap a b, h⟩

theorem four_mul_eq (x : Int) : 4 * x = x + x + x + x := by
  have h4 : (4 : Int) = 1 + 1 + 1 + 1 := rfl
  rw [h4, Int.add_mul, Int.add_mul, Int.add_mul, Int.one_mul]

theorem sq_diff_core (p q r : Int) :
    p + q + (q + r) - (p - q - (q - r)) = q + q + q + q := by
  simp only [Int.sub_eq_add_neg, Int.neg_add, Int.neg_neg]
  calc p + q + (q + r) + (-p + q + (q + -r))
      = (p + -p) + (r + -r) + q + q + q + q := by
        simp only [Int.add_assoc, Int.add_left_comm, Int.add_comm]
    _ = q + q + q + q := by
        rw [Int.add_right_neg, Int.add_right_neg, Int.add_zero, Int.zero_add]

/-- The fold identity `4 m₁m₂ = M² − (m₁ − m₂)²`: `η` is quadratic in the mass difference. -/
theorem eta_fold (m1 m2 : Int) :
    4 * etaNum m1 m2 = (m1 + m2) * (m1 + m2) - (m1 - m2) * (m1 - m2) := by
  unfold etaNum
  rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_sub,
    Int.mul_comm m2 m1, sq_diff_core, four_mul_eq]


/-! ## Layer 3: the shared-error triangle (composite of (a), (b), (c) and Layer 1) -/

/-- Twice the published waveform-systematics variance at a credible-interval edge:
`2σ²_sys = (X_E − X_O)² + (X_P − X_O)²`. -/
def sysVar2 (xE xP xO : Int) : Int := (xE - xO) * (xE - xO) + (xP - xO) * (xP - xO)

theorem sysVar2_blind (xE xP xO g : Int) :
    sysVar2 (xE + g) (xP + g) (xO + g) = sysVar2 xE xP xO := by
  unfold sysVar2
  rw [Int.add_sub_add_right, Int.add_sub_add_right]

/-- The three uncertainty numbers reported for a two-model analysis ,  the Overall mixture
width (×4), the systematic variance at an edge (×2), and the inter-model gap ,  form one
observable. It is invalid for the shared error `g`. -/
theorem uncertainty_triple_invalid_for_shared_error (μE μP vE vP xE xP xO : Int) :
    IsInvalidFor
      (fun g : Int => (mixVar4 (μE + g) (μP + g) vE vP,
                       (sysVar2 (xE + g) (xP + g) (xO + g), (μE + g) - (μP + g))))
      (fun g => g) :=
  ⟨0, 1,
   prod_mk_congr ((mixVar4_blind μE μP vE vP 0).trans (mixVar4_blind μE μP vE vP 1).symm)
     (prod_mk_congr ((sysVar2_blind xE xP xO 0).trans (sysVar2_blind xE xP xO 1).symm)
       ((Int.add_sub_add_right μE 0 μP).trans (Int.add_sub_add_right μE 1 μP).symm)),
   by decide⟩

/-- Spin triangle. Model coefficient errors `δ + d` (EOBNR) and `δ − d` (IMRPhenom) on the
1.5PN term. A `δ = 0` analysis reads `4β̂ = ψ − c`. The inter-model gap in `4β̂` is `2d`,
independent of `δ`; the bias of the averaged estimate (×2) is `2δ`, independent of `d`. -/
theorem spin_triangle (c β δ d : Int) :
    (psi15 c β (δ + d) - c) - (psi15 c β (δ - d) - c) = d + d ∧
    ((psi15 c β (δ + d) - c) + (psi15 c β (δ - d) - c)) - (4 * β + 4 * β) = δ + δ := by
  unfold psi15
  constructor <;> omega

/-- So the inter-model spin gap cannot classify the spin bias. -/
theorem spin_gap_invalid_for_bias (c β d : Int) :
    IsInvalidFor (fun δ : Int => (psi15 c β (δ + d) - c) - (psi15 c β (δ - d) - c))
                 (fun δ => ((psi15 c β (δ + d) - c) + (psi15 c β (δ - d) - c)) - (4 * β + 4 * β)) :=
  ⟨0, 1, (spin_triangle c β 0 d).1.trans (spin_triangle c β 1 d).1.symm,
   fun h => absurd (((spin_triangle c β 0 d).2.symm.trans h).trans (spin_triangle c β 1 d).2)
     (by decide)⟩

/-- Fold law: at fixed total mass, moving the mass difference `Δ` by `e` moves
`M² − Δ² = 4m₁m₂` by `e(2Δ + e)`. -/
theorem fold_shift (M Δ e : Int) :
    (M * M - Δ * Δ) - (M * M - (Δ + e) * (Δ + e)) = e * (Δ + Δ + e) := by
  simp only [Int.add_mul, Int.mul_add, Int.mul_comm Δ e]
  omega

/-- At equal mass the response is second order: the likelihood is flat in `Δ` there. -/
theorem fold_flat_at_equal_mass (M e : Int) :
    (M * M - 0 * 0) - (M * M - (0 + e) * (0 + e)) = e * e := by
  rw [fold_shift M 0 e, Int.add_zero, Int.zero_add]

/-- GW150914 detector-frame medians (0.1 M⊙): `M = 712`, `Δ = 62`. A 1 M⊙ shift in `Δ`
moves `4m₁m₂ = 503100` by `1340` (0.27 %). -/
theorem gw150914_fold_shift :
    (712 * 712 - 62 * 62) - (712 * 712 - 72 * 72) = (1340 : Int) ∧
    4 * etaNum 387 325 = 503100 := by decide


/-! ## Layer 4: the lock point as a spin obstruction, and the detection-level odds -/

/-- Effective-spin numerator `m₁χ₁ + m₂χ₂` (`χ_eff · M`). -/
def effNum (m1 m2 x1 x2 : Int) : Int := m1 * x1 + m2 * x2

/-- Lock point, general form. For any observable symmetric under exchanging the two black
holes (every physical waveform is), at equal mass the spin of black hole 1 is not determined.
The labelling convention `m₂ ≤ m₁` does not break this tie. -/
theorem lockpoint_any_symmetric {β : Sort u} (F : (Int × Int) × (Int × Int) → β)
    (hF : ∀ p q, F (p, q) = F (q, p)) (a x y : Int) (h : x ≠ y) :
    IsInvalidFor F (fun s => s.1.2) :=
  ⟨((a, x), (a, y)), ((a, y), (a, x)), hF (a, x) (a, y), h⟩

/-- The observable `(M, m₁m₂, m₁χ₁ + m₂χ₂)` is exchange-symmetric. -/
theorem massSpinObs_symm (p q : Int × Int) :
    (p.1 + q.1, (etaNum p.1 q.1, effNum p.1 q.1 p.2 q.2)) =
      (q.1 + p.1, (etaNum q.1 p.1, effNum q.1 p.1 q.2 p.2)) :=
  prod_mk_congr (Int.add_comm p.1 q.1)
    (prod_mk_congr (eta_swap p.1 q.1) (Int.add_comm (p.1 * p.2) (q.1 * q.2)))

/-- So `(M, η, χ_eff)` cannot classify the primary spin at the lock point. -/
theorem lockpoint_invalid_for_primary_spin (a x y : Int) (h : x ≠ y) :
    IsInvalidFor (fun s : (Int × Int) × (Int × Int) =>
        (s.1.1 + s.2.1, (etaNum s.1.1 s.2.1, effNum s.1.1 s.2.1 s.1.2 s.2.2)))
      (fun s => s.1.2) :=
  lockpoint_any_symmetric _ (fun p q => massSpinObs_symm p q) a x y h

/-- Off the lock point, the signal that tells the two spin assignments apart is
(mass difference) × (spin difference): it vanishes linearly at the fold. -/
theorem spin_attribution_signal (a b x y : Int) :
    effNum a b x y - effNum a b y x = (a - b) * (x - y) := by
  unfold effNum
  simp only [Int.sub_mul, Int.mul_sub]
  omega

/-- GW150914 detector-frame medians (0.1 M⊙): `Δ = 62`, `M = 712`. A spin difference of
1.0 (10 units) between the holes moves `M · χ_eff` by `620`, against `7120` for a common
spin change of 1.0. -/
theorem gw150914_attribution_weight :
    effNum 387 325 10 0 - effNum 387 325 0 10 = (620 : Int) ∧
    effNum 387 325 10 10 - effNum 387 325 0 0 = (7120 : Int) := by decide

/-- Cause of a zero-lag coincidence. -/
inductive Cause where
  | gw
  | corr
  deriving DecidableEq

/-- Detection, data side. If a correlated transient reproduces the strain a GW would leave in
both detectors, every statistic of the strain pair ,  matched filter, χ², coincidence,
time slides, FAR ,  is invalid for the cause. -/
theorem strain_statistic_invalid_for_cause {D : Type} {β : Sort u} (S : D → β) (d : D) :
    IsInvalidFor (fun s : D × Cause => S s.1) (fun s => s.2) :=
  ⟨(d, Cause.gw), (d, Cause.corr), rfl, fun h => Cause.noConfusion h⟩

/-- Detection, inference side (Layer 1 applied): on such data the posterior odds GW : corr
equal the prior odds. -/
theorem detection_odds_frozen (πgw πcorr ℓ : Int) :
    SameRatio (πgw * ℓ) (πcorr * ℓ) πgw πcorr :=
  posterior_odds_frozen πgw πcorr ℓ

/-- The environmental (PEM) anchor: it fires only on a correlated transient that couples to
the sensors. -/
def pem : Cause × Bool → Bool
  | (Cause.corr, true) => true
  | _ => false

/-- An uncoupled correlated transient defeats the anchor. -/
theorem pem_fails_on_uncoupled {D : Type} (d : D) :
    IsInvalidFor (fun s : D × (Cause × Bool) => (s.1, pem s.2)) (fun s => s.2.1) :=
  ⟨(d, (Cause.gw, false)), (d, (Cause.corr, false)), rfl, fun h => Cause.noConfusion h⟩

/-- The anchor repairs detection on the class where every correlated transient couples. -/
theorem pem_repairs_when_coupled {D : Type} :
    IsValidFor
      (fun s : {s : D × (Cause × Bool) // s.2.1 = Cause.corr → s.2.2 = true} =>
        (s.1.1, pem s.1.2))
      (fun s => s.1.2.1) := by
  intro ⟨⟨d, c, b⟩, hc⟩ ⟨⟨d', c', b'⟩, hc'⟩ h
  have hp : pem (c, b) = pem (c', b') := congrArg (fun p => p.2) h
  have k : c = Cause.corr → b = true := hc
  have k' : c' = Cause.corr → b' = true := hc'
  show c = c'
  cases c <;> cases c' <;> cases b <;> cases b' <;> simp_all [pem]

/-! ## Layer 5: the core principles as laws over LIGO's whole pipeline -/

/-- Every procedure errs. On a witness pair, every rule `w` acting on the observable is wrong
on at least one of the two states. -/
theorem every_procedure_errs {α : Sort u} {β : Sort v} {γ : Sort w}
    (Φ : α → β) (R : α → γ) {a b : α} (hΦ : Φ a = Φ b) (hR : R a ≠ R b) (w : β → γ) :
    ¬ (w (Φ a) = R a ∧ w (Φ b) = R b) :=
  fun ⟨ha, hb⟩ => hR (ha.symm.trans ((congrArg w hΦ).trans hb))

/-- Conservation of distinction: no stage separates states its input merged. -/
theorem conservation_of_distinction {α : Sort u} {β : Sort v} {δ : Sort x}
    (Φ : α → β) (P : β → δ) {a b : α} (h : Φ a = Φ b) : P (Φ a) = P (Φ b) :=
  congrArg P h

/-- LIGO detection pipeline, end to end. For any whitening/filter `C`, any ranking `L`, and
any background/FAR/decision stage `B`, the pipeline on the strain pair is invalid for the
cause GW vs a strain-identical correlated transient. -/
theorem detection_pipeline_blind {D Y₁ Y₂ Y₃ : Type} (C : D → Y₁) (L : Y₁ → Y₂) (B : Y₂ → Y₃)
    (d : D) :
    IsInvalidFor (fun s : D × Cause => B (L (C s.1))) (fun s => s.2) :=
  chain_blind (fun s : D × Cause => s.1) C L B (fun s => s.2)
    (strain_statistic_invalid_for_cause (fun x : D => x) d)

/-- And every decision rule on that pipeline's output misclassifies GW or the mimic. -/
theorem detection_rule_errs {D Y : Type} (P : D → Y) (rule : Y → Cause) (d : D) :
    ¬ (rule (P d) = Cause.gw ∧ rule (P d) = Cause.corr) :=
  fun ⟨h1, h2⟩ => Cause.noConfusion (h1.symm.trans h2)

/-- LIGO parameter pipeline, end to end: any conclusion `B` (e.g. "robust") computed from the
reported uncertainty triple is invalid for the shared waveform error. -/
theorem pe_pipeline_blind {Y : Sort u} (B : Int × (Int × Int) → Y) (μE μP vE vP xE xP xO : Int) :
    IsInvalidFor
      (fun g : Int => B (mixVar4 (μE + g) (μP + g) vE vP,
                         (sysVar2 (xE + g) (xP + g) (xO + g), (μE + g) - (μP + g))))
      (fun g => g) :=
  invalid_postcompose _ B _ (uncertainty_triple_invalid_for_shared_error μE μP vE vP xE xP xO)

/-- Spin pipeline at the lock point: any procedure on any exchange-symmetric observable is
invalid for the primary spin. -/
theorem lockpoint_pipeline_blind {β : Sort u} {Y : Sort v} (F : (Int × Int) × (Int × Int) → β)
    (hF : ∀ p q, F (p, q) = F (q, p)) (P : β → Y) (a x y : Int) (h : x ≠ y) :
    IsInvalidFor (fun s => P (F s)) (fun s => s.1.2) :=
  invalid_postcompose F P _ (lockpoint_any_symmetric F hF a x y h)

#print axioms invalid_not_valid
#print axioms valid_iff_not_invalid
#print axioms factor_valid
#print axioms invalid_no_factor
#print axioms valid_factor
#print axioms valid_iff_factor
#print axioms no_repair
#print axioms invalid_postcompose
#print axioms chain_blind
#print axioms ker_pair
#print axioms anchor_valid
#print axioms posterior_odds_frozen
#print axioms within_class_prior_echo
#print axioms within_class_prior_echo_norm
#print axioms psi15_fibre
#print axioms psi15_orbit
#print axioms psi15_eq_iff
#print axioms phase15_fibre
#print axioms waveform_invalid_for_spin
#print axioms psi15_invalid_for_spin
#print axioms sumTo_zero_fn
#print axioms sumTo_one_fn
#print axioms cons_congr
#print axioms diffs_shift
#print axioms pairwise_blind_list
#print axioms diffs_const
#print axioms pairwise_invalid_for_common_mode_list
#print axioms pairwise_blind
#print axioms pairwise_invalid_for_common_mode
#print axioms mixVar4_blind
#print axioms mixVar4_invalid_for_location
#print axioms parallelogram
#print axioms mixVar4_from_moments
#print axioms eta_swap
#print axioms prod_mk_congr
#print axioms etaPair_swap
#print axioms eta_invalid_for_q
#print axioms eta_invalid_of_ne
#print axioms four_mul_eq
#print axioms sq_diff_core
#print axioms eta_fold
#print axioms sysVar2_blind
#print axioms uncertainty_triple_invalid_for_shared_error
#print axioms spin_triangle
#print axioms spin_gap_invalid_for_bias
#print axioms fold_shift
#print axioms fold_flat_at_equal_mass
#print axioms gw150914_fold_shift
#print axioms lockpoint_any_symmetric
#print axioms massSpinObs_symm
#print axioms lockpoint_invalid_for_primary_spin
#print axioms spin_attribution_signal
#print axioms gw150914_attribution_weight
#print axioms strain_statistic_invalid_for_cause
#print axioms detection_odds_frozen
#print axioms pem_fails_on_uncoupled
#print axioms pem_repairs_when_coupled
#print axioms every_procedure_errs
#print axioms conservation_of_distinction
#print axioms detection_pipeline_blind
#print axioms detection_rule_errs
#print axioms pe_pipeline_blind
#print axioms lockpoint_pipeline_blind

end LigoCongruence
