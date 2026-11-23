/-!
# LIGO anchors: common modes, fibres, prior echo, and reference-relative error

Core Lean 4 only (no Mathlib), in the style of the `PerfectAssociation` package.
Integer encodings: masses in 0.1 M⊙, Table I medians ×100.
Closed certificates use `decide`; general statements use core `Int`/`Nat` lemmas.
-/
namespace LigoAnchors

universe u v w

/-! ## 1. Dark port: every inter-model comparison is blind to a shared error -/

/-- Comparison of two waveform-model errors (EOBNR minus IMRPhenom). -/
def compare (eE eP : Int) : Int := eE - eP

theorem compare_blind (eE eP g : Int) : compare (eE + g) (eP + g) = compare eE eP := by
  unfold compare
  rw [Int.add_sub_add_right]

/-- Closed witness: identical comparison, different common-mode error. -/
theorem compare_cannot_see_common_mode :
    compare 0 0 = compare 1 1 ∧ (0 : Int) + 0 ≠ 1 + 1 := by decide

theorem pointwise_blind (e : Nat → Int) (g : Int) (i j : Nat) :
    (e i + g) - (e j + g) = e i - e j := by
  rw [Int.add_sub_add_right]

/-- Any statistic built from pairwise differences (mixture gap, JS divergence of shifted
    posteriors, …) is invariant under a common shift, for any number of models. -/
theorem any_comparison_statistic_blind {β : Sort u} (T : (Nat → Nat → Int) → β)
    (hT : ∀ f f' : Nat → Nat → Int, (∀ i j, f i j = f' i j) → T f = T f')
    (e : Nat → Int) (g : Int) :
    T (fun i j => (e i + g) - (e j + g)) = T (fun i j => e i - e j) :=
  hT _ _ (pointwise_blind e g)

/-! ## 2. The same algebra for calibration: common amplitude scale ↔ distance -/

/-- Observed log-amplitude = log calibration scale − log luminosity distance. -/
def logAmp (kappa delta : Int) : Int := kappa - delta

/-- A calibration-scale error shared with a distance shift is invisible (exact fibre).
    Both LIGO photon calibrators trace to one "gold standard": its error is this c. -/
theorem calibration_distance_fibre (kappa delta c : Int) :
    logAmp (kappa + c) (delta + c) = logAmp kappa delta := by
  unfold logAmp
  rw [Int.add_sub_add_right]

/-! ## 3. Exact waveform fibre (TaylorF2 1.5PN coefficient) -/

/-- 1.5PN phase coefficient c + 4β + δ; δ is a coefficient error shared by both models. -/
def psi15 (c beta delta : Int) : Int := c + 4 * beta + delta

theorem psi15_fibre (c beta k : Int) : psi15 c beta (4 * k) = psi15 c (beta + k) 0 := by
  unfold psi15
  rw [Int.add_zero, Int.mul_add, Int.add_assoc]

/-- The equality holds at every frequency weight w(v): it is an equality of waveforms. -/
theorem psi15_fibre_all_frequencies (wt : Int → Int) (c beta k f : Int) :
    wt f * psi15 c beta (4 * k) = wt f * psi15 c (beta + k) 0 := by
  rw [psi15_fibre]

/-- Closed witness: same waveform coefficient, different spin. -/
theorem waveform_cannot_classify_spin :
    psi15 0 0 4 = psi15 0 1 0 ∧ (0 : Int) ≠ 1 := by decide

/-- Any likelihood that depends on the parameters only through the waveform is equal on
    the fibre, for every data set d. -/
theorem likelihood_fibre {Θ : Sort u} {H : Sort v} {D : Sort w}
    (logL : D → H → Int) (g : Θ → H) {p q : Θ} (h : g p = g q) (d : D) :
    logL d (g p) = logL d (g q) :=
  congrArg (logL d) h

/-! ## 4. The paper's equal-weight mixture variance (×4) cannot see a common bias -/

def mixVar4 (m1 m2 v1 v2 : Int) : Int := 2 * (v1 + v2) + (m1 - m2) * (m1 - m2)

theorem mixVar4_blind (m1 m2 v1 v2 b : Int) :
    mixVar4 (m1 + b) (m2 + b) v1 v2 = mixVar4 m1 m2 v1 v2 := by
  unfold mixVar4
  rw [Int.add_sub_add_right]

/-- Table I, a₁ (×100): medians 22 and 32, σ ≈ 23. The visible gap contributes
    100 of 2216 (4.5 %) to 4·Var_mix, and any common bias b leaves 2216 unchanged. -/
theorem tableI_a1_mixture :
    mixVar4 22 32 529 529 = 2216 ∧
    ∀ b ∈ List.range 41, mixVar4 (22 + Int.ofNat b) (32 + Int.ofNat b) 529 529 = 2216 := by
  decide

/-! ## 5. Lock point at GW150914: η(q) = η(1/q), quadratic at the fold -/

def etaNum (m1 m2 : Int) : Int := m1 * m2

theorem eta_swap (m1 m2 : Int) : etaNum m1 m2 = etaNum m2 m1 := by
  unfold etaNum
  exact Int.mul_comm m1 m2

/-- Detector-frame medians 38.7, 32.5 M⊙: 4·m₁m₂ = M² − (m₁ − m₂)², with (m₁ − m₂)² = 3844. -/
theorem gw150914_fold :
    4 * etaNum 387 325 = (387 + 325) * (387 + 325) - (387 - 325) * (387 - 325) ∧
    (387 - 325) * (387 - 325) = (3844 : Int) ∧ etaNum 387 325 = etaNum 325 387 := by
  decide

theorem fold_identity_grid :
    ∀ a ∈ List.range 13, ∀ d ∈ List.range 7,
      4 * ((Int.ofNat a + Int.ofNat d) * (Int.ofNat a - Int.ofNat d)) =
        (2 * Int.ofNat a) * (2 * Int.ofNat a) - 4 * (Int.ofNat d * Int.ofNat d) := by
  decide

/-! ## 6. Prior echo along an exact fibre: same data, different posterior on β -/

/-- The data see only ψ = β + ℓ, and say ψ = 1. -/
def lik (psi : Int) : Nat := if psi = 1 then 1 else 0

/-- The paper's convention: the shared error ℓ is fixed at 0. -/
def priorPaper (l : Int) : Nat := if l = 0 then 1 else 0

/-- An open prior: ℓ ∈ {0, 1}, equally weighted. -/
def priorOpen (_l : Int) : Nat := 1

def massBeta (prior : Int → Nat) (beta : Int) : Nat :=
  ([0, 1] : List Int).foldl (fun z l => z + prior l * lik (beta + l)) 0

def massTotal (prior : Int → Nat) : Nat :=
  ([0, 1, 2] : List Int).foldl (fun z b => z + massBeta prior b) 0

/-- Paper's prior: P(β = 1 | data) = 1. -/
theorem paper_prior_certainty : massBeta priorPaper 1 = massTotal priorPaper := by decide

/-- Open prior on the shared error: P(β = 1 | data) = 1/2. -/
theorem open_prior_half : 2 * massBeta priorOpen 1 = massTotal priorOpen := by decide

/-- Identical likelihood; the posterior on β is set by the prior on the error. -/
theorem same_data_different_beta :
    massBeta priorPaper 1 * massTotal priorOpen ≠
      massBeta priorOpen 1 * massTotal priorPaper := by decide

/-- General form: within an exact fibre the posterior ratio equals the prior ratio. -/
def post (prior : Int → Int → Nat) (L : Int → Nat) (uu b l : Int) : Nat :=
  prior b l * L (b + l * uu)

theorem fibre_prior_echo (prior : Int → Int → Nat) (L : Int → Nat) (uu b l b' l' : Int)
    (hfib : b + l * uu = b' + l' * uu) :
    post prior L uu b l * prior b' l' = post prior L uu b' l' * prior b l := by
  unfold post
  rw [hfib]
  generalize L (b' + l' * uu) = y
  generalize prior b l = x
  generalize prior b' l' = z
  rw [Nat.mul_right_comm x y z, Nat.mul_comm x z, Nat.mul_right_comm z x y]

/-! ## 7. Error is reference-relative; an anchor breaks the degeneracy -/

def err (meas ref : Int) : Int := meas - ref

/-- Shifting the (unknown) reference leaves every internal error comparison unchanged. -/
theorem reference_shift_invisible (m1 m2 r c : Int) :
    err m1 (r + c) - err m2 (r + c) = err m1 r - err m2 r :=
  (Int.add_sub_add_right m1 (-(r + c)) m2).trans (Int.add_sub_add_right m1 (-r) m2).symm

/-- One external anchor (a measurement of the known truth) identifies the offset. -/
theorem anchor_identifies (m truth c c' : Int)
    (h : err m (truth + c) = err m (truth + c')) : c = c' :=
  Int.add_left_cancel ((Int.sub_right_inj m).mp h)

#print axioms compare_blind
#print axioms compare_cannot_see_common_mode
#print axioms any_comparison_statistic_blind
#print axioms calibration_distance_fibre
#print axioms psi15_fibre
#print axioms psi15_fibre_all_frequencies
#print axioms waveform_cannot_classify_spin
#print axioms likelihood_fibre
#print axioms mixVar4_blind
#print axioms tableI_a1_mixture
#print axioms eta_swap
#print axioms gw150914_fold
#print axioms fold_identity_grid
#print axioms paper_prior_certainty
#print axioms open_prior_half
#print axioms same_data_different_beta
#print axioms fibre_prior_echo
#print axioms reference_shift_invisible
#print axioms anchor_identifies

end LigoAnchors
