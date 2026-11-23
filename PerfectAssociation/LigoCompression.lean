import PerfectAssociation.LigoCongruence
import PerfectAssociation.Statistics

/-!
# LIGO compression: what the averaging and compression steps cannot see

Core Lean 4 only. Every definition is computable. Counts are `Nat`, signed quantities `Int`,
ratios are cross-multiplied.

* §1 Time slides. A time-slid pair sees only the two single-detector marginals. The fibre of the
  slide data is the Fréchet–Hoeffding class of zero-lag couplings, and the zero-lag coincidence
  count is its coordinate. The slide estimate is exact on the independence locus and is neither an
  upper nor a lower bound off it.
* §2 Second moments. The PSD keeps `(mass, Σ w·a²)` of a whitened bin. Its fibre contains noise
  laws whose tail weight covers the whole Chebyshev interval.
* §3 Equal-weight averaging. The "Overall" posterior forgets the evidence ratio, and the published
  systematic-error formula `σ²_sys = [(X_E − X_O)² + (X_P − X_O)²]/2` forgets every common shift.
* §4 Finite anchors. `k` distinct NR nodes identify exactly the common-mode errors of degree `< k`.
  The node polynomial is invisible to the nodes and to every inter-model comparison at once.
* §5 Rank one. Two detectors never determine three polarization amplitudes; a 2×2 response is
  faithful exactly when its determinant is nonzero; proportional responses give perfectly
  associated outputs for every polarization history.
-/
namespace LigoCompression

open LigoCongruence

universe u

/-! ## §1 Time slides and the Fréchet fibre -/

/-- The zero-lag joint law of the two trigger indicators, as counts over coincidence windows:
`n00` neither detector triggers, `n01` only L, `n10` only H, `n11` both. -/
structure Coupling where
  n00 : Nat
  n01 : Nat
  n10 : Nat
  n11 : Nat

namespace Coupling

/-- Number of coincidence windows. -/
def total (w : Coupling) : Nat := w.n00 + w.n01 + w.n10 + w.n11

/-- Single-detector trigger count in H. -/
def trigH (w : Coupling) : Nat := w.n10 + w.n11

/-- Single-detector trigger count in L. -/
def trigL (w : Coupling) : Nat := w.n01 + w.n11

end Coupling

/-- What a time slide is computed from: the window count and the two single-detector counts. -/
def slideData (w : Coupling) : Nat × Nat × Nat := (w.total, w.trigH, w.trigL)

/-- The law of `(X_H(t), X_L(t + kδ))`, `k ≠ 0`, for windows independent across time: the product
of the two marginals, as counts over `N²` pairs. -/
def productLaw : Nat × Nat × Nat → Coupling
  | (n, a, b) => ⟨(n - a) * (n - b), (n - a) * b, a * (n - b), a * b⟩

/-- Every time slide sees this law. -/
def slid (w : Coupling) : Coupling := productLaw (slideData w)

/-- The target: the number of zero-lag coincidences. -/
def zeroLag (w : Coupling) : Nat := w.n11

/-- Fréchet bounds: `max(0, mH + mL − N) ≤ n₁₁ ≤ min(mH, mL)`. -/
theorem frechet_bounds (w : Coupling) :
    zeroLag w ≤ w.trigH ∧ zeroLag w ≤ w.trigL ∧ w.trigH + w.trigL ≤ w.total + zeroLag w := by
  obtain ⟨a, b, c, d⟩ := w
  show d ≤ c + d ∧ d ≤ b + d ∧ c + d + (b + d) ≤ a + b + c + d + d
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Moving `t` windows from the two one-detector cells into the "neither" and "both" cells
leaves every time slide unchanged. -/
theorem frechet_move (a b c d t : Nat) :
    slideData ⟨a, b + t, c + t, d⟩ = slideData ⟨a + t, b, c, d + t⟩ := by
  show (a + (b + t) + (c + t) + d, c + t + d, b + t + d) =
    (a + t + b + c + (d + t), c + (d + t), b + (d + t))
  refine prod_mk_congr ?_ (prod_mk_congr ?_ ?_) <;> omega

/-- The zero-lag count is the coordinate of the slide fibre: slide data and zero-lag count
together determine the whole coupling. -/
theorem slide_fibre_coordinate : ∀ w w' : Coupling,
    slideData w = slideData w' → zeroLag w = zeroLag w' → w = w'
  | ⟨a, b, c, d⟩, ⟨a', b', c', d'⟩, h, h11 => by
    have hT : a + b + c + d = a' + b' + c' + d' := congrArg Prod.fst h
    have hH : c + d = c' + d' := congrArg (fun p => p.2.1) h
    have hL : b + d = b' + d' := congrArg (fun p => p.2.2) h
    have hd : d = d' := h11
    subst hd
    have hc : c = c' := Nat.add_right_cancel hH
    have hb : b = b' := Nat.add_right_cancel hL
    subst hc
    subst hb
    have ha : a = a' := Nat.add_right_cancel (Nat.add_right_cancel (Nat.add_right_cancel hT))
    subst ha
    rfl

/-- Time slides cannot classify the zero-lag coincidence count: four windows with two triggers
per detector, all disjoint against all coincident. -/
theorem slides_invalid_for_zeroLag : IsInvalidFor slideData zeroLag :=
  ⟨⟨0, 2, 2, 0⟩, ⟨2, 0, 0, 2⟩, by decide, by decide⟩

/-- No number of slides and no statistic of them repairs this: every slide is a copy of one
product law. -/
theorem slides_any_statistic_invalid {β : Sort u} (K : Nat) (S : List Coupling → β) :
    IsInvalidFor (fun w => S (List.replicate K (slid w))) zeroLag :=
  no_repair slideData _ zeroLag
    (fun _ _ h => congrArg (fun p => S (List.replicate K (productLaw p))) h)
    slides_invalid_for_zeroLag

/-- Every background built from the two single-detector trigger distributions (GstLAL's
non-coincident triggers, a trigger-rate model, a PSD) is blind in the same way. -/
theorem marginal_statistics_invalid {β : Sort u} (S : Nat × Nat → Nat × Nat → β) :
    IsInvalidFor (fun w : Coupling => S (w.total, w.trigH) (w.total, w.trigL)) zeroLag :=
  no_repair slideData _ zeroLag
    (fun w w' h => by
      have hT : w.total = w'.total := congrArg Prod.fst h
      have hH : w.trigH = w'.trigH := congrArg (fun p => p.2.1) h
      have hL : w.trigL = w'.trigL := congrArg (fun p => p.2.2) h
      show S (w.total, w.trigH) (w.total, w.trigL) = S (w'.total, w'.trigH) (w'.total, w'.trigL)
      rw [hT, hH, hL])
    slides_invalid_for_zeroLag

/-- The slide estimate of the zero-lag count is `mH·mL/N`; it is exact when `N·n₁₁ = mH·mL`. -/
def SlideExact (w : Coupling) : Prop := w.total * w.n11 = w.trigH * w.trigL

/-- On the independence locus the slide data determine the zero-lag count. -/
theorem slides_valid_on_independence :
    IsValidFor (fun w : {w : Coupling // SlideExact w ∧ 0 < w.total} => slideData w.1)
      (fun w => zeroLag w.1) := by
  intro ⟨w, hw, hN⟩ ⟨w', hw', _⟩ h
  have hT : w.total = w'.total := congrArg Prod.fst h
  have hH : w.trigH = w'.trigH := congrArg (fun p => p.2.1) h
  have hL : w.trigL = w'.trigL := congrArg (fun p => p.2.2) h
  have hw2 : w.total * w.n11 = w.trigH * w.trigL := hw
  have hw2' : w'.total * w'.n11 = w'.trigH * w'.trigL := hw'
  show w.n11 = w'.n11
  apply Nat.eq_of_mul_eq_mul_left hN
  rw [hw2, hT, hw2', hH, hL]

/-- An anchor repairs the background exactly when slide data and anchor together determine the
entire zero-lag coupling. -/
theorem anchor_repairs_iff {δ : Type} (A : Coupling → δ) :
    IsValidFor (fun w => (slideData w, A w)) zeroLag ↔
      ∀ w w', slideData w = slideData w' → A w = A w' → w = w' :=
  ⟨fun hv w w' h hA =>
      slide_fibre_coordinate w w' h (hv w w' ((ker_pair slideData A w w').mpr ⟨h, hA⟩)),
   fun hd w w' h =>
      congrArg zeroLag
        (hd w w' ((ker_pair slideData A w w').mp h).1 ((ker_pair slideData A w w').mp h).2)⟩

/-- In one fibre the slide estimate overshoots one coupling and undershoots another: it is a
bound in neither direction. -/
theorem slide_estimate_not_a_bound :
    ∃ w w' : Coupling, slideData w = slideData w' ∧
      w.total * w.n11 < w.trigH * w.trigL ∧ w'.trigH * w'.trigL < w'.total * w'.n11 :=
  ⟨⟨0, 2, 2, 0⟩, ⟨2, 0, 0, 2⟩, by decide, by decide, by decide⟩

/-- The two ends of the Fréchet interval: `m` triggers per detector among `r + 2m` windows, all
disjoint (`n₁₁ = 0`) or all coincident (`n₁₁ = m`). -/
theorem frechet_ends (r m : Nat) : slideData ⟨r, m, m, 0⟩ = slideData ⟨r + m, 0, 0, m⟩ := by
  show (r + m + m + 0, m + 0, m + 0) = (r + m + 0 + 0 + m, 0 + m, 0 + m)
  refine prod_mk_congr ?_ (prod_mk_congr ?_ ?_) <;> omega

/-- At the coincident end the zero-lag count is `N/m` times the slide estimate `m·m/N`:
`m · (N · m) = N · (m · m)`. -/
theorem coincident_end_excess (N m : Nat) : m * (N * m) = N * (m * m) := by
  rw [Nat.mul_left_comm]

/-- GW150914 scale: 16 days in 15 ms windows (`N = 92 160 000`), 16 loud triggers per detector.
The two ends share every slide, and at the coincident end `N·n₁₁ = 5 760 000 · mH·mL`. -/
theorem gw150914_frechet_scale :
    slideData ⟨92159968, 16, 16, 0⟩ = slideData ⟨92159984, 0, 0, 16⟩ ∧
    92160000 * 16 = 5760000 * (16 * 16) := by decide

/-- The slide ledger: 16 days = 1 382 400 s; 0.1 s steps give 13 824 000 distinct slides on a
16-day ring; their background is 19 110 297 600 000 s = 605 568 Julian years (reported:
608 000 years; with the trials factor 3, 1 in 202 666 → "1 in 203 000 years"). -/
theorem gw150914_slide_ledger :
    16 * 86400 = 1382400 ∧ 1382400 * 10 = 13824000 ∧
    13824000 * 1382400 = 19110297600000 ∧ 19110297600000 / 31557600 = 605568 ∧
    608000 / 3 = 202666 ∧ 1382400 * 1000 / 15 = 92160000 := by decide

/-! ## §2 Second moments and the Chebyshev fibre -/

/-- A symmetric noise law in one whitened frequency bin: atoms `(a, w)`, weight `w` at
amplitude `±a`. -/
abbrev NoiseLaw := List (Nat × Nat)

/-- Total weight. -/
def mass : NoiseLaw → Nat
  | [] => 0
  | (_, w) :: L => w + mass L

/-- Second-moment numerator `Σ w·a²`: the PSD of the bin is `power / mass`. -/
def power : NoiseLaw → Nat
  | [] => 0
  | (a, w) :: L => w * (a * a) + power L

/-- Weight at amplitude `≥ t`. -/
def tail (t : Nat) : NoiseLaw → Nat
  | [] => 0
  | (a, w) :: L => (if t ≤ a then w else 0) + tail t L

/-- What the PSD keeps of a bin. -/
def psd (L : NoiseLaw) : Nat × Nat := (mass L, power L)

/-- Chebyshev: `t² · tail ≤ Σ w·a²`. -/
theorem chebyshev (t : Nat) : ∀ L : NoiseLaw, t * t * tail t L ≤ power L
  | [] => Nat.le_of_eq (Nat.mul_zero (t * t))
  | (a, w) :: L => by
    show t * t * ((if t ≤ a then w else 0) + tail t L) ≤ w * (a * a) + power L
    rw [Nat.mul_add]
    refine Nat.add_le_add ?_ (chebyshev t L)
    by_cases h : t ≤ a
    · rw [if_pos h, Nat.mul_comm w (a * a)]
      exact Nat.mul_le_mul (Nat.mul_le_mul h h) (Nat.le_refl w)
    · rw [if_neg h, Nat.mul_zero]
      exact Nat.zero_le _

/-- Unit variance, threshold `5σ`: the PSD cannot classify the tail weight. -/
theorem psd_invalid_for_tail : IsInvalidFor psd (tail 5) :=
  ⟨[(1, 50)], [(0, 48), (5, 2)], by decide, by decide⟩

/-- At `5.1σ` (σ = 10 units, threshold 51): two laws with the same PSD `(2601, 260100)` have tail
weights `0` and `100` out of `2601`, and the second attains Chebyshev's bound. -/
theorem chebyshev_interval_5p1 :
    psd [(10, 2601)] = psd [(0, 2501), (51, 100)] ∧
    tail 51 [(10, 2601)] = 0 ∧ tail 51 [(0, 2501), (51, 100)] = 100 ∧
    51 * 51 * tail 51 [(0, 2501), (51, 100)] = power [(0, 2501), (51, 100)] := by decide

/-- No law with that PSD exceeds `100/2601`: the fibre's tail range is exactly `[0, 100/2601]`. -/
theorem tail_max_5p1 (L : NoiseLaw) (h : power L = 260100) : tail 51 L ≤ 100 := by
  have hc := chebyshev 51 L
  rw [h] at hc
  omega

/-! ## §3 Equal-weight averaging -/

/-- Two waveform models' posteriors on a two-point grid (equal sample counts) and their evidences. -/
structure TwoModel where
  pE : Nat × Nat
  pP : Nat × Nat
  zE : Nat
  zP : Nat

/-- LIGO's "Overall": "We combine the posterior samples of both distributions with equal weight". -/
def overall (s : TwoModel) : Nat × Nat := (s.pE.1 + s.pP.1, s.pE.2 + s.pP.2)

/-- Evidence-weighted model averaging with equal prior odds. -/
def bma (s : TwoModel) : Nat × Nat :=
  (s.zE * s.pE.1 + s.zP * s.pP.1, s.zE * s.pE.2 + s.zP * s.pP.2)

/-- The equal-weight combination cannot see the evidence ratio (witness ratio `5`; the published
log-evidences 288.7 and 290.3 give `e^1.6 ≈ 4.95`). -/
theorem overall_invalid_for_bma : IsInvalidFor overall bma :=
  ⟨⟨(1, 0), (0, 1), 1, 1⟩, ⟨(1, 0), (0, 1), 1, 5⟩, rfl, by decide⟩

/-- The two averaged posteriors differ by more than a rescaling: odds `1 : 1` against `1 : 5`. -/
theorem bma_witness_not_rescaled : ¬ SameRatio 1 1 1 5 := by
  show ¬ ((1 : Int) * 5 = 1 * 1)
  decide

/-- Evidence-weighted minus equal-weighted posterior mean, cross-multiplied by `2(Z_E + Z_P)`:
(evidence asymmetry) × (inter-model gap). -/
theorem bma_shift (zE zP mE mP : Int) :
    2 * (zE * mE + zP * mP) - (zE + zP) * (mE + mP) = (zP - zE) * (mP - mE) := by
  simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul] <;> omega

/-- Source-frame `m₁` medians (units 0.1 M⊙): EOBNR 363, IMRPhenom 353. With evidence ratio 5 the
evidence-weighted centre lies `40/12 ≈ 3.3` units (0.33 M⊙) below the equal-weight centre. -/
theorem gw150914_m1_bma_shift :
    2 * (1 * 363 + 5 * 353) - (1 + 5) * (363 + 353) = (-40 : Int) ∧
    (5 - 1) * (353 - 363) = (-40 : Int) := by decide

/-- LIGO's waveform-systematics estimate at a credible-interval edge, times two:
`2σ²_sys = (X_E − X_O)² + (X_P − X_O)²`. -/
def sigmaSys2 (xE xP xO : Int) : Int := (xE - xO) * (xE - xO) + (xP - xO) * (xP - xO)

/-- A common shift of both models moves all three edges together and leaves `σ_sys` unchanged. -/
theorem sigmaSys2_blind (xE xP xO g : Int) :
    sigmaSys2 (xE + g) (xP + g) (xO + g) = sigmaSys2 xE xP xO := by
  unfold sigmaSys2
  rw [Int.add_sub_add_right, Int.add_sub_add_right]

/-- Hence `σ_sys` cannot classify a common error. -/
theorem sigmaSys2_invalid_for_common_error (xE xP xO : Int) :
    IsInvalidFor (fun g : Int => sigmaSys2 (xE + g) (xP + g) (xO + g)) (fun g => g) :=
  ⟨0, 1, (sigmaSys2_blind xE xP xO 0).trans (sigmaSys2_blind xE xP xO 1).symm, by decide⟩

/-- A posterior summary that moves with its samples (every quantile, the median, the mean), on
nonempty sample lists. -/
def ShiftEquivariant (Q : List Int → Int) : Prop :=
  ∀ (x : Int) (L : List Int) (g : Int), Q ((x :: L).map (· + g)) = Q (x :: L) + g

/-- The first sample is such a summary, so the hypothesis is satisfiable. -/
def firstSample : List Int → Int
  | [] => 0
  | x :: _ => x

theorem firstSample_equivariant : ShiftEquivariant firstSample :=
  fun _ _ _ => rfl

/-- Computed from shifted samples exactly as published (Overall = both sample lists with equal
weight), `σ_sys` is identical for every common error `g`. -/
theorem sigmaSys_samples_blind (Q : List Int → Int) (hQ : ShiftEquivariant Q)
    (e p : Int) (E P : List Int) (g : Int) :
    sigmaSys2 (Q ((e :: E).map (· + g))) (Q ((p :: P).map (· + g)))
        (Q ((e :: E ++ p :: P).map (· + g))) =
      sigmaSys2 (Q (e :: E)) (Q (p :: P)) (Q (e :: E ++ p :: P)) := by
  have h3 : Q ((e :: E ++ p :: P).map (· + g)) = Q (e :: E ++ p :: P) + g :=
    hQ e (E ++ p :: P) g
  rw [hQ e E g, hQ p P g, h3]
  exact sigmaSys2_blind _ _ _ g

theorem sigmaSys_samples_invalid (Q : List Int → Int) (hQ : ShiftEquivariant Q)
    (e p : Int) (E P : List Int) :
    IsInvalidFor
      (fun g : Int => sigmaSys2 (Q ((e :: E).map (· + g))) (Q ((p :: P).map (· + g)))
        (Q ((e :: E ++ p :: P).map (· + g))))
      (fun g => g) :=
  ⟨0, 1, (sigmaSys_samples_blind Q hQ e p E P 0).trans
    (sigmaSys_samples_blind Q hQ e p E P 1).symm, by decide⟩

/-- Table I, source-frame `m₁` (units 0.1 M⊙): upper edges 416, 405, 411 and lower edges 318,
319, 319 give `2σ²_sys = 61` and `1`; `1.64σ_sys` rounds to the published `±0.9` and `±0.1`; any
common shift up to 10 M⊙ leaves the upper value unchanged. -/
theorem tableI_m1_sigmaSys :
    sigmaSys2 416 405 411 = 61 ∧ sigmaSys2 318 319 319 = 1 ∧
    85 * 85 * 200 < 164 * 164 * 61 ∧ 164 * 164 * 61 < 95 * 95 * 200 ∧
    5 * 5 * 200 < 164 * 164 * 1 ∧ 164 * 164 * 1 < 15 * 15 * 200 ∧
    (∀ g ∈ List.range 101,
      sigmaSys2 (416 + Int.ofNat g) (405 + Int.ofNat g) (411 + Int.ofNat g) = 61) := by
  decide

/-! ## §4 Finite anchors: a sharp threshold -/

/-- Horner evaluation of the coefficient list `[c₀, c₁, …]` (constant term first). -/
def peval : List Int → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * peval cs x

/-- Coefficientwise sum. -/
def padd : List Int → List Int → List Int
  | [], q => q
  | c :: p, [] => c :: p
  | c :: p, d :: q => (c + d) :: padd p q

/-- Multiplication by a constant. -/
def pscale (a : Int) : List Int → List Int
  | [] => []
  | c :: p => (a * c) :: pscale a p

/-- Synthetic division by `x − a`: the quotient. -/
def pquot (a : Int) : List Int → List Int
  | [] => []
  | _ :: p => padd p (pscale a (pquot a p))

/-- The node polynomial `∏ (x − aᵢ)`. -/
def nodePoly : List Int → List Int
  | [] => [1]
  | a :: l => padd (0 :: nodePoly l) (pscale (-a) (nodePoly l))

theorem peval_padd : ∀ (p q : List Int) (x : Int), peval (padd p q) x = peval p x + peval q x
  | [], _, _ => (Int.zero_add _).symm
  | _ :: _, [], _ => (Int.add_zero _).symm
  | c :: p, d :: q, x => by
    show (c + d) + x * peval (padd p q) x = (c + x * peval p x) + (d + x * peval q x)
    rw [peval_padd p q x, Int.mul_add]
    omega

theorem peval_pscale (a : Int) : ∀ (p : List Int) (x : Int), peval (pscale a p) x = a * peval p x
  | [], _ => (Int.mul_zero a).symm
  | c :: p, x => by
    show a * c + x * peval (pscale a p) x = a * (c + x * peval p x)
    rw [peval_pscale a p x, Int.mul_add, Int.mul_left_comm]

/-- Synthetic division: `p(x) = p(a) + (x − a)·q(x)`. -/
theorem peval_pquot (a : Int) : ∀ (p : List Int) (x : Int),
    peval p x = peval p a + (x - a) * peval (pquot a p) x
  | [], x => by
    show (0 : Int) = 0 + (x - a) * 0
    rw [Int.mul_zero, Int.add_zero]
  | c :: p, x => by
    show c + x * peval p x =
      (c + a * peval p a) + (x - a) * peval (padd p (pscale a (pquot a p))) x
    rw [peval_padd, peval_pscale, peval_pquot a p x]
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_assoc, Int.mul_comm,
      Int.mul_left_comm] <;> omega

theorem length_padd_le : ∀ (p q : List Int) (k : Nat),
    p.length ≤ k → q.length ≤ k → (padd p q).length ≤ k
  | [], _, _, _, hq => hq
  | _ :: _, [], _, hp, _ => hp
  | _ :: p, _ :: q, k, hp, hq => by
    cases k with
    | zero => exact absurd hp (Nat.not_succ_le_zero _)
    | succ k =>
      exact Nat.succ_le_succ
        (length_padd_le p q k (Nat.le_of_succ_le_succ hp) (Nat.le_of_succ_le_succ hq))

theorem length_pscale (a : Int) : ∀ p : List Int, (pscale a p).length = p.length
  | [] => rfl
  | _ :: p => congrArg (· + 1) (length_pscale a p)

theorem length_pquot_le_self (a : Int) : ∀ p : List Int, (pquot a p).length ≤ p.length
  | [] => Nat.le_refl 0
  | _ :: p => by
    show (padd p (pscale a (pquot a p))).length ≤ p.length + 1
    apply Nat.le_succ_of_le
    apply length_padd_le p _ p.length (Nat.le_refl _)
    rw [length_pscale]
    exact length_pquot_le_self a p

theorem length_pquot_cons (a c : Int) (p : List Int) : (pquot a (c :: p)).length ≤ p.length := by
  show (padd p (pscale a (pquot a p))).length ≤ p.length
  apply length_padd_le p _ p.length (Nat.le_refl _)
  rw [length_pscale]
  exact length_pquot_le_self a p

theorem length_pquot_pred (a : Int) (p : List Int) (k : Nat) (hp : p.length ≤ k + 1) :
    (pquot a p).length ≤ k := by
  cases p with
  | nil => exact Nat.zero_le k
  | cons c p => exact Nat.le_trans (length_pquot_cons a c p) (Nat.le_of_succ_le_succ hp)

/-- Pairwise distinct nodes. -/
def Distinct : List Int → Prop
  | [] => True
  | a :: l => a ∉ l ∧ Distinct l

/-- A polynomial with at most `k` coefficients vanishing at `k` distinct nodes vanishes everywhere. -/
theorem vanish_everywhere : ∀ (nodes : List Int), Distinct nodes → ∀ (p : List Int),
    p.length ≤ nodes.length → (∀ a ∈ nodes, peval p a = 0) → ∀ x, peval p x = 0
  | [], _, p, hp, _, _ => by
    cases p with
    | nil => rfl
    | cons c p => exact absurd hp (Nat.not_succ_le_zero _)
  | a :: rest, hd, p, hp, hz, x => by
    have hd' : a ∉ rest ∧ Distinct rest := hd
    have ha : peval p a = 0 := hz a (List.Mem.head _)
    have hq : ∀ b ∈ rest, peval (pquot a p) b = 0 := by
      intro b hb
      have hb0 : peval p b = 0 := hz b (List.Mem.tail _ hb)
      have hba : b - a ≠ 0 := by
        intro h
        have hab : b = a := by omega
        exact hd'.1 (hab ▸ hb)
      rw [peval_pquot a p b, ha, Int.zero_add] at hb0
      exact Int.eq_of_mul_eq_mul_left hba (hb0.trans (Int.mul_zero _).symm)
    have hlen : (pquot a p).length ≤ rest.length := length_pquot_pred a p rest.length hp
    have hrest := vanish_everywhere rest hd'.2 (pquot a p) hlen hq x
    rw [peval_pquot a p x, ha, hrest, Int.mul_zero, Int.zero_add]

theorem map_eq_of_mem {α β : Type} (f g : α → β) :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.map f = l.map g
  | [], _ => rfl
  | a :: l, h =>
    cons_congr (h a (List.Mem.head _))
      (map_eq_of_mem f g l (fun b hb => h b (List.Mem.tail _ hb)))

theorem eq_of_map_eq {α β : Type} (f g : α → β) :
    ∀ l : List α, l.map f = l.map g → ∀ a ∈ l, f a = g a
  | [], _, _, ha => nomatch ha
  | b :: l, h, a, ha => by
    have hh : f b = g b ∧ l.map f = l.map g := List.cons.inj h
    cases ha with
    | head => exact hh.1
    | tail _ ha' => exact eq_of_map_eq f g l hh.2 a ha'

/-- Common-mode errors of degree `< k`: coefficient lists of length `≤ k`. -/
abbrev PolyLe (k : Nat) := {p : List Int // p.length ≤ k}

/-- Difference of two coefficient lists. -/
def psub (p q : List Int) : List Int := padd p (pscale (-1) q)

/-- `k` distinct anchor nodes identify every common-mode error of degree `< k`. -/
theorem anchors_valid (nodes : List Int) (hd : Distinct nodes) (θ : Int) :
    IsValidFor (fun p : PolyLe nodes.length => nodes.map (peval p.1)) (fun p => peval p.1 θ) := by
  intro p q hpq
  have hpq' : nodes.map (peval p.1) = nodes.map (peval q.1) := hpq
  have hz : ∀ a ∈ nodes, peval (psub p.1 q.1) a = 0 := by
    intro a ha
    have hpa := eq_of_map_eq _ _ nodes hpq' a ha
    unfold psub
    rw [peval_padd, peval_pscale]
    omega
  have hlen : (psub p.1 q.1).length ≤ nodes.length :=
    length_padd_le _ _ _ p.2 (by rw [length_pscale]; exact q.2)
  have h0 := vanish_everywhere nodes hd (psub p.1 q.1) hlen hz θ
  unfold psub at h0
  rw [peval_padd, peval_pscale] at h0
  show peval p.1 θ = peval q.1 θ
  omega

theorem peval_nodePoly_cons (a : Int) (l : List Int) (x : Int) :
    peval (nodePoly (a :: l)) x = (x - a) * peval (nodePoly l) x := by
  show peval (padd (0 :: nodePoly l) (pscale (-a) (nodePoly l))) x = (x - a) * peval (nodePoly l) x
  rw [peval_padd, peval_pscale]
  show (0 + x * peval (nodePoly l) x) + -a * peval (nodePoly l) x = (x - a) * peval (nodePoly l) x
  rw [Int.zero_add, Int.sub_mul, Int.sub_eq_add_neg, Int.neg_mul]

theorem nodePoly_zero : ∀ (l : List Int) (a : Int), a ∈ l → peval (nodePoly l) a = 0
  | [], _, h => nomatch h
  | b :: l, a, h => by
    rw [peval_nodePoly_cons]
    cases h with
    | head => rw [Int.sub_self, Int.zero_mul]
    | tail _ h' => rw [nodePoly_zero l a h', Int.mul_zero]

theorem nodePoly_ne_zero : ∀ (l : List Int) (x : Int), x ∉ l → peval (nodePoly l) x ≠ 0
  | [], x, _ => by
    show (1 : Int) + x * 0 ≠ 0
    rw [Int.mul_zero, Int.add_zero]
    decide
  | b :: l, x, h => by
    rw [peval_nodePoly_cons]
    have hxb : x - b ≠ 0 := by
      intro e
      have hx : x = b := by omega
      exact h (by rw [hx]; exact List.Mem.head _)
    have hrest : peval (nodePoly l) x ≠ 0 := nodePoly_ne_zero l x (fun e => h (List.Mem.tail _ e))
    intro e
    exact hrest (Int.eq_of_mul_eq_mul_left hxb (e.trans (Int.mul_zero _).symm))

/-- The node polynomial evaluates to the product `∏ (x − aᵢ)`. -/
theorem peval_nodePoly : ∀ (l : List Int) (x : Int),
    peval (nodePoly l) x = l.foldr (fun b acc => (x - b) * acc) 1
  | [], x => by
    show (1 : Int) + x * 0 = 1
    rw [Int.mul_zero, Int.add_zero]
  | a :: l, x => by
    show peval (nodePoly (a :: l)) x = (x - a) * l.foldr (fun b acc => (x - b) * acc) 1
    rw [peval_nodePoly_cons, peval_nodePoly l x]

theorem length_nodePoly : ∀ l : List Int, (nodePoly l).length ≤ l.length + 1
  | [] => Nat.le_refl 1
  | a :: l => by
    show (padd (0 :: nodePoly l) (pscale (-a) (nodePoly l))).length ≤ l.length + 1 + 1
    apply length_padd_le
    · exact Nat.succ_le_succ (length_nodePoly l)
    · rw [length_pscale]
      exact Nat.le_succ_of_le (length_nodePoly l)

/-- One degree more and the same anchors fail: the node polynomial is invisible to them. -/
theorem anchors_invalid_one_degree_up (nodes : List Int) (θ : Int) (hθ : θ ∉ nodes) :
    IsInvalidFor (fun p : PolyLe (nodes.length + 1) => nodes.map (peval p.1))
      (fun p => peval p.1 θ) :=
  ⟨⟨[], Nat.zero_le _⟩, ⟨nodePoly nodes, length_nodePoly nodes⟩,
   map_eq_of_mem _ _ nodes (fun a ha => (nodePoly_zero nodes a ha).symm),
   fun h => nodePoly_ne_zero nodes θ hθ h.symm⟩

/-- The sharp threshold: `k` anchors are valid for degree `< k` and invalid for degree `k`. -/
theorem anchor_threshold (nodes : List Int) (hd : Distinct nodes) (θ : Int) (hθ : θ ∉ nodes) :
    IsValidFor (fun p : PolyLe nodes.length => nodes.map (peval p.1)) (fun p => peval p.1 θ) ∧
    IsInvalidFor (fun p : PolyLe (nodes.length + 1) => nodes.map (peval p.1))
      (fun p => peval p.1 θ) :=
  ⟨anchors_valid nodes hd θ, anchors_invalid_one_degree_up nodes θ hθ⟩

/-- Without a declared error class, no finite anchor set certifies the error off its nodes. -/
theorem finite_anchors_invalid (nodes : List Int) (θ : Int) (hθ : θ ∉ nodes) :
    IsInvalidFor (fun g : Int → Int => nodes.map g) (fun g => g θ) :=
  ⟨fun _ => 0, peval (nodePoly nodes),
   map_eq_of_mem _ _ nodes (fun a ha => (nodePoly_zero nodes a ha).symm),
   fun h => nodePoly_ne_zero nodes θ hθ h.symm⟩

/-- What both validation routes see of the two models' error functions `(e_E, e_P)`: every
inter-model comparison on a finite list `P` of parameters, and both errors at the NR nodes. -/
def validationView (P nodes : List Int) (e : (Int → Int) × (Int → Int)) :
    List Int × List (Int × Int) :=
  (P.map (fun θ => e.1 θ - e.2 θ), nodes.map (fun θ => (e.1 θ, e.2 θ)))

/-- Double blindness: a common error equal to the node polynomial passes every comparison and
every shared NR node, and is nonzero at every other parameter. -/
theorem double_blind (P nodes : List Int) (θ : Int) (hθ : θ ∉ nodes) :
    IsInvalidFor (validationView P nodes) (fun e => e.1 θ) := by
  refine ⟨(fun _ => 0, fun _ => 0), (peval (nodePoly nodes), peval (nodePoly nodes)), ?_, ?_⟩
  · show (P.map (fun _ => (0 : Int) - 0), nodes.map (fun _ => ((0 : Int), (0 : Int)))) =
      (P.map (fun t => peval (nodePoly nodes) t - peval (nodePoly nodes) t),
        nodes.map (fun t => (peval (nodePoly nodes) t, peval (nodePoly nodes) t)))
    refine prod_mk_congr (map_eq_of_mem _ _ P (fun a _ => ?_))
      (map_eq_of_mem _ _ nodes (fun a ha => ?_))
    · show (0 : Int) - 0 = peval (nodePoly nodes) a - peval (nodePoly nodes) a
      rw [Int.sub_self, Int.sub_self]
    · show ((0 : Int), (0 : Int)) = (peval (nodePoly nodes) a, peval (nodePoly nodes) a)
      rw [nodePoly_zero nodes a ha]
  · exact fun h => nodePoly_ne_zero nodes θ hθ h.symm

/-- Nineteen nodes `1, …, 19` (IMRPhenomD was calibrated to 19 hybrids): the node polynomial
vanishes at node 7 and equals `19! = 121 645 100 408 832 000` at `θ = 20`. -/
theorem nineteen_nodes :
    peval (nodePoly [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]) 7 = 0 ∧
    peval (nodePoly [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]) 20 =
      121645100408832000 := by
  rw [peval_nodePoly, peval_nodePoly]
  decide

/-! ## §5 Rank one: networks and polarization -/

/-- A two-detector response matrix: rows `(F₊, F×)` for H and L. -/
abbrev Resp := (Int × Int) × (Int × Int)

/-- The two detector outputs for polarization amplitudes `(h₊, h×)`. -/
def respond (F : Resp) (h : Int × Int) : Int × Int :=
  (F.1.1 * h.1 + F.1.2 * h.2, F.2.1 * h.1 + F.2.2 * h.2)

/-- The response determinant. -/
def det (F : Resp) : Int := F.1.1 * F.2.2 - F.1.2 * F.2.1

theorem adj_fst (a b c d x y : Int) :
    d * (a * x + b * y) - b * (c * x + d * y) = (a * d - b * c) * x := by
  simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_assoc, Int.mul_comm,
    Int.mul_left_comm] <;> omega

theorem adj_snd (a b c d x y : Int) :
    a * (c * x + d * y) - c * (a * x + b * y) = (a * d - b * c) * y := by
  simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_assoc, Int.mul_comm,
    Int.mul_left_comm] <;> omega

theorem respond_zero (F : Resp) : respond F (0, 0) = (0, 0) := by
  show (F.1.1 * 0 + F.1.2 * 0, F.2.1 * 0 + F.2.2 * 0) = (0, 0)
  simp only [Int.mul_zero, Int.add_zero]

/-- A nonzero determinant makes the network faithful. -/
theorem respond_faithful_of_det (F : Resp) (hd : det F ≠ 0) :
    IsValidFor (respond F) (fun h => h) := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := F
  intro ⟨x, y⟩ ⟨x', y'⟩ heq
  have e1 : a * x + b * y = a * x' + b * y' := congrArg Prod.fst heq
  have e2 : c * x + d * y = c * x' + d * y' := congrArg Prod.snd heq
  have hd' : a * d - b * c ≠ 0 := hd
  have hx : (a * d - b * c) * x = (a * d - b * c) * x' := by
    rw [← adj_fst a b c d x y, ← adj_fst a b c d x' y', e1, e2]
  have hy : (a * d - b * c) * y = (a * d - b * c) * y' := by
    rw [← adj_snd a b c d x y, ← adj_snd a b c d x' y', e1, e2]
  exact prod_mk_congr (Int.eq_of_mul_eq_mul_left hd' hx) (Int.eq_of_mul_eq_mul_left hd' hy)

/-- A zero determinant leaves a nonzero polarization the network cannot see. -/
theorem respond_kernel_of_det_zero (F : Resp) (hd : det F = 0) :
    ∃ h : Int × Int, h ≠ (0, 0) ∧ respond F h = (0, 0) := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := F
  have hd' : a * d - b * c = 0 := hd
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨ha, hb⟩ := hab
    subst ha
    subst hb
    by_cases hcd : c = 0 ∧ d = 0
    · obtain ⟨hc, hd0⟩ := hcd
      subst hc
      subst hd0
      exact ⟨(1, 0), by decide, by decide⟩
    · refine ⟨(d, -c), fun h => hcd ⟨?_, ?_⟩, ?_⟩
      · have h2 : -c = 0 := congrArg Prod.snd h
        omega
      · exact congrArg Prod.fst h
      · show (0 * d + 0 * -c, c * d + d * -c) = (0, 0)
        rw [Int.zero_mul, Int.zero_mul, Int.add_zero, Int.mul_neg, Int.mul_comm d c,
          Int.add_right_neg]
  · refine ⟨(b, -a), fun h => hab ⟨?_, ?_⟩, ?_⟩
    · have h2 : -a = 0 := congrArg Prod.snd h
      omega
    · exact congrArg Prod.fst h
    · show (a * b + b * -a, c * b + d * -a) = (0, 0)
      have h2 : c * b + d * -a = 0 := by
        rw [Int.mul_neg, Int.mul_comm c b, Int.mul_comm d a]
        omega
      rw [h2, Int.mul_neg, Int.mul_comm b a, Int.add_right_neg]

/-- A two-detector network determines `(h₊, h×)` exactly when its determinant is nonzero. -/
theorem network_valid_iff_det (F : Resp) : IsValidFor (respond F) (fun h => h) ↔ det F ≠ 0 :=
  ⟨fun hv hd => by
      obtain ⟨h, hne, hz⟩ := respond_kernel_of_det_zero F hd
      exact hne (hv h (0, 0) (hz.trans (respond_zero F).symm)),
   respond_faithful_of_det F⟩

/-- Co-aligned detectors (L responds as `−1` times H) have determinant zero. -/
theorem coaligned_det (a b : Int) : det ((a, b), (-a, -b)) = 0 := by
  show a * -b - b * -a = 0
  rw [Int.mul_neg, Int.mul_neg, Int.mul_comm b a, Int.sub_self]

theorem coaligned_not_valid (a b : Int) :
    ¬ IsValidFor (respond ((a, b), (-a, -b))) (fun h => h) :=
  fun hv => (network_valid_iff_det _).mp hv (coaligned_det a b)

/-- Three polarization amplitudes `(h₊, h×, h_b)`: two tensor, one breathing scalar. -/
abbrev Pol3 := Int × Int × Int

def dot3 (r h : Pol3) : Int := r.1 * h.1 + r.2.1 * h.2.1 + r.2.2 * h.2.2

def respond3 (r s h : Pol3) : Int × Int := (dot3 r h, dot3 s h)

def cross3 (r s : Pol3) : Pol3 :=
  (r.2.1 * s.2.2 - r.2.2 * s.2.1, r.2.2 * s.1 - r.1 * s.2.2, r.1 * s.2.1 - r.2.1 * s.1)

theorem dot_cross_left (r s : Pol3) : dot3 r (cross3 r s) = 0 := by
  obtain ⟨r1, r2, r3⟩ := r
  obtain ⟨s1, s2, s3⟩ := s
  show r1 * (r2 * s3 - r3 * s2) + r2 * (r3 * s1 - r1 * s3) + r3 * (r1 * s2 - r2 * s1) = 0
  simp only [Int.mul_sub, Int.sub_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] <;> omega

theorem dot_cross_right (r s : Pol3) : dot3 s (cross3 r s) = 0 := by
  obtain ⟨r1, r2, r3⟩ := r
  obtain ⟨s1, s2, s3⟩ := s
  show s1 * (r2 * s3 - r3 * s2) + s2 * (r3 * s1 - r1 * s3) + s3 * (r1 * s2 - r2 * s1) = 0
  simp only [Int.mul_sub, Int.sub_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] <;> omega

theorem dot_cross_swap (r s e : Pol3) : dot3 s (cross3 r e) = - dot3 e (cross3 r s) := by
  obtain ⟨r1, r2, r3⟩ := r
  obtain ⟨s1, s2, s3⟩ := s
  obtain ⟨e1, e2, e3⟩ := e
  show s1 * (r2 * e3 - r3 * e2) + s2 * (r3 * e1 - r1 * e3) + s3 * (r1 * e2 - r2 * e1) =
    -(e1 * (r2 * s3 - r3 * s2) + e2 * (r3 * s1 - r1 * s3) + e3 * (r1 * s2 - r2 * s1))
  simp only [Int.mul_sub, Int.sub_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] <;> omega

theorem kernel_of_cross_zero (r s e : Pol3) (h : cross3 r s = (0, 0, 0)) :
    respond3 r s (cross3 r e) = (0, 0) := by
  show (dot3 r (cross3 r e), dot3 s (cross3 r e)) = (0, 0)
  rw [dot_cross_left, dot_cross_swap, h]
  show ((0 : Int), -(e.1 * 0 + e.2.1 * 0 + e.2.2 * 0)) = (0, 0)
  simp only [Int.mul_zero, Int.add_zero, Int.neg_zero]

theorem cross_basis (r : Pol3) (hr : r ≠ (0, 0, 0)) :
    cross3 r (1, 0, 0) ≠ (0, 0, 0) ∨ cross3 r (0, 1, 0) ≠ (0, 0, 0) := by
  obtain ⟨r1, r2, r3⟩ := r
  by_cases h2 : r2 = 0
  · by_cases h3 : r3 = 0
    · right
      intro hc
      have h1 : r1 * 1 - r2 * 0 = 0 := congrArg (fun v => v.2.2) hc
      apply hr
      subst h2
      subst h3
      have h0 : r1 = 0 := by omega
      subst h0
      rfl
    · left
      intro hc
      have h : r3 * 1 - r1 * 0 = 0 := congrArg (fun v => v.2.1) hc
      exact h3 (by omega)
  · left
    intro hc
    have h : r1 * 0 - r2 * 1 = 0 := congrArg (fun v => v.2.2) hc
    exact h2 (by omega)

/-- Two detectors never determine three polarization amplitudes, whatever their orientation. -/
theorem two_detectors_three_modes (r s : Pol3) :
    ∃ h : Pol3, h ≠ (0, 0, 0) ∧ respond3 r s h = (0, 0) := by
  by_cases hrs : cross3 r s = (0, 0, 0)
  · by_cases hr : r = (0, 0, 0)
    · subst hr
      by_cases hs : s = (0, 0, 0)
      · subst hs
        exact ⟨(1, 0, 0), by decide, by decide⟩
      · have hz : ∀ e : Pol3, respond3 (0, 0, 0) s (cross3 s e) = (0, 0) := by
          intro e
          show (dot3 (0, 0, 0) (cross3 s e), dot3 s (cross3 s e)) = (0, 0)
          rw [dot_cross_left]
          show ((0 : Int) * (cross3 s e).1 + 0 * (cross3 s e).2.1 + 0 * (cross3 s e).2.2,
            (0 : Int)) = (0, 0)
          simp only [Int.zero_mul, Int.add_zero]
        rcases cross_basis s hs with h1 | h1
        · exact ⟨_, h1, hz _⟩
        · exact ⟨_, h1, hz _⟩
    · rcases cross_basis r hr with h1 | h1
      · exact ⟨_, h1, kernel_of_cross_zero r s _ hrs⟩
      · exact ⟨_, h1, kernel_of_cross_zero r s _ hrs⟩
  · refine ⟨cross3 r s, hrs, ?_⟩
    show (dot3 r (cross3 r s), dot3 s (cross3 r s)) = (0, 0)
    rw [dot_cross_left, dot_cross_right]

theorem two_detectors_invalid_for_polarization (r s : Pol3) :
    IsInvalidFor (respond3 r s) (fun h => h) := by
  obtain ⟨h, hne, hz⟩ := two_detectors_three_modes r s
  refine ⟨h, (0, 0, 0), ?_, hne⟩
  show respond3 r s h = respond3 r s (0, 0, 0)
  rw [hz]
  show ((0 : Int), (0 : Int)) =
    (r.1 * 0 + r.2.1 * 0 + r.2.2 * 0, s.1 * 0 + s.2.1 * 0 + s.2.2 * 0)
  simp only [Int.mul_zero, Int.add_zero]

/-! ### Perfect association is constant on the polarization fibre -/

theorem centered_congr (A : List Nat) (f f' g g' : Nat → Int)
    (hf : ∀ s, f s = f' s) (hg : ∀ s, g s = g' s) :
    PerfectAssociation.centered A f g = PerfectAssociation.centered A f' g' := by
  have hx : PerfectAssociation.cross A f g = PerfectAssociation.cross A f' g' :=
    PerfectAssociation.total_congr A (fun a => f a * g a) (fun a => f' a * g' a)
      (fun a => by rw [hf a, hg a])
  have h1 : PerfectAssociation.total A f = PerfectAssociation.total A f' :=
    PerfectAssociation.total_congr A f f' hf
  have h2 : PerfectAssociation.total A g = PerfectAssociation.total A g' :=
    PerfectAssociation.total_congr A g g' hg
  unfold PerfectAssociation.centered
  simp only [hx, h1, h2]

/-- Proportional streams (`g = k·f`, `k > 0`, `f` varying) pass the exact Pearson certificate. -/
theorem proportional_streams_perfect (A : List Nat) (f g : Nat → Int) (k : Int) (hk : 0 < k)
    (hg : ∀ s, g s = k * f s) (hV : 0 < PerfectAssociation.spread A f) :
    PerfectAssociation.COR A f g = true := by
  have hf1 : ∀ s, f s = 1 * f s + 0 := fun s => by rw [Int.one_mul, Int.add_zero]
  have hg1 : ∀ s, g s = k * f s + 0 := fun s => by rw [Int.add_zero]; exact hg s
  have hc : PerfectAssociation.centered A f g = 1 * k * PerfectAssociation.centered A f f := by
    rw [centered_congr A f (fun s => 1 * f s + 0) g (fun s => k * f s + 0) hf1 hg1,
      PerfectAssociation.centered_affine]
  have hs : PerfectAssociation.spread A g = k * k * PerfectAssociation.centered A f f := by
    show PerfectAssociation.centered A g g = k * k * PerfectAssociation.centered A f f
    rw [centered_congr A g (fun s => k * f s + 0) g (fun s => k * f s + 0) hg1 hg1,
      PerfectAssociation.centered_affine]
  have hV' : 0 < PerfectAssociation.centered A f f := hV
  unfold PerfectAssociation.COR
  apply decide_eq_true
  rw [hc, hs, show PerfectAssociation.spread A f = PerfectAssociation.centered A f f from rfl]
  refine ⟨Int.mul_pos (by rw [Int.one_mul]; exact hk) hV', ?_⟩
  simp only [Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-- Proportional streams have rank one: every 2×2 minor of their differences vanishes. -/
theorem proportional_minors_vanish (f g : Nat → Int) (k : Int) (hg : ∀ s, g s = k * f s)
    (s t u v : Nat) : (f s - f t) * (g u - g v) = (g s - g t) * (f u - f v) := by
  rw [hg s, hg t, hg u, hg v, ← Int.mul_sub, ← Int.mul_sub]
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem coaligned_streams (a b k : Int) (hp hx : Nat → Int) (s : Nat) :
    (k * a) * hp s + (k * b) * hx s = k * (a * hp s + b * hx s) := by
  rw [Int.mul_add, Int.mul_assoc, Int.mul_assoc]

/-- For every polarization history `(h₊, h×)`, proportional responses give perfectly associated
outputs: the association is the same at every point of the polarization fibre. -/
theorem coaligned_perfect_association (A : List Nat) (a b k : Int) (hk : 0 < k)
    (hp hx : Nat → Int) (hV : 0 < PerfectAssociation.spread A (fun s => a * hp s + b * hx s)) :
    PerfectAssociation.COR A (fun s => a * hp s + b * hx s)
      (fun s => (k * a) * hp s + (k * b) * hx s) = true :=
  proportional_streams_perfect A (fun s => a * hp s + b * hx s)
    (fun s => (k * a) * hp s + (k * b) * hx s) k hk (coaligned_streams a b k hp hx) hV

/-! ## Summary -/

/-- The six obstructions in one statement. -/
theorem ligo_compression_obstructions :
    IsInvalidFor slideData zeroLag ∧
    IsInvalidFor psd (tail 5) ∧
    IsInvalidFor overall bma ∧
    (∀ xE xP xO : Int,
      IsInvalidFor (fun g : Int => sigmaSys2 (xE + g) (xP + g) (xO + g)) (fun g => g)) ∧
    (∀ (P nodes : List Int) (θ : Int), θ ∉ nodes →
      IsInvalidFor (validationView P nodes) (fun e => e.1 θ)) ∧
    (∀ r s : Pol3, IsInvalidFor (respond3 r s) (fun h => h)) :=
  ⟨slides_invalid_for_zeroLag, psd_invalid_for_tail, overall_invalid_for_bma,
   sigmaSys2_invalid_for_common_error, double_blind, two_detectors_invalid_for_polarization⟩

#print axioms frechet_bounds
#print axioms frechet_move
#print axioms slide_fibre_coordinate
#print axioms slides_invalid_for_zeroLag
#print axioms slides_any_statistic_invalid
#print axioms marginal_statistics_invalid
#print axioms slides_valid_on_independence
#print axioms anchor_repairs_iff
#print axioms slide_estimate_not_a_bound
#print axioms frechet_ends
#print axioms coincident_end_excess
#print axioms gw150914_frechet_scale
#print axioms gw150914_slide_ledger
#print axioms chebyshev
#print axioms psd_invalid_for_tail
#print axioms chebyshev_interval_5p1
#print axioms tail_max_5p1
#print axioms overall_invalid_for_bma
#print axioms bma_witness_not_rescaled
#print axioms bma_shift
#print axioms gw150914_m1_bma_shift
#print axioms sigmaSys2_blind
#print axioms sigmaSys2_invalid_for_common_error
#print axioms firstSample_equivariant
#print axioms sigmaSys_samples_blind
#print axioms sigmaSys_samples_invalid
#print axioms tableI_m1_sigmaSys
#print axioms peval_padd
#print axioms peval_pscale
#print axioms peval_pquot
#print axioms length_padd_le
#print axioms length_pscale
#print axioms length_pquot_le_self
#print axioms length_pquot_cons
#print axioms length_pquot_pred
#print axioms vanish_everywhere
#print axioms map_eq_of_mem
#print axioms eq_of_map_eq
#print axioms anchors_valid
#print axioms peval_nodePoly_cons
#print axioms nodePoly_zero
#print axioms nodePoly_ne_zero
#print axioms peval_nodePoly
#print axioms length_nodePoly
#print axioms anchors_invalid_one_degree_up
#print axioms anchor_threshold
#print axioms finite_anchors_invalid
#print axioms double_blind
#print axioms nineteen_nodes
#print axioms adj_fst
#print axioms adj_snd
#print axioms respond_zero
#print axioms respond_faithful_of_det
#print axioms respond_kernel_of_det_zero
#print axioms network_valid_iff_det
#print axioms coaligned_det
#print axioms coaligned_not_valid
#print axioms dot_cross_left
#print axioms dot_cross_right
#print axioms dot_cross_swap
#print axioms kernel_of_cross_zero
#print axioms cross_basis
#print axioms two_detectors_three_modes
#print axioms two_detectors_invalid_for_polarization
#print axioms centered_congr
#print axioms proportional_streams_perfect
#print axioms proportional_minors_vanish
#print axioms coaligned_streams
#print axioms coaligned_perfect_association
#print axioms ligo_compression_obstructions

end LigoCompression
