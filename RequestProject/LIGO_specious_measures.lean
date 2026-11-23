module

public import RequestProject.Measurement

/-!
# Specious measures in the GW150914 analysis

We read the transformations of Abbott et al., *Improved analysis of GW150914 using a fully
spin-precessing waveform model*, Phys. Rev. X 6, 041014 (2016), through the exact calibration
of `Measure`.  A transformation `T` between measured representations is an exact calibration
only if it has the same quantity kind, is a homomorphic association, admits full substitution,
lands in a calibrated range and carries a reverse reading.  Full substitution forces
injectivity (`fullSubstitution_injective`), so every fibre `T a₁ = T a₂` with `a₁ ≠ a₂` is an
obstruction, and the obstruction passes to every exact calibration through `T` and to every
isomorphic transposition.

Numbers from the paper are carried as integers in a fixed unit (hundredths, thousandths,
millionths, tenths of a degree).  All arithmetic is `Nat`/`Int` arithmetic, discharged by
`omega` and by kernel evaluation (`decide`).  Trigonometric values enter only through an
arbitrary function `sinMicro` with hypotheses on its values at the two injected tilts.

* §0 The obstruction lemmas `fibre_obstructs` and `relation_not_reflected`.
* §1 The model difference `D(m₁, m₂) = m₁ − m₂` (Table I, `q = 0.84`, `0.84`): a homomorphism
  whose kernel is the common-mode diagonal; its exact completion `(D, S)` and the relation
  `within w`.
* §2 The effective precession spin `χp` of Eq. (6) at the injection `q = 0.81`,
  `a₁ = 0.34`, `a₂ = 0.67`: the azimuth fibre and the primary-spin fibre.
* §3 The equal-weight posterior combination behind the column "Overall" of Table I.
* §4 The projection of the waveform modes `(2, ±2) ⊕ (2, ±1)` onto `(2, ±2)` in the
  time and phase marginalization.
* §5 The Gaussian likelihood of Eq. (4): sign fibre, detector-split fibre, kind separation.
* §6 The compression of six spin degrees of freedom to four in precessing IMRPhenom.
-/

@[expose] public section

namespace LigoSpecious

open Measure

universe u

/-! ## Quantity kinds, signatures and interpretations -/

/-- Quantity kinds occurring in the analysis. -/
inductive LigoKind where
  | massRatio
  | spin
  | modeAmplitude
  | posteriorCount
  | strain
  | evidenceWeight
  | parameterPoint
  | tableValue
  deriving DecidableEq

/-- Operation symbols: binary addition. -/
inductive AddOp : Nat → Type where
  | add : AddOp 2

/-- The additive signature: addition, no relation symbols. -/
def addSig : Signature := ⟨AddOp, fun _ => Empty⟩

/-- The bare signature: no operation symbols and no relation symbols. -/
def bareSig : Signature := ⟨fun _ => Empty, fun _ => Empty⟩

/-- Addition on `ℤ`. -/
def addInt : {n : Nat} → AddOp n → (Fin n → Int) → Int
  | _, .add, xs => xs 0 + xs 1

/-- Componentwise addition on `ℤ × ℤ`. -/
def addPair : {n : Nat} → AddOp n → (Fin n → Int × Int) → Int × Int
  | _, .add, xs => ((xs 0).1 + (xs 1).1, (xs 0).2 + (xs 1).2)

/-- Elimination of an empty operation symbol. -/
def noOp {α : Type} : {n : Nat} → Empty → (Fin n → α) → α
  | _, e, _ => nomatch e

/-- Equality of pairs from equality of components. -/
theorem pair_congr {α β : Type} {a c : α} {b d : β} (h₁ : a = c) (h₂ : b = d) :
    (a, b) = (c, d) := by
  subst h₁
  subst h₂
  rfl

/-! ## §0 The obstruction lemmas -/

section Obstruction

variable {K : Type} {σ : Signature}

/-- **Fibre obstruction.**  Two distinct states with the same image rule out injectivity, full
substitution, every exact calibration through `T` (over every calibrated range) and every
isomorphic transposition. -/
theorem fibre_obstructs {A B : MeasStructure.{u} K σ} {T : A.carrier → B.carrier}
    (h : ∃ a₁ a₂, a₁ ≠ a₂ ∧ T a₁ = T a₂) :
    ¬ Measure.Injective A B T ∧ ¬ FullSubstitution A B T ∧
    (∀ Bcal : B.carrier → Prop, ¬ Nonempty (ExactCalibration A B Bcal T)) ∧
    ¬ IsomorphicTransposition A B T := by
  refine ⟨?_, not_injective_implies_not_fullSubstitution h, ?_, ?_⟩
  · intro hi
    obtain ⟨a₁, a₂, hne, heq⟩ := h
    exact hne (hi a₁ a₂ heq)
  · intro Bcal hC
    obtain ⟨C⟩ := hC
    exact not_injective_implies_not_fullSubstitution h C.fullSubst
  · intro hI
    have hI' : ∃ e : MeasIso A B, ∀ a, e.toFun a = T a := hI
    obtain ⟨e, he⟩ := hI'
    obtain ⟨a₁, a₂, hne, heq⟩ := h
    apply hne
    have h1 : e.toFun a₁ = e.toFun a₂ := (he a₁).trans (heq.trans (he a₂).symm)
    have h2 : e.invFun (e.toFun a₁) = e.invFun (e.toFun a₂) := congrArg e.invFun h1
    rw [e.left_inv a₁, e.left_inv a₂] at h2
    exact h2

/-- **Relation obstruction.**  A relation instance that holds in the image and fails in the
source rules out full substitution, with no appeal to equality. -/
theorem relation_not_reflected {A B : MeasStructure.{u} K σ} {T : A.carrier → B.carrier}
    {n : Nat} (r : σ.Rel n) (xs : Fin n → A.carrier)
    (hB : B.rel r (fun i => T (xs i))) (hA : ¬ A.rel r xs) :
    ¬ FullSubstitution A B T :=
  fun hf => hA ((hf.2 r xs).mpr hB)

end Obstruction

/-! ## §1 The model difference `D(m₁, m₂) = m₁ − m₂`

Two waveform models return estimates `m₁`, `m₂` of one parameter; the difference of the two
models is the proxy for the systematic error ("the difference between two precessing waveform
models" is the proxy of §VI).  For the mass ratio, Table I lists `q = 0.84 +0.14 −0.20` for
precessing EOBNR, for precessing IMRPhenom and for "Overall", in hundredths `84`, `98`, `64`.
The paper records that multiple models may be wrong in the same way (§I); the common-mode
errors `(g, g)` are exactly the kernel of `D`. -/

/-- Pairs of model estimates `(m₁, m₂)` of one parameter, in hundredths, under addition. -/
def pairStr : MeasStructure.{0} LigoKind addSig where
  carrier := Int × Int
  kind := .massRatio
  op f xs := addPair f xs
  rel _ _ := False

/-- Differences of model estimates, in hundredths, under addition. -/
def diffStr : MeasStructure.{0} LigoKind addSig where
  carrier := Int
  kind := .massRatio
  op f xs := addInt f xs
  rel _ _ := False

/-- The model difference `D(m₁, m₂) = m₁ − m₂`. -/
def modelDiff (p : Int × Int) : Int := p.1 - p.2

/-- `D` preserves addition. -/
theorem modelDiff_preservesOperation : PreservesOperation pairStr diffStr modelDiff := by
  intro n f xs
  cases f
  show (xs 0).1 + (xs 1).1 - ((xs 0).2 + (xs 1).2) =
    ((xs 0).1 - (xs 0).2) + ((xs 1).1 - (xs 1).2)
  omega

/-- `D` is a homomorphic association: preservation alone does not make a substitution. -/
theorem modelDiff_homomorphic : HomomorphicAssociation pairStr diffStr modelDiff :=
  ⟨modelDiff_preservesOperation, preservesEquality_of_sameness _, fun _ _ h => False.elim h⟩

/-- **Common-mode kernel of the model difference.**  At the published medians `84`, `84` and at
the published interval ends `98`, `98` and `64`, `64` the difference is `0`.  The kernel of `D`
is the whole diagonal, a common displacement `g` is invisible to `D`, and the fibre of `D`
through `(x, y)` is exactly its common-mode orbit.  Every proposed truth `R` reproduces both
published medians through the error pair `(84 − R, 84 − R)` with zero model difference. -/
theorem ligo_modelDifference_commonMode_fibre :
    modelDiff (84, 84) = 0 ∧ modelDiff (98, 98) = 0 ∧ modelDiff (64, 64) = 0 ∧
    (∀ x y : Int, modelDiff (x, y) = 0 ↔ x = y) ∧
    (∀ x y g : Int, modelDiff (x + g, y + g) = modelDiff (x, y)) ∧
    (∀ x y x' y' : Int, modelDiff (x, y) = modelDiff (x', y') ↔
      ∃ g : Int, x' = x + g ∧ y' = y + g) ∧
    (∀ R : Int, R + (84 - R) = 84 ∧ modelDiff (84 - R, 84 - R) = 0) := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
  · intro x y
    show x - y = 0 ↔ x = y
    constructor
    · intro h
      omega
    · intro h
      omega
  · intro x y g
    show x + g - (y + g) = x - y
    omega
  · intro x y x' y'
    show x - y = x' - y' ↔ ∃ g : Int, x' = x + g ∧ y' = y + g
    constructor
    · intro h
      exact ⟨x' - x, by omega, by omega⟩
    · intro ⟨g, h1, h2⟩
      omega
  · intro R
    refine ⟨by omega, ?_⟩
    show 84 - R - (84 - R) = 0
    omega

/-- The common-mode witness: `(84, 84)` and `(98, 98)` are distinct states with the same
difference. -/
theorem modelDiff_fibre_witness :
    ∃ a₁ a₂ : Int × Int, a₁ ≠ a₂ ∧ modelDiff a₁ = modelDiff a₂ :=
  ⟨(84, 84), (98, 98), by decide, by decide⟩

/-- `D` is not injective. -/
theorem ligo_modelDifference_not_injective : ¬ Measure.Injective pairStr diffStr modelDiff :=
  (fibre_obstructs (A := pairStr) (B := diffStr) (T := modelDiff) modelDiff_fibre_witness).1

/-- `D` does not admit full substitution. -/
theorem ligo_modelDifference_not_fullSubstitution : ¬ FullSubstitution pairStr diffStr modelDiff :=
  (fibre_obstructs (A := pairStr) (B := diffStr) (T := modelDiff) modelDiff_fibre_witness).2.1

/-- `D` is no part of an exact calibration of the pair of estimates, over any calibrated
range of differences. -/
theorem ligo_modelDifference_no_exact_calibration (Bcal : diffStr.carrier → Prop) :
    ¬ Nonempty (ExactCalibration pairStr diffStr Bcal modelDiff) :=
  (fibre_obstructs (A := pairStr) (B := diffStr) (T := modelDiff)
    modelDiff_fibre_witness).2.2.1 Bcal

/-- `D` is the forward map of no isomorphism. -/
theorem ligo_modelDifference_not_isomorphic_transposition :
    ¬ IsomorphicTransposition pairStr diffStr modelDiff :=
  (fibre_obstructs (A := pairStr) (B := diffStr) (T := modelDiff) modelDiff_fibre_witness).2.2.2

/-! ### The exact completion `(D, S)`

The sum `S = m₁ + m₂` is twice the bias of the equal-weight combination of the two models.
Together with `D` it is an exact calibration onto the parity range `d + s ≡ 0 (mod 2)`:
`D` alone carries no information about `S` beyond parity. -/

/-- `(D, S)(m₁, m₂) = (m₁ − m₂, m₁ + m₂)`. -/
def diffSum (p : Int × Int) : Int × Int := (p.1 - p.2, p.1 + p.2)

/-- The calibrated range of `(D, S)`: `d + s` is even. -/
def parityRange (b : Int × Int) : Prop := (b.1 + b.2) % 2 = 0

/-- The reverse reading `(d, s) ↦ ((s + d)/2, (s − d)/2)`. -/
def diffSumRecal (b : Int × Int) : Int × Int := ((b.2 + b.1) / 2, (b.2 - b.1) / 2)

/-- `(D, S)` preserves addition. -/
theorem diffSum_preservesOperation : PreservesOperation pairStr pairStr diffSum := by
  intro n f xs
  cases f
  show ((xs 0).1 + (xs 1).1 - ((xs 0).2 + (xs 1).2),
      (xs 0).1 + (xs 1).1 + ((xs 0).2 + (xs 1).2)) =
    ((xs 0).1 - (xs 0).2 + ((xs 1).1 - (xs 1).2),
      (xs 0).1 + (xs 0).2 + ((xs 1).1 + (xs 1).2))
  exact pair_congr (by omega) (by omega)

/-- `(D, S)` reflects equality: `a₁ = a₂ ↔ (D, S) a₁ = (D, S) a₂`. -/
theorem diffSum_eq_iff (a₁ a₂ : Int × Int) : a₁ = a₂ ↔ diffSum a₁ = diffSum a₂ := by
  obtain ⟨x, y⟩ := a₁
  obtain ⟨x', y'⟩ := a₂
  constructor
  · intro h
    exact congrArg diffSum h
  · intro h
    have h1 : x - y = x' - y' := congrArg Prod.fst h
    have h2 : x + y = x' + y' := congrArg Prod.snd h
    exact pair_congr (by omega) (by omega)

/-- `(D, S)` lands in the parity range. -/
theorem diffSum_lands (a : Int × Int) : parityRange (diffSum a) := by
  obtain ⟨x, y⟩ := a
  show (x - y + (x + y)) % 2 = 0
  omega

/-- The reverse reading inverts `(D, S)` on the parity range. -/
theorem diffSum_recal_spec (b : Int × Int) (hb : parityRange b) :
    diffSum (diffSumRecal b) = b := by
  obtain ⟨d, s⟩ := b
  have hb' : (d + s) % 2 = 0 := hb
  show ((s + d) / 2 - (s - d) / 2, (s + d) / 2 + (s - d) / 2) = (d, s)
  exact pair_congr (by omega) (by omega)

/-- **`(D, S)` is an exact calibration** of the pair of estimates onto the parity range. -/
def diffSumCalibration : ExactCalibration pairStr pairStr parityRange diffSum where
  sameKind := rfl
  hom := ⟨diffSum_preservesOperation, preservesEquality_of_sameness _,
    fun _ _ h => False.elim h⟩
  fullSubst := ⟨diffSum_eq_iff, fun _ _ => ⟨fun h => False.elim h, fun h => False.elim h⟩⟩
  lands := diffSum_lands
  recal := diffSumRecal
  recal_spec := diffSum_recal_spec

/-- The pair of model estimates is isomorphic to the parity range of `(D, S)`. -/
theorem ligo_modelDifference_anchor_isomorphism :
    Isomorphic pairStr (pairStr.restrict parityRange diffSumCalibration.closedRange) :=
  exact_calibration_isomorphic diffSumCalibration

/-- For every observed difference `d`, every sum `s` of the same parity occurs: the model
difference carries no information about the bias of the combined estimate. -/
theorem ligo_overall_bias_free_of_difference :
    ∀ d s : Int, (d + s) % 2 = 0 → ∃ e : Int × Int, modelDiff e = d ∧ e.1 + e.2 = s := by
  intro d s hds
  have h : diffSum (diffSumRecal (d, s)) = (d, s) := diffSum_recal_spec (d, s) hds
  have h1 : (diffSumRecal (d, s)).1 - (diffSumRecal (d, s)).2 = d := congrArg Prod.fst h
  have h2 : (diffSumRecal (d, s)).1 + (diffSumRecal (d, s)).2 = s := congrArg Prod.snd h
  exact ⟨diffSumRecal (d, s), h1, h2⟩

/-! ### The relation `within w`

The statement "the systematic error is at most the statistical width `w`" is a relation of
the error state `(e₁, e₂)`: both models lie within `w` of the truth.  Its image under `D` is
"the models agree within `w`". -/

/-- Relation symbols: the unary relation `within w`. -/
inductive WithinRel : Nat → Type where
  | within (w : Int) : WithinRel 1

/-- The signature with addition and the relations `within w`. -/
def widthSig : Signature := ⟨AddOp, WithinRel⟩

/-- `within w` on error pairs: both errors lie in `[−w, w]`. -/
def errWithin : {n : Nat} → WithinRel n → (Fin n → Int × Int) → Prop
  | _, .within w, xs => (xs 0).1 ≤ w ∧ -w ≤ (xs 0).1 ∧ (xs 0).2 ≤ w ∧ -w ≤ (xs 0).2

/-- `within w` on differences: the difference lies in `[−w, w]`. -/
def difWithin : {n : Nat} → WithinRel n → (Fin n → Int) → Prop
  | _, .within w, xs => xs 0 ≤ w ∧ -w ≤ xs 0

/-- Error pairs with the relations `within w`. -/
def errStr : MeasStructure.{0} LigoKind widthSig where
  carrier := Int × Int
  kind := .massRatio
  op f xs := addPair f xs
  rel r xs := errWithin r xs

/-- Differences with the relations `within w`. -/
def difWStr : MeasStructure.{0} LigoKind widthSig where
  carrier := Int
  kind := .massRatio
  op f xs := addInt f xs
  rel r xs := difWithin r xs

/-- **`D` does not reflect `within w`.**  A common error `g > w` has zero model difference,
which is within every width `w ≥ 0`. -/
theorem ligo_modelDifference_width_not_reflected (w g : Int) (hw : 0 ≤ w) (hg : w < g) :
    ¬ FullSubstitution errStr difWStr modelDiff := by
  refine relation_not_reflected (r := WithinRel.within w) (fun _ => ((g, g) : Int × Int)) ?_ ?_
  · show g - g ≤ w ∧ -w ≤ g - g
    constructor <;> omega
  · intro h
    have h' : g ≤ w ∧ -w ≤ g ∧ g ≤ w ∧ -w ≤ g := h
    omega

/-- **The published widths of `q`.**  Table I gives the upper half-width `0.14` and the lower
half-width `0.20` of the 90% interval of the mass ratio, in hundredths `14` and `20`.  A common
error of `0.15` exceeds the first and a common error of `0.21` exceeds the second, and both have
zero model difference; the relation `within w` is not reflected by `D`. -/
theorem ligo_modelDifference_q_widths_not_reflected :
    ((14 : Int) < 15 ∧ modelDiff (15, 15) = 0) ∧ ((20 : Int) < 21 ∧ modelDiff (21, 21) = 0) ∧
    ¬ FullSubstitution errStr difWStr modelDiff :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ligo_modelDifference_width_not_reflected 14 15 (by decide) (by decide)⟩

/-! ## §2 The effective precession spin `χp`

Equation (6) of the paper reads `χp = max(B₁ S₁⊥, B₂ S₂⊥)/(B₁ m₁²)` with `B₁ = 2 + 3q/2` and
`B₂ = 2 + 3/(2q)`.  With `Sᵢ⊥ = mᵢ² aᵢ sin θᵢ` and `q = m₂/m₁` this is
`χp = max(a₁ sin θ₁, (B₂/B₁) q² a₂ sin θ₂)`.  For `q = n/100` one has
`(B₂/B₁) q² = K₂(n)/K₁(n)` with `K₁(n) = 100 (3n + 400)` and `K₂(n) = n (4n + 300)`.

Spin magnitudes are counted in hundredths, tilts and azimuths in tenths of a degree, and the
sines in millionths: `sinMicro θ` stands for `10⁶ sin θ` and is an arbitrary function of the
tilt, constrained only through the certified windows at the two injected tilts.  Then
`χp = max(K₁ (a₁ s₁), K₂ (a₂ s₂)) / (K₁ · 10⁸)`.  The azimuths `φ₁`, `φ₂` do not occur.

The injection is the numerical-relativity waveform SXS:BBH:0308 of the paper:
`q = 0.81`, `a₁ = 0.34`, `a₂ = 0.67`, `θ₁ = 18.8°`, `θ₂ = 149.4°`, `φ₁ = 30.9°`, `φ₂ = 38.7°`.
The windows `322265 ≤ 10⁶ sin 18.8° ≤ 322266` and `509041 ≤ 10⁶ sin 149.4° ≤ 509042` are
certified by exact rational enclosures (alternating-series brackets and a Machin enclosure of
`π`) in the companion script `ligo_modules_crosscheck.py`. -/

/-- A spin state of the binary: mass ratio `q` and spin magnitudes `a₁`, `a₂` in hundredths;
tilts `θ₁`, `θ₂` and azimuths `φ₁`, `φ₂` in tenths of a degree. -/
structure SpinState where
  q : Nat
  a1 : Nat
  a2 : Nat
  th1 : Int
  th2 : Int
  ph1 : Int
  ph2 : Int

/-- `K₁(n) = 100 (3n + 400)`. -/
def K1 (n : Nat) : Nat := 100 * (3 * n + 400)

/-- `K₂(n) = n (4n + 300)`. -/
def K2 (n : Nat) : Nat := n * (4 * n + 300)

/-- The larger of two natural numbers. -/
def maxN (x y : Nat) : Nat := if x ≤ y then y else x

/-- `x ≤ y` gives `max x y = y`. -/
theorem maxN_of_le {x y : Nat} (h : x ≤ y) : maxN x y = y := by
  unfold maxN
  rw [if_pos h]

/-- `y < x` gives `max x y = x`. -/
theorem maxN_of_lt {x y : Nat} (h : y < x) : maxN x y = x := by
  unfold maxN
  rw [if_neg (by omega : ¬ x ≤ y)]

/-- Numerator of `χp`: `max(K₁ (a₁ s₁), K₂ (a₂ s₂))`, where `sᵢ = sinMicro θᵢ`. -/
def chiPNum (sinMicro : Int → Nat) (s : SpinState) : Nat :=
  maxN (K1 s.q * (s.a1 * sinMicro s.th1)) (K2 s.q * (s.a2 * sinMicro s.th2))

/-- Denominator of `χp`: `K₁ · 10⁸`. -/
def chiPDen (s : SpinState) : Nat := K1 s.q * 100000000

/-- Equation (6): `χp` as the fraction (numerator, denominator). -/
def chiP (sinMicro : Int → Nat) (s : SpinState) : Nat × Nat :=
  (chiPNum sinMicro s, chiPDen s)

/-- Spin states, with no operation and no relation. -/
def spinStr : MeasStructure.{0} LigoKind bareSig where
  carrier := SpinState
  kind := .spin
  op f xs := noOp f xs
  rel _ _ := False

/-- Values of `χp` as fractions, with no operation and no relation. -/
def chiPStr : MeasStructure.{0} LigoKind bareSig where
  carrier := Nat × Nat
  kind := .spin
  op f xs := noOp f xs
  rel _ _ := False

/-- The injection SXS:BBH:0308: `q = 0.81`, `a₁ = 0.34`, `a₂ = 0.67`, `θ₁ = 18.8°`,
`θ₂ = 149.4°`, `φ₁ = 30.9°`, `φ₂ = 38.7°`. -/
def nrInjection : SpinState := ⟨81, 34, 67, 188, 1494, 309, 387⟩

/-- The injection with the azimuth of the primary turned to `100.0°`. -/
def nrInjectionRot : SpinState := { nrInjection with ph1 := 1000 }

/-- The numerator of `χp` at the injection: the secondary term dominates, under the certified
windows for the two sines. -/
theorem chiPNum_nrInjection (sinMicro : Int → Nat)
    (h1 : 322265 ≤ sinMicro 188 ∧ sinMicro 188 ≤ 322266)
    (h2 : 509041 ≤ sinMicro 1494 ∧ sinMicro 1494 ≤ 509042) :
    chiPNum sinMicro nrInjection = K2 81 * (67 * sinMicro 1494) := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  have hK1 : K1 81 = 64300 := by decide
  have hK2 : K2 81 = 50544 := by decide
  have hdom : K1 81 * (34 * sinMicro 188) ≤ K2 81 * (67 * sinMicro 1494) := by
    rw [hK1, hK2]
    omega
  show maxN (K1 81 * (34 * sinMicro 188)) (K2 81 * (67 * sinMicro 1494)) =
    K2 81 * (67 * sinMicro 1494)
  exact maxN_of_le hdom

/-- **The real values of Equation (6) at the injection.**  `K₁(81) = 64300`, `K₂(81) = 50544`,
the denominator is `6430000000000`, the secondary term dominates, `χp` is the secondary term,
`0.268093 ≤ χp ≤ 0.268094`, and the primary term `a₁ sin θ₁` lies in `[0.10957, 0.10958]`. -/
theorem ligo_chiP_real_values (sinMicro : Int → Nat)
    (h1 : 322265 ≤ sinMicro 188 ∧ sinMicro 188 ≤ 322266)
    (h2 : 509041 ≤ sinMicro 1494 ∧ sinMicro 1494 ≤ 509042) :
    K1 81 = 64300 ∧ K2 81 = 50544 ∧ chiPDen nrInjection = 6430000000000 ∧
    K1 81 * (34 * sinMicro 188) ≤ K2 81 * (67 * sinMicro 1494) ∧
    chiPNum sinMicro nrInjection = K2 81 * (67 * sinMicro 1494) ∧
    268093 * chiPDen nrInjection ≤ 1000000 * chiPNum sinMicro nrInjection ∧
    1000000 * chiPNum sinMicro nrInjection ≤ 268094 * chiPDen nrInjection ∧
    10957000 ≤ 34 * sinMicro 188 ∧ 34 * sinMicro 188 ≤ 10958000 := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  have hK1 : K1 81 = 64300 := by decide
  have hK2 : K2 81 = 50544 := by decide
  have hden : chiPDen nrInjection = 6430000000000 := by decide
  have hnum : chiPNum sinMicro nrInjection = K2 81 * (67 * sinMicro 1494) :=
    chiPNum_nrInjection sinMicro ⟨h1a, h1b⟩ ⟨h2a, h2b⟩
  have hnum' : chiPNum sinMicro nrInjection = 50544 * (67 * sinMicro 1494) := by
    rw [hnum, hK2]
  have hdom : K1 81 * (34 * sinMicro 188) ≤ K2 81 * (67 * sinMicro 1494) := by
    rw [hK1, hK2]
    omega
  refine ⟨hK1, hK2, hden, hdom, hnum, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega

/-- The injected `χp` lies strictly below `0.4`, the location at which the paper reports the
posterior of the effective precession spin to peak for the inclination at the upper end of its
credible interval. -/
theorem ligo_chiP_injected_below_posterior_peak (sinMicro : Int → Nat)
    (h1 : 322265 ≤ sinMicro 188 ∧ sinMicro 188 ≤ 322266)
    (h2 : 509041 ≤ sinMicro 1494 ∧ sinMicro 1494 ≤ 509042) :
    1000000 * chiPNum sinMicro nrInjection < 400000 * chiPDen nrInjection := by
  obtain ⟨_, _, _, _, _, _, hup, _, _⟩ := ligo_chiP_real_values sinMicro h1 h2
  have hden : chiPDen nrInjection = 6430000000000 := by decide
  omega

/-- A function whose values at the two injected tilts are the roundings of `10⁶ sin 18.8°`
and `10⁶ sin 149.4°`. -/
def sinAtTilts (θ : Int) : Nat :=
  if θ = 188 then 322266 else if θ = 1494 then 509041 else 0

/-- `sinAtTilts` lies in both certified windows. -/
theorem sinAtTilts_windows :
    (322265 ≤ sinAtTilts 188 ∧ sinAtTilts 188 ≤ 322266) ∧
    (509041 ≤ sinAtTilts 1494 ∧ sinAtTilts 1494 ≤ 509042) := by
  decide

/-- Closed form of `χp` at the injection for `sinAtTilts`:
`χp = 1723840876368 / 6430000000000`. -/
theorem ligo_chiP_real_values_closed :
    chiP sinAtTilts nrInjection = (1723840876368, 6430000000000) := by
  decide

/-- Eq. (6) does not depend on the azimuths. -/
theorem chiP_azimuth_invariant (sinMicro : Int → Nat) (s : SpinState) (p₁ p₂ : Int) :
    chiP sinMicro { s with ph1 := p₁, ph2 := p₂ } = chiP sinMicro s :=
  rfl

/-- The azimuth-turned injection differs from the injection. -/
theorem nrInjectionRot_ne : nrInjectionRot ≠ nrInjection := by
  intro h
  have h' : (1000 : Int) = 309 := congrArg SpinState.ph1 h
  omega

/-- **Azimuth fibre of Equation (6).**  Every change of the azimuths `φ₁`, `φ₂` leaves `χp`
unchanged.  At the injection, turning `φ₁` from `30.9°` to `100.0°` gives a different spin
state, a different angle `φ₁₂ = φ₁ − φ₂` between the in-plane spin projections, and the same
`χp`. -/
theorem ligo_chiP_azimuth_fibre :
    (∀ (sinMicro : Int → Nat) (s : SpinState) (p₁ p₂ : Int),
      chiP sinMicro { s with ph1 := p₁, ph2 := p₂ } = chiP sinMicro s) ∧
    (∀ sinMicro : Int → Nat, chiP sinMicro nrInjectionRot = chiP sinMicro nrInjection) ∧
    nrInjectionRot ≠ nrInjection ∧
    nrInjectionRot.ph1 - nrInjectionRot.ph2 ≠ nrInjection.ph1 - nrInjection.ph2 := by
  refine ⟨chiP_azimuth_invariant, fun _ => rfl, nrInjectionRot_ne, by decide⟩

/-- The azimuth fibre exhibits two distinct states with the same `χp`. -/
theorem chiP_fibre_witness (sinMicro : Int → Nat) :
    ∃ a₁ a₂ : SpinState, a₁ ≠ a₂ ∧ chiP sinMicro a₁ = chiP sinMicro a₂ :=
  ⟨nrInjectionRot, nrInjection, nrInjectionRot_ne, rfl⟩

/-- `χp` is not injective on spin states. -/
theorem ligo_chiP_not_injective (sinMicro : Int → Nat) :
    ¬ Measure.Injective spinStr chiPStr (chiP sinMicro) :=
  (fibre_obstructs (A := spinStr) (B := chiPStr) (T := chiP sinMicro)
    (chiP_fibre_witness sinMicro)).1

/-- `χp` does not admit full substitution of spin states. -/
theorem ligo_chiP_not_fullSubstitution (sinMicro : Int → Nat) :
    ¬ FullSubstitution spinStr chiPStr (chiP sinMicro) :=
  (fibre_obstructs (A := spinStr) (B := chiPStr) (T := chiP sinMicro)
    (chiP_fibre_witness sinMicro)).2.1

/-- `χp` is no part of an exact calibration of spin states, over any calibrated range. -/
theorem ligo_chiP_no_exact_calibration (sinMicro : Int → Nat) (Bcal : chiPStr.carrier → Prop) :
    ¬ Nonempty (ExactCalibration spinStr chiPStr Bcal (chiP sinMicro)) :=
  (fibre_obstructs (A := spinStr) (B := chiPStr) (T := chiP sinMicro)
    (chiP_fibre_witness sinMicro)).2.2.1 Bcal

/-- `χp` is the forward map of no isomorphism of spin states. -/
theorem ligo_chiP_not_isomorphic_transposition (sinMicro : Int → Nat) :
    ¬ IsomorphicTransposition spinStr chiPStr (chiP sinMicro) :=
  (fibre_obstructs (A := spinStr) (B := chiPStr) (T := chiP sinMicro)
    (chiP_fibre_witness sinMicro)).2.2.2

/-! ### The primary-spin fibre

The max of Equation (6) is attained by the secondary term at the injection.  Every primary spin
`a₁` whose term stays below it leaves `χp` unchanged. -/

/-- If the secondary term dominates before and after the change of `a₁`, `χp` is unchanged. -/
theorem chiP_primary_fibre (sinMicro : Int → Nat) (s : SpinState) (a : Nat)
    (h : K1 s.q * (s.a1 * sinMicro s.th1) ≤ K2 s.q * (s.a2 * sinMicro s.th2))
    (h' : K1 s.q * (a * sinMicro s.th1) ≤ K2 s.q * (s.a2 * sinMicro s.th2)) :
    chiP sinMicro { s with a1 := a } = chiP sinMicro s := by
  have e1 : maxN (K1 s.q * (a * sinMicro s.th1)) (K2 s.q * (s.a2 * sinMicro s.th2)) =
      K2 s.q * (s.a2 * sinMicro s.th2) := maxN_of_le h'
  have e2 : maxN (K1 s.q * (s.a1 * sinMicro s.th1)) (K2 s.q * (s.a2 * sinMicro s.th2)) =
      K2 s.q * (s.a2 * sinMicro s.th2) := maxN_of_le h
  unfold chiP
  exact pair_congr (e1.trans e2.symm) rfl

/-- **Primary-spin fibre.**  At the injection, every primary spin `a₁ ∈ {0, …, 0.83}` gives the
same `χp`. -/
theorem ligo_chiP_primarySpin_fibre (sinMicro : Int → Nat)
    (h1 : 322265 ≤ sinMicro 188 ∧ sinMicro 188 ≤ 322266)
    (h2 : 509041 ≤ sinMicro 1494 ∧ sinMicro 1494 ≤ 509042) (a : Nat) (ha : a ≤ 83) :
    chiP sinMicro { nrInjection with a1 := a } = chiP sinMicro nrInjection := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  have hK1 : K1 81 = 64300 := by decide
  have hK2 : K2 81 = 50544 := by decide
  have hP : a * sinMicro 188 ≤ 83 * 322266 := Nat.mul_le_mul ha h1b
  have hdom : K1 81 * (34 * sinMicro 188) ≤ K2 81 * (67 * sinMicro 1494) := by
    rw [hK1, hK2]
    omega
  have hdom' : K1 81 * (a * sinMicro 188) ≤ K2 81 * (67 * sinMicro 1494) := by
    rw [hK1, hK2]
    omega
  exact chiP_primary_fibre sinMicro nrInjection a hdom hdom'

/-- **Primary-spin threshold.**  At the injection, every primary spin `a₁ ≥ 0.84` makes the
primary term the maximum and changes `χp`. -/
theorem ligo_chiP_primarySpin_threshold (sinMicro : Int → Nat)
    (h1 : 322265 ≤ sinMicro 188 ∧ sinMicro 188 ≤ 322266)
    (h2 : 509041 ≤ sinMicro 1494 ∧ sinMicro 1494 ≤ 509042) (a : Nat) (ha : 84 ≤ a) :
    chiP sinMicro { nrInjection with a1 := a } ≠ chiP sinMicro nrInjection := by
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  have hK1 : K1 81 = 64300 := by decide
  have hK2 : K2 81 = 50544 := by decide
  have hP : 84 * 322265 ≤ a * sinMicro 188 := Nat.mul_le_mul ha h1a
  have hlt : K2 81 * (67 * sinMicro 1494) < K1 81 * (a * sinMicro 188) := by
    rw [hK1, hK2]
    omega
  have hnum0 : chiPNum sinMicro nrInjection = K2 81 * (67 * sinMicro 1494) :=
    chiPNum_nrInjection sinMicro ⟨h1a, h1b⟩ ⟨h2a, h2b⟩
  have hnum1 : chiPNum sinMicro { nrInjection with a1 := a } = K1 81 * (a * sinMicro 188) := by
    show maxN (K1 81 * (a * sinMicro 188)) (K2 81 * (67 * sinMicro 1494)) =
      K1 81 * (a * sinMicro 188)
    exact maxN_of_lt hlt
  intro h
  have hn : chiPNum sinMicro { nrInjection with a1 := a } = chiPNum sinMicro nrInjection :=
    (Prod.mk.inj (show (_, _) = (_, _) from h)).1
  rw [hnum1, hnum0] at hn
  rw [hK1, hK2] at hn hlt
  omega

/-- The published 90% intervals of `a₁` (hundredths) against the fibre: the intervals
`[0.02, 0.65]` of precessing EOBNR and `[0.02, 0.78]` of "Overall" lie inside the fibre
`a₁ ≤ 0.83`; the upper end `0.85` of precessing IMRPhenom lies beyond the threshold. -/
theorem ligo_chiP_primarySpin_credible_intervals (sinMicro : Int → Nat)
    (h1 : 322265 ≤ sinMicro 188 ∧ sinMicro 188 ≤ 322266)
    (h2 : 509041 ≤ sinMicro 1494 ∧ sinMicro 1494 ≤ 509042) :
    (∀ a : Nat, 2 ≤ a → a ≤ 65 →
      chiP sinMicro { nrInjection with a1 := a } = chiP sinMicro nrInjection) ∧
    (∀ a : Nat, 2 ≤ a → a ≤ 78 →
      chiP sinMicro { nrInjection with a1 := a } = chiP sinMicro nrInjection) ∧
    chiP sinMicro { nrInjection with a1 := 85 } ≠ chiP sinMicro nrInjection :=
  ⟨fun a _ ha => ligo_chiP_primarySpin_fibre sinMicro h1 h2 a (by omega),
    fun a _ ha => ligo_chiP_primarySpin_fibre sinMicro h1 h2 a (by omega),
    ligo_chiP_primarySpin_threshold sinMicro h1 h2 85 (by omega)⟩

/-! ## §3 The equal-weight combination of two posteriors

The column "Overall" of Table I is the equal-weight average of the posteriors of the two
precessing models; the paper reads it as the assumption that the observed signal could have
come from either model with equal posterior probability.  For a threshold `x` a model posterior
is recorded by its probability mass below and above `x`, in hundredths.  `Post2` holds
`(eob1, eob2)` for precessing EOBNR and `(imr1, imr2)` for precessing IMRPhenom.  The combined
masses are `(eob1 + imr1, eob2 + imr2)` up to the factor `1/2`, which is injective and does not
change fibres. -/

/-- Masses below and above a threshold, for precessing EOBNR and for precessing IMRPhenom, in
hundredths of probability. -/
structure Post2 where
  eob1 : Int
  eob2 : Int
  imr1 : Int
  imr2 : Int

/-- Componentwise addition of mass records. -/
def addPost : {n : Nat} → AddOp n → (Fin n → Post2) → Post2
  | _, .add, xs => ⟨(xs 0).eob1 + (xs 1).eob1, (xs 0).eob2 + (xs 1).eob2,
      (xs 0).imr1 + (xs 1).imr1, (xs 0).imr2 + (xs 1).imr2⟩

/-- The equal-weight combination, up to the factor `1/2`: masses below and above the
threshold. -/
def overall (P : Post2) : Int × Int := (P.eob1 + P.imr1, P.eob2 + P.imr2)

/-- Pairs of model posteriors under addition. -/
def post2Str : MeasStructure.{0} LigoKind addSig where
  carrier := Post2
  kind := .posteriorCount
  op f xs := addPost f xs
  rel _ _ := False

/-- Combined posteriors under addition. -/
def overallStr : MeasStructure.{0} LigoKind addSig where
  carrier := Int × Int
  kind := .posteriorCount
  op f xs := addPair f xs
  rel _ _ := False

/-- The combination preserves addition. -/
theorem overall_preservesOperation : PreservesOperation post2Str overallStr overall := by
  intro n f xs
  cases f
  show ((xs 0).eob1 + (xs 1).eob1 + ((xs 0).imr1 + (xs 1).imr1),
      (xs 0).eob2 + (xs 1).eob2 + ((xs 0).imr2 + (xs 1).imr2)) =
    ((xs 0).eob1 + (xs 0).imr1 + ((xs 1).eob1 + (xs 1).imr1),
      (xs 0).eob2 + (xs 0).imr2 + ((xs 1).eob2 + (xs 1).imr2))
  exact pair_congr (by omega) (by omega)

/-- The combination is a homomorphic association. -/
theorem overall_homomorphic : HomomorphicAssociation post2Str overallStr overall :=
  ⟨overall_preservesOperation, preservesEquality_of_sameness _, fun _ _ h => False.elim h⟩

/-- **Redistribution fibre of the equal-weight combination.**  Moving mass `δ` below the
threshold in precessing EOBNR and the same mass `δ` above the threshold in precessing
IMRPhenom leaves the combination unchanged.  At the threshold `0.65` of the primary spin, the
splits `(1.0, 0.8)` and `(0.9, 0.9)` of the mass below the threshold, and every split
`(f_E, f_P)` with `0.9 ≤ f_E ≤ 1` and `f_E + f_P = 1.8`, give the combined masses
`(0.9, 0.1)` of the "Overall" column. -/
theorem ligo_modelAverage_fibre :
    (∀ (P : Post2) (δ : Int),
      overall ⟨P.eob1 + δ, P.eob2 - δ, P.imr1 - δ, P.imr2 + δ⟩ = overall P) ∧
    overall ⟨100, 0, 80, 20⟩ = (180, 20) ∧ overall ⟨90, 10, 90, 10⟩ = (180, 20) ∧
    (∀ fE fP : Int, 90 ≤ fE → fE ≤ 100 → 0 ≤ fP → fP ≤ 90 → fE + fP = 180 →
      overall ⟨fE, 100 - fE, fP, 100 - fP⟩ = (180, 20)) := by
  refine ⟨?_, by decide, by decide, ?_⟩
  · intro P δ
    show (P.eob1 + δ + (P.imr1 - δ), P.eob2 - δ + (P.imr2 + δ)) =
      (P.eob1 + P.imr1, P.eob2 + P.imr2)
    exact pair_congr (by omega) (by omega)
  · intro fE fP h1 h2 h3 h4 h5
    show (fE + fP, 100 - fE + (100 - fP)) = (180, 20)
    exact pair_congr (by omega) (by omega)

/-- **The published bounds confine the model masses to a segment, on which the combination is
constant.**  Let `FE` and `FP` be the cumulative distributions of precessing EOBNR and
precessing IMRPhenom, in hundredths of probability.  Let `xE < xO < xP` be the 90% upper bounds
of precessing EOBNR, "Overall" and precessing IMRPhenom; Table I gives `0.54 < 0.65 < 0.74` for
the primary spin.  Then `FE xE = 90`, `FP xP = 90`, and, the combined distribution being the
mean of the two, `FE xO + FP xO = 180`.  Monotonicity gives `90 ≤ FE xO ≤ 100` and
`80 ≤ FP xO ≤ 90`, and the split `(FE xO, FP xO)` lies on the segment of the previous theorem. -/
theorem ligo_modelAverage_bound_segment (FE FP : Int → Int)
    (hE : ∀ x y : Int, x ≤ y → FE x ≤ FE y) (hP : ∀ x y : Int, x ≤ y → FP x ≤ FP y)
    (hEtop : ∀ x : Int, FE x ≤ 100) (hPbot : ∀ x : Int, 0 ≤ FP x)
    (xE xO xP : Int) (hEO : xE < xO) (hOP : xO < xP)
    (hE90 : FE xE = 90) (hP90 : FP xP = 90) (hO90 : FE xO + FP xO = 180) :
    90 ≤ FE xO ∧ FE xO ≤ 100 ∧ 80 ≤ FP xO ∧ FP xO ≤ 90 ∧
    overall ⟨FE xO, 100 - FE xO, FP xO, 100 - FP xO⟩ = (180, 20) := by
  have h1 : FE xE ≤ FE xO := hE xE xO (by omega)
  have h2 : FP xO ≤ FP xP := hP xO xP (by omega)
  have h3 : FE xO ≤ 100 := hEtop xO
  have h4 : 0 ≤ FP xO := hPbot xO
  refine ⟨by omega, h3, by omega, by omega, ?_⟩
  show (FE xO + FP xO, 100 - FE xO + (100 - FP xO)) = (180, 20)
  exact pair_congr (by omega) (by omega)

/-- The two extreme splits are distinct states. -/
theorem post2_witness_ne : (⟨100, 0, 80, 20⟩ : Post2) ≠ (⟨90, 10, 90, 10⟩ : Post2) := by
  intro h
  have h' : (100 : Int) = 90 := congrArg Post2.eob1 h
  omega

/-- The extreme splits are two distinct states with the same combination. -/
theorem modelAverage_fibre_witness :
    ∃ a₁ a₂ : Post2, a₁ ≠ a₂ ∧ overall a₁ = overall a₂ :=
  ⟨⟨100, 0, 80, 20⟩, ⟨90, 10, 90, 10⟩, post2_witness_ne, by decide⟩

/-- The equal-weight combination is not injective. -/
theorem ligo_modelAverage_not_injective : ¬ Measure.Injective post2Str overallStr overall :=
  (fibre_obstructs (A := post2Str) (B := overallStr) (T := overall)
    modelAverage_fibre_witness).1

/-- The equal-weight combination does not admit full substitution of the pair of posteriors. -/
theorem ligo_modelAverage_not_fullSubstitution : ¬ FullSubstitution post2Str overallStr overall :=
  (fibre_obstructs (A := post2Str) (B := overallStr) (T := overall)
    modelAverage_fibre_witness).2.1

/-- The combination is no part of an exact calibration of the pair of posteriors, over any
calibrated range. -/
theorem ligo_modelAverage_no_exact_calibration (Bcal : overallStr.carrier → Prop) :
    ¬ Nonempty (ExactCalibration post2Str overallStr Bcal overall) :=
  (fibre_obstructs (A := post2Str) (B := overallStr) (T := overall)
    modelAverage_fibre_witness).2.2.1 Bcal

/-- The combination is the forward map of no isomorphism. -/
theorem ligo_modelAverage_not_isomorphic_transposition :
    ¬ IsomorphicTransposition post2Str overallStr overall :=
  (fibre_obstructs (A := post2Str) (B := overallStr) (T := overall)
    modelAverage_fibre_witness).2.2.2

/-! ## §4 The projection of the waveform modes in the likelihood marginalization

Precessing EOBNR contains the modes `(2, ±2)` and `(2, ±1)`.  To save computing time the
marginalization over the arrival time and the phase is carried out as if the waveform
contained only the `(2, ±2)` inertial-frame modes (Sec. II).  `ModeAmps` records the amplitudes
of the four modes `(2, 2)`, `(2, −2)`, `(2, 1)`, `(2, −1)`.  The substitution is the projection
`P(h₂₂, h₂₋₂, h₂₁, h₂₋₁) = (h₂₂, h₂₋₂)`.  An estimate of the size of the dropped component
bounds the error of the approximation; it does not change the kernel of `P`. -/

/-- Amplitudes of the modes `(2, 2)`, `(2, −2)`, `(2, 1)`, `(2, −1)`. -/
structure ModeAmps where
  h22 : Int
  h2m2 : Int
  h21 : Int
  h2m1 : Int

/-- Componentwise addition of mode amplitudes. -/
def addModes : {n : Nat} → AddOp n → (Fin n → ModeAmps) → ModeAmps
  | _, .add, xs => ⟨(xs 0).h22 + (xs 1).h22, (xs 0).h2m2 + (xs 1).h2m2,
      (xs 0).h21 + (xs 1).h21, (xs 0).h2m1 + (xs 1).h2m1⟩

/-- The projection onto the `(2, ±2)` modes. -/
def proj22 (h : ModeAmps) : Int × Int := (h.h22, h.h2m2)

/-- Waveforms with the modes `(2, ±2)` and `(2, ±1)`, under addition. -/
def modeStr : MeasStructure.{0} LigoKind addSig where
  carrier := ModeAmps
  kind := .modeAmplitude
  op f xs := addModes f xs
  rel _ _ := False

/-- Waveforms with the modes `(2, ±2)` only, under addition. -/
def modeProjStr : MeasStructure.{0} LigoKind addSig where
  carrier := Int × Int
  kind := .modeAmplitude
  op f xs := addPair f xs
  rel _ _ := False

/-- The projection preserves addition. -/
theorem proj22_preservesOperation : PreservesOperation modeStr modeProjStr proj22 := by
  intro n f xs
  cases f
  rfl

/-- The projection is a homomorphic association. -/
theorem proj22_homomorphic : HomomorphicAssociation modeStr modeProjStr proj22 :=
  ⟨proj22_preservesOperation, preservesEquality_of_sameness _, fun _ _ h => False.elim h⟩

/-- The projection is a valid measurement comparison in the sense of `Measure`: same quantity
kind and a homomorphic association. -/
theorem proj22_validMeasurementComparison : ValidMeasurementComparison modeStr modeProjStr proj22 :=
  ⟨rfl, proj22_homomorphic⟩

/-- **Kernel of the mode projection.**  The `(2, ±1)` amplitudes are invisible to `P`: states
that differ only in them have the same image, `P` vanishes exactly on the states without
`(2, ±2)` content, and a `(2, ±1)` amplitude of `3`, `−3` is lost against the state without
it. -/
theorem ligo_modeProjection_fibre :
    (∀ a b c d c' d' : Int, proj22 ⟨a, b, c, d⟩ = proj22 ⟨a, b, c', d'⟩) ∧
    proj22 ⟨5, 7, 0, 0⟩ = proj22 ⟨5, 7, 3, -3⟩ ∧
    (∀ h : ModeAmps, proj22 h = (0, 0) ↔ h.h22 = 0 ∧ h.h2m2 = 0) := by
  refine ⟨fun _ _ _ _ _ _ => rfl, by decide, ?_⟩
  intro h
  constructor
  · intro hp
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · intro hp
    exact pair_congr hp.1 hp.2

/-- The two states with equal `(2, ±2)` content and different `(2, ±1)` content are distinct. -/
theorem modeAmps_witness_ne : (⟨5, 7, 0, 0⟩ : ModeAmps) ≠ (⟨5, 7, 3, -3⟩ : ModeAmps) := by
  intro h
  have h' : (0 : Int) = 3 := congrArg ModeAmps.h21 h
  omega

/-- The projection exhibits two distinct states with the same image. -/
theorem modeProjection_fibre_witness :
    ∃ a₁ a₂ : ModeAmps, a₁ ≠ a₂ ∧ proj22 a₁ = proj22 a₂ :=
  ⟨⟨5, 7, 0, 0⟩, ⟨5, 7, 3, -3⟩, modeAmps_witness_ne, by decide⟩

/-- The mode projection is not injective. -/
theorem ligo_modeProjection_not_injective :
    ¬ Measure.Injective modeStr modeProjStr proj22 :=
  (fibre_obstructs (A := modeStr) (B := modeProjStr) (T := proj22)
    modeProjection_fibre_witness).1

/-- The mode projection does not admit full substitution. -/
theorem ligo_modeProjection_not_fullSubstitution :
    ¬ FullSubstitution modeStr modeProjStr proj22 :=
  (fibre_obstructs (A := modeStr) (B := modeProjStr) (T := proj22)
    modeProjection_fibre_witness).2.1

/-- The mode projection is no part of an exact calibration, over any calibrated range. -/
theorem ligo_modeProjection_no_exact_calibration (Bcal : modeProjStr.carrier → Prop) :
    ¬ Nonempty (ExactCalibration modeStr modeProjStr Bcal proj22) :=
  (fibre_obstructs (A := modeStr) (B := modeProjStr) (T := proj22)
    modeProjection_fibre_witness).2.2.1 Bcal

/-- The mode projection is the forward map of no isomorphism. -/
theorem ligo_modeProjection_not_isomorphic_transposition :
    ¬ IsomorphicTransposition modeStr modeProjStr proj22 :=
  (fibre_obstructs (A := modeStr) (B := modeProjStr) (T := proj22)
    modeProjection_fibre_witness).2.2.2

/-- **Homomorphism alone is not substitution.**  The projection is a valid measurement
comparison, and it is not injective. -/
theorem ligo_modeProjection_linear_not_injective :
    ValidMeasurementComparison modeStr modeProjStr proj22 ∧
    ¬ Measure.Injective modeStr modeProjStr proj22 :=
  ⟨proj22_validMeasurementComparison, ligo_modeProjection_not_injective⟩

/-! ## §5 The Gaussian likelihood of Equation (4)

Equation (4) reads `L(data | ϑ) ∝ exp(−½ Σₖ ⟨hₖ(ϑ) − dₖ | hₖ(ϑ) − dₖ⟩)`, summed over the two
detectors, with the noise-weighted inner product.  In whitened coordinates the noise-weighted
product is the Euclidean product.  A whitened residual `r` is a vector of integers (of any
length) and the exponent is `Λ(r) = Σᵢ rᵢ²`.  The likelihood is a function `g ∘ Λ` of the
exponent alone: `g(Λ) = exp(−Λ/2)` is one such function, and every function of `Λ` takes equal
values on equal exponents.  Residual strain and evidence weight are different quantity kinds
in `Measure`; the formal statements below keep the two layers apart. -/

/-- The sum of the squares of the components of a whitened residual: the exponent `Λ` of
Equation (4). -/
def gaussExponent : List Int → Int
  | [] => 0
  | x :: xs => x * x + gaussExponent xs

/-- The antipodal residual `−r`. -/
def resNeg : List Int → List Int
  | [] => []
  | x :: xs => (-x) :: resNeg xs

/-- Componentwise sum of two residuals. -/
def zipAdd : List Int → List Int → List Int
  | x :: xs, y :: ys => (x + y) :: zipAdd xs ys
  | _, _ => []

/-- The first component of a residual, `0` for the empty residual. -/
def headZ : List Int → Int
  | [] => 0
  | x :: _ => x

/-- Componentwise sum of residuals as an interpretation of the operation symbol. -/
def addList : {n : Nat} → AddOp n → (Fin n → List Int) → List Int
  | _, .add, xs => zipAdd (xs 0) (xs 1)

/-- `(−x)(−x) = x x`. -/
theorem int_neg_sq (x : Int) : (-x) * (-x) = x * x := by
  first
  | exact Int.neg_mul_neg x x
  | rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]

/-- The exponent is even: `Λ(−r) = Λ(r)`. -/
theorem gaussExponent_resNeg : ∀ r : List Int, gaussExponent (resNeg r) = gaussExponent r
  | [] => rfl
  | x :: xs => by
    show (-x) * (-x) + gaussExponent (resNeg xs) = x * x + gaussExponent xs
    rw [int_neg_sq x, gaussExponent_resNeg xs]

/-- The exponents of `[1]` and `[−1]` agree. -/
theorem exponent_pm_one : gaussExponent [1] = gaussExponent [-1] := by
  decide

/-- **Sign fibre and equal-exponent fibre of the likelihood.**  The exponent of `−r` equals
the exponent of `r`; every function `g` of the exponent, in particular `exp(−Λ/2)`, takes the
same value at `r` and at `−r`; a residual with a nonzero first component differs from its
negative; the residuals `(1, 0, 0, 3)` and `(2, 1, 1, 2)` are different and both have exponent
`10`. -/
theorem ligo_likelihood_sign_fibre :
    (∀ r : List Int, gaussExponent (resNeg r) = gaussExponent r) ∧
    (∀ (β : Type) (g : Int → β) (r : List Int),
      g (gaussExponent (resNeg r)) = g (gaussExponent r)) ∧
    (∀ (x : Int) (xs : List Int), x ≠ 0 → resNeg (x :: xs) ≠ x :: xs) ∧
    gaussExponent [1, 0, 0, 3] = 10 ∧ gaussExponent [2, 1, 1, 2] = 10 ∧
    ([1, 0, 0, 3] : List Int) ≠ [2, 1, 1, 2] := by
  refine ⟨gaussExponent_resNeg, ?_, ?_, by decide, by decide, ?_⟩
  · intro β g r
    exact congrArg g (gaussExponent_resNeg r)
  · intro x xs hx h
    have h' : -x = x := congrArg headZ h
    omega
  · intro h
    have h' : (1 : Int) = 2 := congrArg headZ h
    omega

/-- The two residuals `[1]` and `[−1]` are distinct and have the same exponent. -/
theorem likelihood_fibre_witness (β : Type) (g : Int → β) :
    ∃ a₁ a₂ : List Int, a₁ ≠ a₂ ∧ g (gaussExponent a₁) = g (gaussExponent a₂) := by
  refine ⟨[1], [-1], ?_, congrArg g exponent_pm_one⟩
  intro h
  have h' : (1 : Int) = -1 := congrArg headZ h
  omega

/-- Whitened residuals of quantity kind strain, with no operation and no relation. -/
def resBare : MeasStructure.{0} LigoKind bareSig where
  carrier := List Int
  kind := .strain
  op f xs := noOp f xs
  rel _ _ := False

/-- Values of a function of the exponent, of quantity kind evidence weight, with no operation
and no relation. -/
def weightBare (β : Type) : MeasStructure.{0} LigoKind bareSig where
  carrier := β
  kind := .evidenceWeight
  op f xs := noOp f xs
  rel _ _ := False

/-- **No function of the exponent is injective on residuals.**  The likelihood map
`r ↦ g (Λ r)` is not injective, for every `g`. -/
theorem ligo_likelihood_not_injective (β : Type) (g : Int → β) :
    ¬ Measure.Injective resBare (weightBare β) (fun r => g (gaussExponent r)) :=
  (fibre_obstructs (A := resBare) (B := weightBare β) (T := fun r => g (gaussExponent r))
    (likelihood_fibre_witness β g)).1

/-- The likelihood map does not admit full substitution of residuals. -/
theorem ligo_likelihood_not_fullSubstitution (β : Type) (g : Int → β) :
    ¬ FullSubstitution resBare (weightBare β) (fun r => g (gaussExponent r)) :=
  (fibre_obstructs (A := resBare) (B := weightBare β) (T := fun r => g (gaussExponent r))
    (likelihood_fibre_witness β g)).2.1

/-- The likelihood map is no part of an exact calibration of residuals, over any calibrated
range. -/
theorem ligo_likelihood_no_exact_calibration (β : Type) (g : Int → β)
    (Bcal : (weightBare β).carrier → Prop) :
    ¬ Nonempty (ExactCalibration resBare (weightBare β) Bcal (fun r => g (gaussExponent r))) :=
  (fibre_obstructs (A := resBare) (B := weightBare β) (T := fun r => g (gaussExponent r))
    (likelihood_fibre_witness β g)).2.2.1 Bcal

/-- The likelihood map is the forward map of no isomorphism. -/
theorem ligo_likelihood_not_isomorphic_transposition (β : Type) (g : Int → β) :
    ¬ IsomorphicTransposition resBare (weightBare β) (fun r => g (gaussExponent r)) :=
  (fibre_obstructs (A := resBare) (B := weightBare β) (T := fun r => g (gaussExponent r))
    (likelihood_fibre_witness β g)).2.2.2

/-- Residuals under componentwise addition. -/
def resStr : MeasStructure.{0} LigoKind addSig where
  carrier := List Int
  kind := .strain
  op f xs := addList f xs
  rel _ _ := False

/-- Exponent values under addition, of quantity kind evidence weight. -/
def weightStr : MeasStructure.{0} LigoKind addSig where
  carrier := Int
  kind := .evidenceWeight
  op f xs := addInt f xs
  rel _ _ := False

/-- **The exponent is quadratic, not additive.**  For the residual `r = (1)`,
`Λ(r + r) = 4` while `Λ(r) + Λ(r) = 2`. -/
theorem ligo_likelihood_not_additive : ¬ PreservesOperation resStr weightStr gaussExponent :=
  not_preservesOperation_of_noncommuting (A := resStr) (B := weightStr) (T := gaussExponent)
    AddOp.add (fun _ => ([1] : List Int)) (by change (4 : Int) ≠ 2; decide)

/-- Residual strain and evidence weight are different quantity kinds. -/
theorem residual_weight_not_sameKind : ¬ SameKind resStr weightStr := by
  intro h
  cases h

/-- **Kind separation.**  Residual strain and evidence weight are different quantity kinds: no
map from residuals to exponent values is a valid measurement comparison, no exact calibration
exists over any range, and the two representations are not isomorphic.  The relation of a
likelihood to a residual rests on an evidential relation of the target, which `Measure` does
not contain. -/
theorem ligo_residual_weight_not_comparable :
    ¬ SameKind resStr weightStr ∧
    (∀ T : List Int → Int, ¬ ValidMeasurementComparison resStr weightStr T) ∧
    (∀ (Bcal : Int → Prop) (T : List Int → Int),
      ¬ Nonempty (ExactCalibration resStr weightStr Bcal T)) ∧
    ¬ Isomorphic resStr weightStr :=
  different_quantity_kind_implies_not_comparable residual_weight_not_sameKind

/-! ## §6 The six spin degrees of freedom of precessing IMRPhenom

Precessing IMRPhenom has four independent parameters for the six spin degrees of freedom: the
nonprecessing waveform it rotates depends on the two spin projections on the Newtonian orbital
angular momentum, and the in-plane spins enter through a single spin parameter and the phase of
the binary in the orbital plane (Sec. II).  The paper states that binaries with identical
projection of the total spin on the orbital plane have identical waveforms in this model
(Sec. IV, on `φ₁₂`).  `Spin6` holds the spin components `(S₁ₓ, S₁ᵧ, S₁ᵤ, S₂ₓ, S₂ᵧ, S₂ᵤ)` with
the `z`-axis along the orbital angular momentum; `Spin4` holds the two aligned components and
the total in-plane projection `(S₁ₓ + S₂ₓ, S₁ᵧ + S₂ᵧ)`. -/

/-- The six spin components, `z` along the Newtonian orbital angular momentum. -/
structure Spin6 where
  s1x : Int
  s1y : Int
  s1z : Int
  s2x : Int
  s2y : Int
  s2z : Int

/-- The four spin parameters of the model: the aligned components and the total in-plane
projection. -/
structure Spin4 where
  z1 : Int
  z2 : Int
  px : Int
  py : Int

/-- Componentwise addition of spin components. -/
def addSpin6 : {n : Nat} → AddOp n → (Fin n → Spin6) → Spin6
  | _, .add, xs => ⟨(xs 0).s1x + (xs 1).s1x, (xs 0).s1y + (xs 1).s1y, (xs 0).s1z + (xs 1).s1z,
      (xs 0).s2x + (xs 1).s2x, (xs 0).s2y + (xs 1).s2y, (xs 0).s2z + (xs 1).s2z⟩

/-- Componentwise addition of model spin parameters. -/
def addSpin4 : {n : Nat} → AddOp n → (Fin n → Spin4) → Spin4
  | _, .add, xs => ⟨(xs 0).z1 + (xs 1).z1, (xs 0).z2 + (xs 1).z2,
      (xs 0).px + (xs 1).px, (xs 0).py + (xs 1).py⟩

/-- The compression of the six spin components to the four parameters of the model. -/
def imrSpin (s : Spin6) : Spin4 := ⟨s.s1z, s.s2z, s.s1x + s.s2x, s.s1y + s.s2y⟩

/-- Six spin components under addition. -/
def spin6Str : MeasStructure.{0} LigoKind addSig where
  carrier := Spin6
  kind := .spin
  op f xs := addSpin6 f xs
  rel _ _ := False

/-- Four model spin parameters under addition. -/
def spin4Str : MeasStructure.{0} LigoKind addSig where
  carrier := Spin4
  kind := .spin
  op f xs := addSpin4 f xs
  rel _ _ := False

/-- Equality of `Spin4` from equality of components. -/
theorem spin4_congr {a b c d a' b' c' d' : Int} (h₁ : a = a') (h₂ : b = b') (h₃ : c = c')
    (h₄ : d = d') : (⟨a, b, c, d⟩ : Spin4) = (⟨a', b', c', d'⟩ : Spin4) := by
  subst h₁
  subst h₂
  subst h₃
  subst h₄
  rfl

/-- The compression preserves addition. -/
theorem imrSpin_preservesOperation : PreservesOperation spin6Str spin4Str imrSpin := by
  intro n f xs
  cases f
  show (⟨(xs 0).s1z + (xs 1).s1z, (xs 0).s2z + (xs 1).s2z,
        (xs 0).s1x + (xs 1).s1x + ((xs 0).s2x + (xs 1).s2x),
        (xs 0).s1y + (xs 1).s1y + ((xs 0).s2y + (xs 1).s2y)⟩ : Spin4) =
      (⟨(xs 0).s1z + (xs 1).s1z, (xs 0).s2z + (xs 1).s2z,
        (xs 0).s1x + (xs 0).s2x + ((xs 1).s1x + (xs 1).s2x),
        (xs 0).s1y + (xs 0).s2y + ((xs 1).s1y + (xs 1).s2y)⟩ : Spin4)
  exact spin4_congr rfl rfl (by omega) (by omega)

/-- The compression is a homomorphic association. -/
theorem imrSpin_homomorphic : HomomorphicAssociation spin6Str spin4Str imrSpin :=
  ⟨imrSpin_preservesOperation, preservesEquality_of_sameness _, fun _ _ h => False.elim h⟩

/-- States with the same aligned components and the same total in-plane projection have the
same image. -/
theorem imrSpin_eq_of {s s' : Spin6} (h1 : s.s1z = s'.s1z) (h2 : s.s2z = s'.s2z)
    (h3 : s.s1x + s.s2x = s'.s1x + s'.s2x) (h4 : s.s1y + s.s2y = s'.s1y + s'.s2y) :
    imrSpin s = imrSpin s' :=
  spin4_congr h1 h2 h3 h4

/-- The compression is onto the four parameters of the model. -/
theorem imrSpin_surjective : ∀ t : Spin4, ∃ s : Spin6, imrSpin s = t := by
  intro t
  obtain ⟨z1, z2, px, py⟩ := t
  refine ⟨⟨px, py, z1, 0, 0, z2⟩, ?_⟩
  show (⟨z1, z2, px + 0, py + 0⟩ : Spin4) = (⟨z1, z2, px, py⟩ : Spin4)
  exact spin4_congr rfl rfl (by omega) (by omega)

/-- **Spin-compression fibre of precessing IMRPhenom.**  Spin states with equal aligned
components and equal total in-plane projection have equal images; a two-parameter family of
nonzero in-plane spin pairs `(u, v, 0, −u, −v, 0)` has the image of the zero spin state; the
states `(1, 0, 0, 0, 0, 0)` and `(0, 0, 0, 1, 0, 0)` have the same total in-plane projection
`(1, 0)` and are distinct. -/
theorem ligo_imrPhenom_spinCompression_fibre :
    (∀ s s' : Spin6, s.s1z = s'.s1z → s.s2z = s'.s2z →
      s.s1x + s.s2x = s'.s1x + s'.s2x → s.s1y + s.s2y = s'.s1y + s'.s2y →
      imrSpin s = imrSpin s') ∧
    (∀ u v : Int, imrSpin ⟨u, v, 0, -u, -v, 0⟩ = imrSpin ⟨0, 0, 0, 0, 0, 0⟩) ∧
    imrSpin ⟨1, 0, 0, 0, 0, 0⟩ = imrSpin ⟨0, 0, 0, 1, 0, 0⟩ ∧
    (⟨1, 0, 0, 0, 0, 0⟩ : Spin6) ≠ (⟨0, 0, 0, 1, 0, 0⟩ : Spin6) := by
  refine ⟨fun _ _ h1 h2 h3 h4 => imrSpin_eq_of h1 h2 h3 h4, ?_, ?_, ?_⟩
  · intro u v
    exact imrSpin_eq_of rfl rfl (by show u + -u = (0 : Int) + 0; omega)
      (by show v + -v = (0 : Int) + 0; omega)
  · exact imrSpin_eq_of rfl rfl (by decide) (by decide)
  · intro h
    have h' : (1 : Int) = 0 := congrArg Spin6.s1x h
    omega

/-- The compression exhibits two distinct states with the same image. -/
theorem imrSpin_fibre_witness :
    ∃ a₁ a₂ : Spin6, a₁ ≠ a₂ ∧ imrSpin a₁ = imrSpin a₂ :=
  ⟨⟨1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 1, 0, 0⟩, ligo_imrPhenom_spinCompression_fibre.2.2.2,
    ligo_imrPhenom_spinCompression_fibre.2.2.1⟩

/-- The spin compression is not injective. -/
theorem ligo_imrPhenom_spinCompression_not_injective :
    ¬ Measure.Injective spin6Str spin4Str imrSpin :=
  (fibre_obstructs (A := spin6Str) (B := spin4Str) (T := imrSpin) imrSpin_fibre_witness).1

/-- The spin compression does not admit full substitution of the six spin components. -/
theorem ligo_imrPhenom_spinCompression_not_fullSubstitution :
    ¬ FullSubstitution spin6Str spin4Str imrSpin :=
  (fibre_obstructs (A := spin6Str) (B := spin4Str) (T := imrSpin) imrSpin_fibre_witness).2.1

/-- The spin compression is no part of an exact calibration, over any calibrated range. -/
theorem ligo_imrPhenom_spinCompression_no_exact_calibration (Bcal : spin4Str.carrier → Prop) :
    ¬ Nonempty (ExactCalibration spin6Str spin4Str Bcal imrSpin) :=
  (fibre_obstructs (A := spin6Str) (B := spin4Str) (T := imrSpin)
    imrSpin_fibre_witness).2.2.1 Bcal

/-- The spin compression is the forward map of no isomorphism. -/
theorem ligo_imrPhenom_spinCompression_not_isomorphic_transposition :
    ¬ IsomorphicTransposition spin6Str spin4Str imrSpin :=
  (fibre_obstructs (A := spin6Str) (B := spin4Str) (T := imrSpin)
    imrSpin_fibre_witness).2.2.2

end LigoSpecious

end
