module

public import RequestProject.Measurement
public import RequestProject.LIGO_specious_measures

/-!
# The published values of GW150914 against the structures of `Measure`

Table I of Abbott et al., *Improved analysis of GW150914 using a fully spin-precessing waveform
model*, Phys. Rev. X 6, 041014 (2016), reports for every source parameter the median of a
posterior distribution.  A posterior carries structure that its median does not carry: the
detector-frame total mass is the sum of the detector-frame component masses, and every
detector-frame mass is `1 + z` times the corresponding source-frame mass.  The map `T` from
posteriors to printed medians is a homomorphic association exactly when it carries these
relations to the printed values, and the printed values decide whether it does.

Printed values are natural numbers in a fixed unit: masses in hundredths of a solar mass,
redshifts in units of `10⁻⁴`, probabilities in basis points, spin magnitudes and mass ratios in
thousandths.  A value printed to `k` decimals stands for its round-to-nearest interval, so each
hypothesis on `T` below is a closed interval of naturals.  The structure `A` of posteriors is an
arbitrary measured representation over the signature of addition and the redshift relation; the
hypotheses fix the values of `T` at the posteriors involved.

* §1 Additivity.  The medians of `m₁`, `m₂` and `M` of the column precessing IMRPhenom admit no
  map `T` that preserves addition.
* §2 The redshift relation.  The total mass of precessing EOBNR and the total, secondary and
  final masses of precessing IMRPhenom admit no map `T` that preserves `M_det = (1 + z) M_src`.
* §3 The Kolmogorov–Smirnov p-values of `φ₁₂` (Sec. IV).  The stated range for precessing
  EOBNR lies on both sides of the threshold `0.05` that the paper fixes in Sec. III.
* §4 Calibration scope.  The injection SXS:BBH:0308 and every published 90% upper bound on a spin
  magnitude lie outside the calibrated region of the precessing models.  The inclusion of the
  calibrated region into the stated domain is injective and homomorphic; the obstruction to an
  exact calibration over the stated domain is its range.
-/

@[expose] public section

namespace LigoSpecious

open Measure

/-! ## Reported values

The structure `natStr` carries addition and the ternary redshift relation.  For a detector-frame
value `d` and a source-frame value `s`, both in hundredths of a solar mass, and `Z = 10⁴ z`, the
relation `d = (1 + z) s` reads `10⁴ d = (10⁴ + Z) s`. -/

/-- Relation symbols of the reported values: the ternary redshift relation. -/
inductive TableRel : Nat → Type where
  | redshift : TableRel 3

/-- The signature of the reported values: addition and the redshift relation. -/
def tableSig : Signature := ⟨AddOp, TableRel⟩

/-- Addition on `ℕ`. -/
def addNat : {n : Nat} → AddOp n → (Fin n → Nat) → Nat
  | _, .add, xs => xs 0 + xs 1

/-- The redshift relation on reported values: detector-frame value `d`, `Z = 10⁴ z` and
source-frame value `s` satisfy `10⁴ d = (10⁴ + Z) s`. -/
def tableRel : {n : Nat} → TableRel n → (Fin n → Nat) → Prop
  | _, .redshift, xs => 10000 * xs 0 = (10000 + xs 1) * xs 2

/-- Reported values with addition and the redshift relation. -/
def natStr : MeasStructure.{0} LigoKind tableSig where
  carrier := Nat
  kind := .tableValue
  op f xs := addNat f xs
  rel r xs := tableRel r xs

/-! ## §1 Additivity of the medians

If `xs 0` and `xs 1` are posteriors and `A.op add xs` is the posterior of their sum, a map `T`
that preserves addition has `T (A.op add xs) = T (xs 0) + T (xs 1)`.  Printed intervals for the
three values rule this out when the interval of the sum lies beyond the sum of the intervals. -/

/-- **Additivity certificate.**  The values of `T` at `xs 0`, `xs 1` and at the sum lie in the
intervals `[aLo, aHi]`, `[bLo, bHi]` and `[cLo, cHi]`.  If `aHi + bHi < cLo` or
`cHi < aLo + bLo`, then `T` does not preserve addition. -/
theorem tableI_median_not_additive (A : MeasStructure.{0} LigoKind tableSig)
    (T : A.carrier → Nat) (xs : Fin 2 → A.carrier) (aLo aHi bLo bHi cLo cHi : Nat)
    (ha : aLo ≤ T (xs 0) ∧ T (xs 0) ≤ aHi) (hb : bLo ≤ T (xs 1) ∧ T (xs 1) ≤ bHi)
    (hc : cLo ≤ T (A.op AddOp.add xs) ∧ T (A.op AddOp.add xs) ≤ cHi)
    (hgap : aHi + bHi < cLo ∨ cHi < aLo + bLo) :
    ¬ PreservesOperation A natStr T := by
  intro h
  have h' : T (A.op AddOp.add xs) = T (xs 0) + T (xs 1) := h AddOp.add xs
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  rcases hgap with hg | hg
  · omega
  · omega

/-- **Table I, precessing IMRPhenom: the medians do not add.**  The column prints
`m₁ = 38.5`, `m₂ = 32.2` and `M = 70.9`, with intervals `[38.45, 38.55]`, `[32.15, 32.25]` and
`[70.85, 70.95]`, in hundredths `[3845, 3855]`, `[3215, 3225]` and `[7085, 7095]`.  The sum of
the upper ends is `7080 < 7085`.  A map `T` taking these values at the posteriors of `m₁`, `m₂`
and `m₁ + m₂` preserves no addition, is no valid measurement comparison, and lies in no exact
calibration over any range. -/
theorem ligo_tableI_imrphenom_median_not_additive (A : MeasStructure.{0} LigoKind tableSig)
    (T : A.carrier → Nat) (xs : Fin 2 → A.carrier)
    (hm1 : 3845 ≤ T (xs 0) ∧ T (xs 0) ≤ 3855)
    (hm2 : 3215 ≤ T (xs 1) ∧ T (xs 1) ≤ 3225)
    (hM : 7085 ≤ T (A.op AddOp.add xs) ∧ T (A.op AddOp.add xs) ≤ 7095) :
    ¬ PreservesOperation A natStr T ∧ ¬ ValidMeasurementComparison A natStr T ∧
    ∀ Bcal : natStr.carrier → Prop, ¬ Nonempty (ExactCalibration A natStr Bcal T) := by
  have h : ¬ PreservesOperation A natStr T :=
    tableI_median_not_additive A T xs 3845 3855 3215 3225 7085 7095 hm1 hm2 hM
      (Or.inl (by decide))
  obtain ⟨_, hv, hc⟩ := not_hom_implies_not_valid h
  exact ⟨h, hv, hc⟩

/-! ## §2 The redshift relation on the medians

Detector-frame value, redshift and source-frame value of one object satisfy
`d = (1 + z) s` at every sample of the posterior.  If `A` carries this relation at `xs`, a map
`T` that preserves relations satisfies `10⁴ T(xs 0) = (10⁴ + T(xs 1)) T(xs 2)`.  Printed
intervals for the three values rule this out when the two sides of the relation, evaluated at the
extreme ends of the intervals, do not meet. -/

/-- **Redshift certificate.**  `A` carries the redshift relation at `xs`.  The values of `T` at
`xs 0`, `xs 1` and `xs 2` lie in the intervals `[dLo, dHi]`, `[zLo, zHi]` and `[sLo, sHi]`.  If
`10⁴ dHi < (10⁴ + zLo) sLo` or `(10⁴ + zHi) sHi < 10⁴ dLo`, then `T` does not preserve the
relation. -/
theorem tableI_median_not_redshift_relation (A : MeasStructure.{0} LigoKind tableSig)
    (T : A.carrier → Nat) (xs : Fin 3 → A.carrier) (hA : A.rel TableRel.redshift xs)
    (dLo dHi zLo zHi sLo sHi : Nat)
    (hd : dLo ≤ T (xs 0) ∧ T (xs 0) ≤ dHi) (hz : zLo ≤ T (xs 1) ∧ T (xs 1) ≤ zHi)
    (hs : sLo ≤ T (xs 2) ∧ T (xs 2) ≤ sHi)
    (hgap : 10000 * dHi < (10000 + zLo) * sLo ∨ (10000 + zHi) * sHi < 10000 * dLo) :
    ¬ PreservesRelation A natStr T := by
  intro h
  have h' : 10000 * T (xs 0) = (10000 + T (xs 1)) * T (xs 2) := h TableRel.redshift xs hA
  obtain ⟨hd1, hd2⟩ := hd
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hs1, hs2⟩ := hs
  have hlo : (10000 + zLo) * sLo ≤ (10000 + T (xs 1)) * T (xs 2) :=
    Nat.mul_le_mul (by omega) hs1
  have hhi : (10000 + T (xs 1)) * T (xs 2) ≤ (10000 + zHi) * sHi :=
    Nat.mul_le_mul (by omega) hs2
  rcases hgap with hg | hg
  · omega
  · omega

/-- **Table I, precessing EOBNR: total mass.**  The column prints `M = 71.6`, `z = 0.094` and
`M_source = 65.6`, with intervals `[71.55, 71.65]`, `[0.0935, 0.0945]` and `[65.55, 65.65]`, in
the units of the module `[7155, 7165]`, `[935, 945]` and `[6555, 6565]`.  The detector-frame value
is at most `71.65`, and `(1 + 0.0935) · 65.55 = 71.678925` exceeds it:
`10000 · 7165 = 71650000 < 71678925 = 10935 · 6555`. -/
theorem ligo_tableI_eobnr_totalMass_not_redshift (A : MeasStructure.{0} LigoKind tableSig)
    (T : A.carrier → Nat) (xs : Fin 3 → A.carrier) (hA : A.rel TableRel.redshift xs)
    (hd : 7155 ≤ T (xs 0) ∧ T (xs 0) ≤ 7165)
    (hz : 935 ≤ T (xs 1) ∧ T (xs 1) ≤ 945)
    (hs : 6555 ≤ T (xs 2) ∧ T (xs 2) ≤ 6565) :
    ¬ PreservesRelation A natStr T ∧ ¬ ValidMeasurementComparison A natStr T ∧
    ∀ Bcal : natStr.carrier → Prop, ¬ Nonempty (ExactCalibration A natStr Bcal T) := by
  have h : ¬ PreservesRelation A natStr T :=
    tableI_median_not_redshift_relation A T xs hA 7155 7165 935 945 6555 6565 hd hz hs
      (Or.inl (by decide))
  exact ⟨h, fun hv => h hv.2.2.2, fun _ ⟨C⟩ => h C.hom.2.2⟩

/-- **Table I, precessing IMRPhenom: total mass.**  The column prints `M = 70.9`, `z = 0.093`
and `M_source = 65.0`, with intervals `[70.85, 70.95]`, `[0.0925, 0.0935]` and `[64.95, 65.05]`,
in the units of the module `[7085, 7095]`, `[925, 935]` and `[6495, 6505]`:
`10000 · 7095 = 70950000 < 70957875 = 10925 · 6495`. -/
theorem ligo_tableI_imrphenom_totalMass_not_redshift (A : MeasStructure.{0} LigoKind tableSig)
    (T : A.carrier → Nat) (xs : Fin 3 → A.carrier) (hA : A.rel TableRel.redshift xs)
    (hd : 7085 ≤ T (xs 0) ∧ T (xs 0) ≤ 7095)
    (hz : 925 ≤ T (xs 1) ∧ T (xs 1) ≤ 935)
    (hs : 6495 ≤ T (xs 2) ∧ T (xs 2) ≤ 6505) :
    ¬ PreservesRelation A natStr T ∧ ¬ ValidMeasurementComparison A natStr T ∧
    ∀ Bcal : natStr.carrier → Prop, ¬ Nonempty (ExactCalibration A natStr Bcal T) := by
  have h : ¬ PreservesRelation A natStr T :=
    tableI_median_not_redshift_relation A T xs hA 7085 7095 925 935 6495 6505 hd hz hs
      (Or.inl (by decide))
  exact ⟨h, fun hv => h hv.2.2.2, fun _ ⟨C⟩ => h C.hom.2.2⟩

/-- **Table I, precessing IMRPhenom: secondary mass.**  The column prints `m₂ = 32.2` and
`m₂_source = 29.6`, with intervals `[32.15, 32.25]` and `[29.55, 29.65]`, in hundredths
`[3215, 3225]` and `[2955, 2965]`, and `z = 0.093` in `[925, 935]`:
`10000 · 3225 = 32250000 < 32283375 = 10925 · 2955`. -/
theorem ligo_tableI_imrphenom_secondaryMass_not_redshift
    (A : MeasStructure.{0} LigoKind tableSig)
    (T : A.carrier → Nat) (xs : Fin 3 → A.carrier) (hA : A.rel TableRel.redshift xs)
    (hd : 3215 ≤ T (xs 0) ∧ T (xs 0) ≤ 3225)
    (hz : 925 ≤ T (xs 1) ∧ T (xs 1) ≤ 935)
    (hs : 2955 ≤ T (xs 2) ∧ T (xs 2) ≤ 2965) :
    ¬ PreservesRelation A natStr T ∧ ¬ ValidMeasurementComparison A natStr T ∧
    ∀ Bcal : natStr.carrier → Prop, ¬ Nonempty (ExactCalibration A natStr Bcal T) := by
  have h : ¬ PreservesRelation A natStr T :=
    tableI_median_not_redshift_relation A T xs hA 3215 3225 925 935 2955 2965 hd hz hs
      (Or.inl (by decide))
  exact ⟨h, fun hv => h hv.2.2.2, fun _ ⟨C⟩ => h C.hom.2.2⟩

/-- **Table I, precessing IMRPhenom: final mass.**  The column prints `M_f = 67.6` and
`M_f_source = 62.0`, with intervals `[67.55, 67.65]` and `[61.95, 62.05]`, in hundredths
`[6755, 6765]` and `[6195, 6205]`, and `z = 0.093` in `[925, 935]`:
`10000 · 6765 = 67650000 < 67680375 = 10925 · 6195`. -/
theorem ligo_tableI_imrphenom_finalMass_not_redshift (A : MeasStructure.{0} LigoKind tableSig)
    (T : A.carrier → Nat) (xs : Fin 3 → A.carrier) (hA : A.rel TableRel.redshift xs)
    (hd : 6755 ≤ T (xs 0) ∧ T (xs 0) ≤ 6765)
    (hz : 925 ≤ T (xs 1) ∧ T (xs 1) ≤ 935)
    (hs : 6195 ≤ T (xs 2) ∧ T (xs 2) ≤ 6205) :
    ¬ PreservesRelation A natStr T ∧ ¬ ValidMeasurementComparison A natStr T ∧
    ∀ Bcal : natStr.carrier → Prop, ¬ Nonempty (ExactCalibration A natStr Bcal T) := by
  have h : ¬ PreservesRelation A natStr T :=
    tableI_median_not_redshift_relation A T xs hA 6755 6765 925 935 6195 6205 hd hz hs
      (Or.inl (by decide))
  exact ⟨h, fun hv => h hv.2.2.2, fun _ ⟨C⟩ => h C.hom.2.2⟩

/-! ## §3 The Kolmogorov–Smirnov verdict on `φ₁₂`

Sec. III fixes the criterion: p-values smaller than `0.05` indicate that the samples come from a
different distribution with a high level of significance.  Sec. IV states that the precessing
EOBNR posterior of `φ₁₂` deviates significantly from the prior, with KS p-value in
`[0.0077, 0.075]`, and that the precessing IMRPhenom posterior does not, with KS p-value in
`[0.30, 0.60]`.  In basis points the ranges are `[77, 750]` and `[3000, 6000]`, and the threshold
is `500`. -/

/-- The verdict of the criterion of Sec. III on a p-value in basis points: `true` exactly when
`p < 0.05`. -/
def ksVerdict (p : Nat) : Bool := if p < 500 then true else false

/-- **The stated range of the EOBNR p-value contains both verdicts.**  The verdict is `true` on
`[0.0077, 0.05)` and `false` on `[0.05, 0.075]`; the endpoints `0.0077` and `0.075` of the stated
range have opposite verdicts.  On the stated range `[0.30, 0.60]` of precessing IMRPhenom the
verdict is `false` throughout. -/
theorem ligo_ks_phi12_verdict_split :
    (ksVerdict 77 = true ∧ ksVerdict 750 = false) ∧
    (∀ p : Nat, 77 ≤ p → p < 500 → ksVerdict p = true) ∧
    (∀ p : Nat, 500 ≤ p → p ≤ 750 → ksVerdict p = false) ∧
    (∀ p : Nat, 3000 ≤ p → p ≤ 6000 → ksVerdict p = false) := by
  refine ⟨⟨by decide, by decide⟩, ?_, ?_, ?_⟩
  · intro p _ h2
    show (if p < 500 then true else false) = true
    rw [if_pos h2]
  · intro p h1 _
    show (if p < 500 then true else false) = false
    rw [if_neg (by omega : ¬ p < 500)]
  · intro p h1 _
    show (if p < 500 then true else false) = false
    rw [if_neg (by omega : ¬ p < 500)]

/-! ## §4 Calibration scope

Sec. II gives the stated domain of the precessing EOBNR model: mass ratio `0.01 ≤ q ≤ 1` and spin
magnitudes `0 ≤ χ₁, χ₂ ≤ 0.99`.  It gives the calibration to numerical relativity as 38
simulations of nonprecessing-spin systems with mass ratios up to `1/8`, spin magnitudes up to
almost extremal for equal-mass binaries and up to `0.5` for unequal-mass binaries; neither
precessing model is calibrated to a precessing simulation.  Sec. II also describes the same set
once as 38 nonspinning simulations; `calibratedRegion` takes the wider description, so every
failure below holds a fortiori for the narrower one.

A point of the parameter space is `(q, a₁, a₂)` in thousandths.  The stated domain and the
calibrated region are decidable subsets, and the inclusion of the second into the first has no
fibre: the obstruction to an exact calibration over the stated domain is surjectivity, the range
of validity. -/

/-- A point `(q, a₁, a₂)` of the parameter space: the mass ratio and the two spin magnitudes,
in thousandths. -/
structure ParamPoint where
  q : Nat
  a1 : Nat
  a2 : Nat

/-- The stated domain: `0.01 ≤ q ≤ 1` and `a₁, a₂ ≤ 0.99`. -/
abbrev statedDomain (p : ParamPoint) : Prop :=
  10 ≤ p.q ∧ p.q ≤ 1000 ∧ p.a1 ≤ 990 ∧ p.a2 ≤ 990

/-- The calibrated region: `q ≥ 1/8`, spins at most `0.99`, and spins at most `0.5` unless the
masses are equal. -/
abbrev calibratedRegion (p : ParamPoint) : Prop :=
  125 ≤ p.q ∧ p.q ≤ 1000 ∧ (p.q = 1000 ∨ (p.a1 ≤ 500 ∧ p.a2 ≤ 500)) ∧ p.a1 ≤ 990 ∧ p.a2 ≤ 990

/-- Points of the stated domain. -/
abbrev StatedPoint : Type := {p : ParamPoint // statedDomain p}

/-- Points of the calibrated region. -/
abbrev CalPoint : Type := {p : ParamPoint // calibratedRegion p}

/-- The stated domain, with no operation and no relation. -/
def statedStr : MeasStructure.{0} LigoKind bareSig where
  carrier := StatedPoint
  kind := .parameterPoint
  op f xs := noOp f xs
  rel _ _ := False

/-- The calibrated region, with no operation and no relation. -/
def calStr : MeasStructure.{0} LigoKind bareSig where
  carrier := CalPoint
  kind := .parameterPoint
  op f xs := noOp f xs
  rel _ _ := False

/-- The calibrated region lies in the stated domain. -/
theorem calibrated_subset (p : ParamPoint) (h : calibratedRegion p) : statedDomain p := by
  obtain ⟨h1, h2, _, h3, h4⟩ := h
  exact ⟨by omega, h2, h3, h4⟩

/-- The inclusion of the calibrated region into the stated domain. -/
def calEmbed (a : CalPoint) : StatedPoint :=
  ⟨Subtype.val a, calibrated_subset (Subtype.val a) (Subtype.property a)⟩

/-- The inclusion preserves every operation: there are none. -/
theorem calEmbed_preservesOperation : PreservesOperation calStr statedStr calEmbed := by
  intro n f xs
  first
  | exact Empty.elim f
  | cases f

/-- The inclusion is a homomorphic association. -/
theorem calEmbed_homomorphic : HomomorphicAssociation calStr statedStr calEmbed :=
  ⟨calEmbed_preservesOperation, preservesEquality_of_sameness _, fun _ _ h => False.elim h⟩

/-- The inclusion is injective: it has no fibre. -/
theorem calEmbed_injective : Measure.Injective calStr statedStr calEmbed := by
  intro a₁ a₂ h
  obtain ⟨p₁, hp₁⟩ := a₁
  obtain ⟨p₂, hp₂⟩ := a₂
  have h2 : (calEmbed ⟨p₁, hp₁⟩ : StatedPoint) = calEmbed ⟨p₂, hp₂⟩ := h
  have h3 : p₁ = p₂ := congrArg Subtype.val h2
  subst h3
  rfl

/-- The point `q = 0.84`, `a₁ = 0.54`, `a₂ = 0` of the stated domain: the median mass ratio of
Table I with the 90% upper bound on the primary spin of precessing EOBNR. -/
def uncalibratedPoint : StatedPoint := ⟨⟨840, 540, 0⟩, by decide⟩

/-- **Calibration scope.**  The inclusion of the calibrated region into the stated domain is a
valid measurement comparison and is injective.  It admits no exact calibration over any range
that contains the point `(0.84, 0.54, 0)`, in particular over the stated domain: the failure is
the range, and no fibre is involved. -/
theorem ligo_calibration_scope_not_exact :
    ValidMeasurementComparison calStr statedStr calEmbed ∧
    Measure.Injective calStr statedStr calEmbed ∧
    ∀ Bcal : statedStr.carrier → Prop, Bcal uncalibratedPoint →
      ¬ Nonempty (ExactCalibration calStr statedStr Bcal calEmbed) := by
  refine ⟨⟨rfl, calEmbed_homomorphic⟩, calEmbed_injective, ?_⟩
  intro Bcal hB
  apply not_surjective_implies_not_calibration
  refine ⟨uncalibratedPoint, hB, ?_⟩
  intro a h
  obtain ⟨p, hp⟩ := a
  have h2 : (calEmbed ⟨p, hp⟩ : StatedPoint) = uncalibratedPoint := h
  have h3 : p = (⟨840, 540, 0⟩ : ParamPoint) := congrArg Subtype.val h2
  subst h3
  exact absurd hp (by decide)

/-- A point with a mass ratio below `1` and a spin magnitude above `0.5` is not calibrated. -/
theorem not_calibrated_of_spin (q a1 a2 : Nat) (hq : q < 1000) (h : 500 < a1 ∨ 500 < a2) :
    ¬ calibratedRegion ⟨q, a1, a2⟩ := by
  intro hc
  have hc' : 125 ≤ q ∧ q ≤ 1000 ∧ (q = 1000 ∨ (a1 ≤ 500 ∧ a2 ≤ 500)) ∧ a1 ≤ 990 ∧
      a2 ≤ 990 := hc
  clear hc
  obtain ⟨_, _, hs, _, _⟩ := hc'
  rcases hs with hs | ⟨hs1, hs2⟩
  · omega
  · rcases h with h | h
    · omega
    · omega

/-- **The injection lies outside the calibrated region.**  The numerical-relativity waveform
SXS:BBH:0308 has `q = 0.81`, `a₁ = 0.34`, `a₂ = 0.67`.  It lies in the stated domain and outside
the calibrated region; the point with `a₂ = 0.5` is calibrated. -/
theorem ligo_calibration_injection_outside :
    statedDomain ⟨810, 340, 670⟩ ∧ ¬ calibratedRegion ⟨810, 340, 670⟩ ∧
    calibratedRegion ⟨810, 340, 500⟩ :=
  ⟨by decide, by decide, by decide⟩

/-- **The published upper bounds on the spins lie outside the calibrated region.**  Table I gives
the mass ratio `q = 0.84` with the 90% interval `[0.64, 0.98]`, below `1` throughout.  It gives
the 90% upper bounds on the primary spin `0.54`, `0.74`, `0.65` and on the secondary spin `0.70`,
`0.78`, `0.75` for precessing EOBNR, precessing IMRPhenom and "Overall".  For every mass ratio of
the interval, each of the six points is outside the calibrated region. -/
theorem ligo_calibration_credible_spin_bounds :
    ∀ q : Nat, 640 ≤ q → q ≤ 980 →
      (∀ u : Nat, (u = 540 ∨ u = 740 ∨ u = 650) → ¬ calibratedRegion ⟨q, u, 0⟩) ∧
      (∀ u : Nat, (u = 700 ∨ u = 780 ∨ u = 750) → ¬ calibratedRegion ⟨q, 0, u⟩) := by
  intro q h1 h2
  refine ⟨?_, ?_⟩
  · intro u hu
    exact not_calibrated_of_spin q u 0 (by omega) (Or.inl (by omega))
  · intro u hu
    exact not_calibrated_of_spin q 0 u (by omega) (Or.inr (by omega))

/-- **A tenth of each posterior lies beyond the calibrated spin.**  Let `F` be the cumulative
distribution of a spin magnitude, with the spin in thousandths and the probability in
hundredths, and let the 90% upper bound `b` exceed `0.5`.  The probability above `0.5` is at
least `10` hundredths, one tenth. -/
theorem ligo_calibration_posterior_mass_outside (F : Int → Int)
    (hF : ∀ x y : Int, x ≤ y → F x ≤ F y) (b : Int) (hb : 500 < b) (h90 : F b = 90) :
    10 ≤ 100 - F 500 := by
  have h1 : F 500 ≤ F b := hF 500 b (by omega)
  omega

end LigoSpecious

end
