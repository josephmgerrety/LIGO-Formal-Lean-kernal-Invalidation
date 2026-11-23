import PerfectAssociation.LigoCongruence
import PerfectAssociation.EqualityBridge
import PerfectAssociation.Algebra

/-!
# LIGO calibration: faithfulness, substitution, transitivity, homomorphism

Core Lean 4 only. Every definition is computable.

Part 1. A calibration `C : P → R` from structure values `P` to calibrated values `R` is
faithful when equal calibrated values come from equal structure values. Faithfulness is
equivalent to substitution, to transitivity through `C`, and to validity for every target.
Part 2. Isomorphisms are faithful; faithfulness is exactly the condition under which
isomorphism of all information carriers detects equality of structure values.
Part 3. Affine calibrations `z ↦ a z + b`: faithful iff the gain `a` is nonzero,
additive homomorphism iff the offset `b` is zero; the two conditions are independent.
Part 4. Agreement within a margin is not transitive and is the kernel of no map.
Scale: 1 mm = 10^15 am, so 1/500000000000000 mm = 2 am.
-/
namespace LigoCalibration

universe u v w

/-! ## Part 1: faithful calibration -/

/-- Equal calibrated values come from equal structure values. -/
def Faithful {P : Sort u} {R : Sort v} (C : P → R) : Prop :=
  ∀ a b, C a = C b → a = b

/-- Substitution through `C`: every property of `a` is a property of `b` when `C a = C b`. -/
def Substitutes {P : Sort u} {R : Sort v} (C : P → R) : Prop :=
  ∀ (Q : P → Prop) (a b : P), C a = C b → Q a → Q b

/-- Transitivity through `C`: calibrated equalities chain into an equality of structure values. -/
def Chains {P : Sort u} {R : Sort v} (C : P → R) : Prop :=
  ∀ a b c : P, C a = C b → C b = C c → a = c

theorem faithful_substitutes {P : Sort u} {R : Sort v} {C : P → R} (h : Faithful C) :
    Substitutes C :=
  fun _ a b hC qa => (h a b hC) ▸ qa

theorem substitutes_faithful {P : Sort u} {R : Sort v} {C : P → R} (h : Substitutes C) :
    Faithful C :=
  fun a b hC => h (fun x => a = x) a b hC rfl

theorem faithful_chains {P : Sort u} {R : Sort v} {C : P → R} (h : Faithful C) :
    Chains C :=
  fun a b c h₁ h₂ => (h a b h₁).trans (h b c h₂)

theorem chains_faithful {P : Sort u} {R : Sort v} {C : P → R} (h : Chains C) :
    Faithful C :=
  fun a b hC => h a b b hC rfl

/-- A faithful calibration is valid for every target. -/
theorem faithful_valid_for_all {P : Sort u} {R : Sort v} {γ : Sort w} {C : P → R}
    (h : Faithful C) (T : P → γ) : LigoCongruence.IsValidFor C T :=
  fun a b hab => congrArg T (h a b hab)

/-- Validity for the identity target is faithfulness. -/
theorem faithful_iff_valid_id {P : Sort u} {R : Sort v} (C : P → R) :
    Faithful C ↔ LigoCongruence.IsValidFor C (fun a : P => a) :=
  Iff.rfl

/-- Substitution, transitivity and validity for every target are one condition. -/
theorem faithful_characterisation {P : Sort u} {R : Sort v} (C : P → R) :
    (Faithful C ↔ Substitutes C) ∧ (Faithful C ↔ Chains C) ∧
    (Faithful C ↔ ∀ T : P → P, LigoCongruence.IsValidFor C T) :=
  ⟨⟨faithful_substitutes, substitutes_faithful⟩,
   ⟨faithful_chains, chains_faithful⟩,
   ⟨faithful_valid_for_all, fun h a b hab => h (fun x => x) a b hab⟩⟩

/-- With decidable equality, faithfulness is preservation of inequality. -/
theorem faithful_iff_preserves_ne {P : Sort u} {R : Sort v} [DecidableEq P] (C : P → R) :
    Faithful C ↔ ∀ a b, a ≠ b → C a ≠ C b :=
  ⟨fun h a b hne hC => hne (h a b hC),
   fun h a b hC => Decidable.byContradiction fun hne => h a b hne hC⟩

/-- A pair that `C` merges and the structure separates: the explicit failure of substitution. -/
theorem substitution_fails {P : Sort u} {R : Sort v} {C : P → R} {a b : P}
    (hC : C a = C b) (hne : a ≠ b) : ¬ Substitutes C :=
  fun h => hne (substitutes_faithful h a b hC)

/-- The property that separates the merged pair: "equals `a`". -/
theorem separating_property {P : Sort u} {a b : P} (hne : a ≠ b) :
    ∃ Q : P → Prop, Q a ∧ ¬ Q b :=
  ⟨fun x => a = x, rfl, hne⟩

/-- ... and of transitivity: the chain `a, b, b` concludes `a = b`. -/
theorem chain_fails {P : Sort u} {R : Sort v} {C : P → R} {a b : P}
    (hC : C a = C b) (hne : a ≠ b) : ¬ Chains C :=
  fun h => hne (h a b b hC rfl)

/-- The merged pair is an invalid pair of `C` for the identity target. -/
theorem merged_pair_invalid {P : Sort u} {R : Sort v} {C : P → R} {a b : P}
    (hC : C a = C b) (hne : a ≠ b) : LigoCongruence.IsInvalidFor C (fun t : P => t) :=
  ⟨a, b, hC, hne⟩

/-- A chain of calibrations keeps every merger of its first link. -/
theorem chain_unfaithful {P : Sort u} {R : Sort v} {S : Sort w} (C₁ : P → R) (C₂ : R → S)
    (h : ¬ Faithful C₁) : ¬ Faithful (fun a => C₂ (C₁ a)) :=
  fun hf => h (fun a b hab => hf a b (congrArg C₂ hab))

theorem faithful_comp {P : Sort u} {R : Sort v} {S : Sort w} {C₁ : P → R} {C₂ : R → S}
    (h₁ : Faithful C₁) (h₂ : Faithful C₂) : Faithful (fun a => C₂ (C₁ a)) :=
  fun a b hab => h₁ a b (h₂ (C₁ a) (C₁ b) hab)

/-! ## Part 2: isomorphism and information carriers -/

theorem iso_faithful {P : Sort u} {R : Sort v} (e : EqualityBridge.Iso P R) :
    Faithful e.toFun :=
  fun _ _ h => e.injective h

theorem iso_preserves_ne {P : Sort u} {R : Sort v} (e : EqualityBridge.Iso P R) {a b : P}
    (hne : a ≠ b) : e.toFun a ≠ e.toFun b :=
  fun h => hne (e.injective h)

theorem iso_reflects_ne {P : Sort u} {R : Sort v} (e : EqualityBridge.Iso P R) {a b : P}
    (hne : e.toFun a ≠ e.toFun b) : a ≠ b :=
  fun h => hne (congrArg e.toFun h)

/-- Composition of isomorphisms. -/
def isoTrans {A : Sort u} {B : Sort v} {C : Sort w} (e₁ : EqualityBridge.Iso A B)
    (e₂ : EqualityBridge.Iso B C) : EqualityBridge.Iso A C where
  toFun x := e₂.toFun (e₁.toFun x)
  invFun z := e₁.invFun (e₂.invFun z)
  left_inv x := (congrArg e₁.invFun (e₂.left_inv (e₁.toFun x))).trans (e₁.left_inv x)
  right_inv z := (congrArg e₂.toFun (e₁.right_inv (e₂.invFun z))).trans (e₂.right_inv z)

/-- A calibration is faithful exactly when isomorphism of all information carriers over the
calibrated values detects equality of the structure values. -/
theorem faithful_iff_carriers_detect_equality {P : Sort u} {R : Sort v} (C : P → R) :
    Faithful C ↔ ∀ a b : P,
      (∀ F : R → Type w, Nonempty (EqualityBridge.Iso (F (C a)) (F (C b)))) → a = b :=
  ⟨fun h a b hF => h a b (EqualityBridge.eq_iff_forall_iso.mpr hF),
   fun h a b hC => h a b (fun F => ⟨EqualityBridge.transport F hC⟩)⟩

/-- For a merged pair the calibrated carriers are isomorphic while the structure carriers are not. -/
theorem carriers_gap {P : Sort u} {R : Sort v} (C : P → R) {a b : P}
    (hC : C a = C b) (hne : a ≠ b) :
    (∀ F : R → Type w, Nonempty (EqualityBridge.Iso (F (C a)) (F (C b)))) ∧
    ¬ (∀ F : P → Type w, Nonempty (EqualityBridge.Iso (F a) (F b))) :=
  ⟨fun F => ⟨EqualityBridge.transport F hC⟩,
   fun H => hne (EqualityBridge.eq_iff_forall_iso.mpr H)⟩

/-- The 1.5PN coefficient merges `(0, 4)` and `(1, 0)`: it is not faithful. -/
theorem psi15_not_faithful (c : Int) :
    ¬ Faithful (fun s : Int × Int => LigoCongruence.psi15 c s.1 s.2) :=
  fun h => absurd (congrArg Prod.fst (h (0, 4) (1, 0) (LigoCongruence.psi15_fibre c 0 1)))
    (by decide)

/-- The waveform carriers over the two spin states are isomorphic, and the states differ. -/
theorem waveform_carriers_iso_states_differ (c : Int) :
    ∃ s t : Int × Int,
      (∀ F : Int → Type w, Nonempty (EqualityBridge.Iso
        (F (LigoCongruence.psi15 c s.1 s.2)) (F (LigoCongruence.psi15 c t.1 t.2)))) ∧ s ≠ t :=
  ⟨(0, 4), (1, 0), fun F => ⟨EqualityBridge.transport F (LigoCongruence.psi15_fibre c 0 1)⟩,
   by decide⟩

/-! ## Part 3: affine calibrations -/

open AssociationAlgebra in
/-- Unit gain: faithful for every offset. -/
theorem affine_unit_gain_faithful (b : Int) : Faithful (Affine 1 b) :=
  fun x y h =>
    (Int.one_mul x).symm.trans (((Int.add_left_inj b).mp h).trans (Int.one_mul y))

open AssociationAlgebra in
/-- Zero gain: constant, hence not faithful. -/
theorem affine_zero_gain_not_faithful (b : Int) : ¬ Faithful (Affine 0 b) :=
  fun h => absurd
    (h 0 1 ((congrArg (· + b) (Int.zero_mul 0)).trans (congrArg (· + b) (Int.zero_mul 1)).symm))
    (by decide)

open AssociationAlgebra in
theorem affine_faithful_iff (a b : Int) : Faithful (Affine a b) ↔ a ≠ 0 :=
  ⟨fun h ha => by subst ha; exact affine_zero_gain_not_faithful b h,
   fun ha x y h => Int.eq_of_mul_eq_mul_left ha ((Int.add_left_inj b).mp h)⟩

open AssociationAlgebra in
/-- The four calibrations `(gain, offset) ∈ {0, 1}²`: faithfulness and homomorphism are independent. -/
theorem faithful_hom_independent :
    (Faithful (Affine 1 0) ∧ AdditiveHom (Affine 1 0)) ∧
    (Faithful (Affine 1 1) ∧ ¬ AdditiveHom (Affine 1 1)) ∧
    (¬ Faithful (Affine 0 0) ∧ AdditiveHom (Affine 0 0)) ∧
    (¬ Faithful (Affine 0 1) ∧ ¬ AdditiveHom (Affine 0 1)) :=
  ⟨⟨affine_unit_gain_faithful 0, (affine_hom_iff 1 0).mpr rfl⟩,
   ⟨affine_unit_gain_faithful 1, affine_nonzero_offset_not_hom 1 1 (by decide)⟩,
   ⟨affine_zero_gain_not_faithful 0, (affine_hom_iff 0 0).mpr rfl⟩,
   ⟨affine_zero_gain_not_faithful 1, affine_nonzero_offset_not_hom 0 1 (by decide)⟩⟩

open AssociationAlgebra in
/-- An offset leaves every difference of calibrated values equal to the difference of the
structure values. -/
theorem offset_preserves_differences (b x y : Int) :
    Affine 1 b x - Affine 1 b y = x - y := by
  unfold Affine
  rw [Int.add_sub_add_right, Int.one_mul, Int.one_mul]

open AssociationAlgebra in
/-- The translation by an offset `c` is an isomorphism of the carrier. -/
def translationIso (c : Int) : EqualityBridge.Iso Int Int where
  toFun := Affine 1 c
  invFun := Affine 1 (-c)
  left_inv z := by
    unfold Affine
    rw [Int.one_mul, Int.one_mul, Int.add_neg_cancel_right]
  right_inv z := by
    unfold Affine
    rw [Int.one_mul, Int.one_mul, Int.neg_add_cancel_right]

open AssociationAlgebra in
/-- A nonzero offset is an isomorphism of the equality structure and not a homomorphism of
the addition. -/
theorem offset_iso_not_hom (c : Int) (hc : c ≠ 0) :
    (∃ e : EqualityBridge.Iso Int Int, e.toFun = Affine 1 c) ∧ ¬ AdditiveHom (Affine 1 c) :=
  ⟨⟨translationIso c, rfl⟩, affine_nonzero_offset_not_hom 1 c hc⟩

open AssociationAlgebra in
/-- Composition law: offsets of a chain of calibrations combine as `a₂ b₁ + b₂`. -/
theorem affine_comp (a₁ b₁ a₂ b₂ z : Int) :
    Affine a₂ b₂ (Affine a₁ b₁ z) = Affine (a₂ * a₁) (a₂ * b₁ + b₂) z := by
  unfold Affine
  rw [Int.mul_add, Int.add_assoc, Int.mul_assoc]

open AssociationAlgebra in
theorem hom_comp {f g : Int → Int} (hf : AdditiveHom f) (hg : AdditiveHom g) :
    AdditiveHom (fun z => g (f z)) :=
  fun u v => (congrArg g (hf u v)).trans (hg (f u) (f v))

open AssociationAlgebra in
/-- A nonzero offset breaks additivity at every pair of inputs, by the same amount `-b`. -/
theorem affine_defect_everywhere (a b u v : Int) (hb : b ≠ 0) :
    Affine a b (u + v) ≠ Affine a b u + Affine a b v := by
  intro h
  have hd := affine_defect a b u v
  unfold AdditiveDefect at hd
  rw [h, Int.add_comm (Affine a b u) (Affine a b v), Int.add_sub_cancel, Int.sub_self] at hd
  exact hb (Int.neg_eq_zero.mp hd.symm)

open AssociationAlgebra in
/-- Two perturbations of 2 am through a calibration with offset 1 am: the calibrated reading of
their sum is 5, the sum of their calibrated readings is 6, and the defect is -1 am. -/
theorem offset_scale_checkpoint :
    Affine 1 1 2 = 3 ∧ Affine 1 1 (2 + 2) = 5 ∧ Affine 1 1 2 + Affine 1 1 2 = 6 ∧
    AdditiveDefect (Affine 1 1) 2 2 = -1 := by
  decide

/-! ## Part 4: margins and scale -/

/-- Agreement within the margin `ε`, for amplitudes in `Nat`. -/
def Within (ε a b : Nat) : Prop := a ≤ b + ε ∧ b ≤ a + ε

instance (ε a b : Nat) : Decidable (Within ε a b) :=
  inferInstanceAs (Decidable (a ≤ b + ε ∧ b ≤ a + ε))

theorem within_refl (ε a : Nat) : Within ε a a :=
  ⟨Nat.le_add_right a ε, Nat.le_add_right a ε⟩

theorem within_symm {ε a b : Nat} (h : Within ε a b) : Within ε b a :=
  ⟨h.2, h.1⟩

/-- Every positive margin destroys transitivity: `0 ≈ ε ≈ 2ε` and `0 ≉ 2ε`. -/
theorem within_not_transitive (ε : Nat) (hε : 0 < ε) :
    ¬ ∀ a b c : Nat, Within ε a b → Within ε b c → Within ε a c := by
  intro h
  have h1 : Within ε 0 ε :=
    ⟨Nat.zero_le _, Nat.le_of_eq (Nat.zero_add ε).symm⟩
  have h2 : Within ε ε (ε + ε) :=
    ⟨Nat.le_trans (Nat.le_add_right ε ε) (Nat.le_add_right (ε + ε) ε), Nat.le_refl _⟩
  have h3 := (h 0 ε (ε + ε) h1 h2).2
  rw [Nat.zero_add] at h3
  exact Nat.not_le.mpr (Nat.lt_add_of_pos_right hε) h3

/-- No map from amplitudes to any type has `Within ε` as its kernel. -/
theorem within_not_a_kernel (ε : Nat) (hε : 0 < ε) {X : Sort u} :
    ¬ ∃ f : Nat → X, ∀ a b, f a = f b ↔ Within ε a b :=
  fun ⟨_, hf⟩ => within_not_transitive ε hε fun a b c hab hbc =>
    (hf a c).mp (((hf a b).mpr hab).trans ((hf b c).mpr hbc))

/-- Attometres per millimetre: 1 mm = 10⁻³ m and 1 am = 10⁻¹⁸ m. -/
def amPerMm : Nat := 1000000000000000

/-- The perturbation 1/500000000000000 mm, in attometres. -/
def perturbationAm : Nat := 2

theorem perturbation_exact : amPerMm = 500000000000000 * perturbationAm := by
  decide

/-- With a margin of 1 am, half of the perturbation: `0 ≈ 1 ≈ 2` and `0 ≉ 2`. -/
theorem margin_chain_at_scale :
    Within 1 0 1 ∧ Within 1 1 perturbationAm ∧ ¬ Within 1 0 perturbationAm := by
  decide

/-! ## Part 5: anchors for an affine calibration -/

open AssociationAlgebra in
/-- One reading at a known input `z₀` leaves the gain undetermined. -/
theorem one_anchor_invalid_for_gain (z₀ : Int) :
    LigoCongruence.IsInvalidFor (fun p : Int × Int => Affine p.1 p.2 z₀) (fun p => p.1) :=
  ⟨(0, z₀), (1, 0), by
    show Affine 0 z₀ z₀ = Affine 1 0 z₀
    unfold Affine
    rw [Int.zero_mul, Int.zero_add, Int.one_mul, Int.add_zero], (by decide : ¬ ((0 : Int) = 1))⟩

open AssociationAlgebra in
/-- One reading at a known nonzero input leaves the offset undetermined. -/
theorem one_anchor_invalid_for_offset (z₀ : Int) (hz : z₀ ≠ 0) :
    LigoCongruence.IsInvalidFor (fun p : Int × Int => Affine p.1 p.2 z₀) (fun p => p.2) :=
  ⟨(0, z₀), (1, 0), by
    show Affine 0 z₀ z₀ = Affine 1 0 z₀
    unfold Affine
    rw [Int.zero_mul, Int.zero_add, Int.one_mul, Int.add_zero], hz⟩

open AssociationAlgebra in
/-- A reading at the known input `0` identifies the offset. -/
theorem zero_anchor_identifies_offset :
    LigoCongruence.IsValidFor (fun p : Int × Int => Affine p.1 p.2 0) (fun p => p.2) :=
  fun p q h => by
    have h0 : Affine p.1 p.2 0 = Affine q.1 q.2 0 := h
    unfold Affine at h0
    rw [Int.mul_zero, Int.mul_zero, Int.zero_add, Int.zero_add] at h0
    exact h0

open AssociationAlgebra in
/-- Readings at the known inputs `0` and `1` identify the gain and the offset. -/
theorem zero_unit_anchors_valid :
    LigoCongruence.IsValidFor
      (fun p : Int × Int => (Affine p.1 p.2 0, Affine p.1 p.2 1)) (fun p => p) :=
  fun ⟨a, b⟩ ⟨a', b'⟩ h => by
    have h0 : Affine a b 0 = Affine a' b' 0 := congrArg Prod.fst h
    have h1 : Affine a b 1 = Affine a' b' 1 := congrArg Prod.snd h
    unfold Affine at h0 h1
    rw [Int.mul_zero, Int.mul_zero, Int.zero_add, Int.zero_add] at h0
    rw [Int.mul_one, Int.mul_one, h0] at h1
    exact LigoCongruence.prod_mk_congr ((Int.add_left_inj b').mp h1) h0

#print axioms faithful_substitutes
#print axioms substitutes_faithful
#print axioms faithful_chains
#print axioms chains_faithful
#print axioms faithful_valid_for_all
#print axioms faithful_iff_valid_id
#print axioms faithful_characterisation
#print axioms faithful_iff_preserves_ne
#print axioms substitution_fails
#print axioms separating_property
#print axioms chain_fails
#print axioms merged_pair_invalid
#print axioms chain_unfaithful
#print axioms faithful_comp
#print axioms iso_faithful
#print axioms iso_preserves_ne
#print axioms iso_reflects_ne
#print axioms isoTrans
#print axioms faithful_iff_carriers_detect_equality
#print axioms carriers_gap
#print axioms psi15_not_faithful
#print axioms waveform_carriers_iso_states_differ
#print axioms affine_unit_gain_faithful
#print axioms affine_zero_gain_not_faithful
#print axioms affine_faithful_iff
#print axioms faithful_hom_independent
#print axioms offset_preserves_differences
#print axioms translationIso
#print axioms offset_iso_not_hom
#print axioms affine_comp
#print axioms hom_comp
#print axioms affine_defect_everywhere
#print axioms offset_scale_checkpoint
#print axioms within_refl
#print axioms within_symm
#print axioms within_not_transitive
#print axioms within_not_a_kernel
#print axioms perturbation_exact
#print axioms margin_chain_at_scale
#print axioms one_anchor_invalid_for_gain
#print axioms one_anchor_invalid_for_offset
#print axioms zero_anchor_identifies_offset
#print axioms zero_unit_anchors_valid

end LigoCalibration
