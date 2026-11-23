module

public import RequestProject.Equality

/-!
# Measure Requires Isomorphic Structure-Preserving Sameness

Joseph Gerrety

Measurement is not created by numerical association.
Measurement requires preserved quantitative structure.
Exact reversible calibration requires isomorphic transposition of that structure.

Let `A` and `B` be two representations proposed as measurements of the same quantitative
property, e.g. mass expressed in tons and mass expressed in kilograms.  Each representation
carries the structure `Σ` (operations such as `+`, relations such as `≤`, `<`, and equality)
that gives the quantity its meaning.  We write `𝒜 = (A, Σ_A)` and `ℬ = (B, Σ_B)`.

Central requirement: two measured representations are quantitatively comparable only through
a structure-preserving correspondence.

The development follows the derivation section by section.

 §1  `SameKind`: the quantity-kind function `κ` and the first obstruction.
 §2  `HomomorphicAssociation`: preservation of operations, equality and relations.
 §3  `FullSubstitution`: preservation and reflection of equality and of every relation.
 §4  Full substitution forces injectivity (`fullSubstitution_injective`).
 §5  Complete calibrated coverage forces surjectivity onto the calibrated range.
 §6  Homomorphism + reversible substitution gives isomorphism
      (`exact_calibration_implies_isomorphic_transposition`).
 §7  Without homomorphic preservation there is no valid structural transposition.
 §8  Complete reversible calibration forces bijectivity.
 §9  200 tons versus 41 bright smiles: different kinds, no comparison.
 §10 200 tons versus 15 kg: comparable through the exact isomorphism `T(a) = 907.18474 a`,
      and unequal: `200 t = 181436.948 kg > 15 kg`.
 §11 The Calibration–Measure Isomorphic Necessity Theorem.
 §12 Contrapositive forms.

Everything is computable and written against core Lean 4 only.  There is no `choose`, no
`noncomputable` definition, no `native_decide`, and no declared `axiom`; the results of this
file use no `Classical.choice`, only (in some proofs) `propext` and `Quot.sound`
(function extensionality), which belong to Lean's kernel logic.
Because no choice principle is used, the reverse calibration over the calibrated range is
carried as explicit data (`ExactCalibration.recal`): the existence statement
`∀ b ∈ B_cal, ∃ a, T a = b` alone does not compute an inverse map, whereas a calibration
that claims to be reversible must supply its reverse reading.  Every structural property of
that reverse map (two-sided inverse, operation preservation, relation preservation and
reflection) is then derived, never assumed.

The axiom audit for this file is `RequestProject/MeasurementAxioms.lean`.
-/

@[expose] public section

namespace Measure

universe u

/-! ## The measurement signature and measurement structures -/

/-- A measurement signature `Σ`: for every arity `n`, the symbols of `n`-ary operations
and the symbols of `n`-ary relations that a measurement comparison uses. -/
structure Signature where
  /-- `n`-ary operation symbols (e.g. `+` in arity `2`) -/
  Op : Nat → Type
  /-- `n`-ary relation symbols (e.g. `≤`, `<` in arity `2`) -/
  Rel : Nat → Type

/-- A measured representation `𝒜 = (A, Σ_A)` of quantity kind `κ(A) ∈ K`:
a carrier of values, the quantity kind it represents, and an interpretation of every
operation and relation symbol of the signature `σ`. -/
structure MeasStructure (K : Type) (σ : Signature) where
  /-- the carrier `A` of measurement values -/
  carrier : Type u
  /-- the quantity kind `κ(A)` -/
  kind : K
  /-- interpretation of the `n`-ary operations -/
  op : {n : Nat} → σ.Op n → (Fin n → carrier) → carrier
  /-- interpretation of the `n`-ary relations -/
  rel : {n : Nat} → σ.Rel n → (Fin n → carrier) → Prop

variable {K : Type} {σ : Signature}

section Predicates

variable (A B : MeasStructure.{u} K σ)

/-! ## §1. Same quantitative kind -/

/-- `SameKind(A, B) ⟺ κ(A) = κ(B)`. -/
def SameKind : Prop := A.kind = B.kind

/-! ## §2. Homomorphic association -/

/-- `T(f(a₁, …, aₙ)) = f(T a₁, …, T aₙ)` for every operation symbol `f`
(for a binary operation: `T(a₁ ∘_A a₂) = T(a₁) ∘_B T(a₂)`). -/
def PreservesOperation (T : A.carrier → B.carrier) : Prop :=
  ∀ {n : Nat} (f : σ.Op n) (xs : Fin n → A.carrier),
    T (A.op f xs) = B.op f (fun i => T (xs i))

/-- `a₁ = a₂ ⟹ T(a₁) = T(a₂)`. -/
def PreservesEquality (T : A.carrier → B.carrier) : Prop :=
  ∀ a₁ a₂ : A.carrier, a₁ = a₂ → T a₁ = T a₂

/-- `R_A(a₁, …, aₙ) ⟹ R_B(T a₁, …, T aₙ)` for every relation symbol `R`. -/
def PreservesRelation (T : A.carrier → B.carrier) : Prop :=
  ∀ {n : Nat} (r : σ.Rel n) (xs : Fin n → A.carrier),
    A.rel r xs → B.rel r (fun i => T (xs i))

/-- Homomorphic association `HomAssoc(T)`: the association does not destroy the
structure by which the quantities are compared. -/
def HomomorphicAssociation (T : A.carrier → B.carrier) : Prop :=
  PreservesOperation A B T ∧ PreservesEquality A B T ∧ PreservesRelation A B T

/-! ## §3. Full substitution: reflection as well as preservation -/

/-- `T(a₁) = T(a₂) ⟹ a₁ = a₂`. -/
def ReflectsEquality (T : A.carrier → B.carrier) : Prop :=
  ∀ a₁ a₂ : A.carrier, T a₁ = T a₂ → a₁ = a₂

/-- `R_B(T a₁, …, T aₙ) ⟹ R_A(a₁, …, aₙ)` for every relation symbol `R`. -/
def ReflectsRelation (T : A.carrier → B.carrier) : Prop :=
  ∀ {n : Nat} (r : σ.Rel n) (xs : Fin n → A.carrier),
    B.rel r (fun i => T (xs i)) → A.rel r xs

/-- Full substitution `FullSubstitution(T)`:
`a₁ = a₂ ⟺ T(a₁) = T(a₂)` and `R_A(a₁, …, aₙ) ⟺ R_B(T a₁, …, T aₙ)` for every relation.
Every atomic statement in one calibrated representation transposes into the other
without changing its truth value. -/
def FullSubstitution (T : A.carrier → B.carrier) : Prop :=
  (∀ a₁ a₂ : A.carrier, a₁ = a₂ ↔ T a₁ = T a₂) ∧
  (∀ {n : Nat} (r : σ.Rel n) (xs : Fin n → A.carrier),
    A.rel r xs ↔ B.rel r (fun i => T (xs i)))

/-- Injectivity of a transposition. -/
def Injective (T : A.carrier → B.carrier) : Prop :=
  ∀ a₁ a₂ : A.carrier, T a₁ = T a₂ → a₁ = a₂

/-- Surjectivity onto the calibrated range `B_cal ⊆ B`. -/
def SurjectiveOnto (Bcal : B.carrier → Prop) (T : A.carrier → B.carrier) : Prop :=
  ∀ b : B.carrier, Bcal b → ∃ a : A.carrier, T a = b

/-- A valid measurement comparison through `T`: same quantity kind, and `T` is a
homomorphic association. -/
def ValidMeasurementComparison (T : A.carrier → B.carrier) : Prop :=
  SameKind A B ∧ HomomorphicAssociation A B T

/-- A calibrated range `B_cal` is closed under the operations of `ℬ`. -/
def ClosedRange (Bcal : B.carrier → Prop) : Prop :=
  ∀ {n : Nat} (f : σ.Op n) (bs : Fin n → B.carrier), (∀ i, Bcal (bs i)) → Bcal (B.op f bs)

end Predicates

/-- The calibrated sub-representation `ℬ_cal`: the values of `ℬ` lying in a closed
calibrated range, with the inherited kind, operations and relations. -/
def MeasStructure.restrict (B : MeasStructure.{u} K σ) (Bcal : B.carrier → Prop)
    (h : ClosedRange B Bcal) : MeasStructure.{u} K σ where
  carrier := {b : B.carrier // Bcal b}
  kind := B.kind
  op f xs := ⟨B.op f (fun i => (xs i).val), h f _ (fun i => (xs i).property)⟩
  rel r xs := B.rel r (fun i => (xs i).val)

/-! ## Isomorphism of measured representations -/

/-- An isomorphism of measured representations `𝒜 ≅ ℬ`: same quantity kind, a two-sided
inverse pair `T, T⁻¹`, both preserving every operation, and both preserving and reflecting
every relation. -/
structure MeasIso (A B : MeasStructure.{u} K σ) where
  /-- the quantity kinds agree -/
  kind_eq : A.kind = B.kind
  /-- the transposition `T` -/
  toFun : A.carrier → B.carrier
  /-- the reverse transposition `T⁻¹` -/
  invFun : B.carrier → A.carrier
  /-- `T⁻¹ (T a) = a` -/
  left_inv : ∀ a, invFun (toFun a) = a
  /-- `T (T⁻¹ b) = b` -/
  right_inv : ∀ b, toFun (invFun b) = b
  /-- `T` preserves every operation -/
  map_op : PreservesOperation A B toFun
  /-- `T` preserves and reflects every relation -/
  map_rel : ∀ {n : Nat} (r : σ.Rel n) (xs : Fin n → A.carrier),
    A.rel r xs ↔ B.rel r (fun i => toFun (xs i))
  /-- `T⁻¹` preserves every operation -/
  inv_map_op : PreservesOperation B A invFun
  /-- `T⁻¹` preserves and reflects every relation -/
  inv_map_rel : ∀ {n : Nat} (r : σ.Rel n) (ys : Fin n → B.carrier),
    B.rel r ys ↔ A.rel r (fun i => invFun (ys i))

/-- `𝒜 ≅ ℬ`: an isomorphism of measured representations exists. -/
def Isomorphic (A B : MeasStructure.{u} K σ) : Prop := Nonempty (MeasIso A B)

/-- `T` is an isomorphic transposition: it is the forward map of an isomorphism
`𝒜 ≅ ℬ`. -/
def IsomorphicTransposition (A B : MeasStructure.{u} K σ) (T : A.carrier → B.carrier) :
    Prop :=
  ∃ e : MeasIso A B, ∀ a, e.toFun a = T a

/-! ## Exact calibration -/

/-- An exact calibration of `𝒜` into `ℬ` over the calibrated range `B_cal` through `T`:

 the two representations have the same quantity kind;
 `T` is a homomorphic association;
 `T` admits full substitution;
 `T` takes values in the calibrated range;
 every admissible value `b ∈ B_cal` has a representative `recal b` in `A` with
  `T (recal b) = b` (complete calibrated coverage, read off constructively). -/
structure ExactCalibration (A B : MeasStructure.{u} K σ) (Bcal : B.carrier → Prop)
    (T : A.carrier → B.carrier) where
  /-- `SameKind(A, B)` -/
  sameKind : SameKind A B
  /-- `HomAssoc(T)` -/
  hom : HomomorphicAssociation A B T
  /-- `FullSubstitution(T)` -/
  fullSubst : FullSubstitution A B T
  /-- `T` lands in the calibrated range -/
  lands : ∀ a, Bcal (T a)
  /-- reverse reading of the calibration on the calibrated range -/
  recal : B.carrier → A.carrier
  /-- complete calibrated coverage: `T (recal b) = b` for every `b ∈ B_cal` -/
  recal_spec : ∀ b, Bcal b → T (recal b) = b

section Theory

variable {A B : MeasStructure.{u} K σ}

/-! ## §2 (continued). Preservation of equality is the logic of sameness -/

/-- Every map preserves equality: this is Leibniz sameness (`Sameness.eq_iff_same_values`),
applied to the function `T`. -/
theorem preservesEquality_of_sameness (T : A.carrier → B.carrier) :
    PreservesEquality A B T :=
  fun _ _ h => Sameness.eq_iff_same_values.mp h B.carrier T

/-- Full substitution contains homomorphic preservation of equality and of relations. -/
theorem FullSubstitution.preservesRelation {T : A.carrier → B.carrier}
    (h : FullSubstitution A B T) : PreservesRelation A B T :=
  fun r xs => (h.2 r xs).mp

/-- Full substitution contains reflection of relations. -/
theorem FullSubstitution.reflectsRelation {T : A.carrier → B.carrier}
    (h : FullSubstitution A B T) : ReflectsRelation A B T :=
  fun r xs => (h.2 r xs).mpr

/-! ## §4. Full substitution forces injectivity -/

/-- Full substitution of equality reflects equality. -/
theorem fullSubstitution_reflectsEquality {T : A.carrier → B.carrier}
    (h : FullSubstitution A B T) : ReflectsEquality A B T :=
  fun a₁ a₂ => (h.1 a₁ a₂).mpr

/-- Full substitution forces injectivity. Not an additional assumption: it follows from
full substitutability of equality. -/
theorem fullSubstitution_injective {T : A.carrier → B.carrier}
    (h : FullSubstitution A B T) : Injective A B T :=
  fullSubstitution_reflectsEquality h

namespace ExactCalibration

variable {Bcal : B.carrier → Prop} {T : A.carrier → B.carrier}

/-! ## §5. Complete calibrated coverage forces surjectivity -/

/-- Complete calibrated coverage ⟹ `T` surjective onto the calibrated range. -/
theorem surjectiveOnto (C : ExactCalibration A B Bcal T) : SurjectiveOnto A B Bcal T :=
  fun b hb => ⟨C.recal b, C.recal_spec b hb⟩

/-- The reverse reading is a left inverse of `T`.  This is derived from injectivity, i.e.
from full substitution of equality. -/
theorem recal_left (C : ExactCalibration A B Bcal T) (a : A.carrier) :
    C.recal (T a) = a :=
  fullSubstitution_injective C.fullSubst _ _ (C.recal_spec (T a) (C.lands a))

/-! ## §6. Homomorphism + reversible substitution gives isomorphism -/

/-- Rewriting a tuple of calibrated values through `T ∘ recal`. -/
theorem tuple_recal (C : ExactCalibration A B Bcal T) {n : Nat} (bs : Fin n → B.carrier)
    (hbs : ∀ i, Bcal (bs i)) : (fun i => T (C.recal (bs i))) = bs :=
  funext fun i => C.recal_spec (bs i) (hbs i)

/-- The calibrated range is automatically closed under the operations of `ℬ`. -/
theorem closedRange (C : ExactCalibration A B Bcal T) : ClosedRange B Bcal := by
  intro n f bs hbs
  have key : B.op f bs = T (A.op f (fun i => C.recal (bs i))) := by
    rw [C.hom.1 f, C.tuple_recal bs hbs]
  rw [key]
  exact C.lands _

/-- The reverse calibration preserves every operation on the calibrated range. -/
theorem recal_preservesOperation (C : ExactCalibration A B Bcal T) {n : Nat} (f : σ.Op n)
    (bs : Fin n → B.carrier) (hbs : ∀ i, Bcal (bs i)) :
    C.recal (B.op f bs) = A.op f (fun i => C.recal (bs i)) := by
  apply fullSubstitution_injective C.fullSubst
  rw [C.recal_spec _ (C.closedRange f bs hbs), C.hom.1 f, C.tuple_recal bs hbs]

/-- The reverse calibration preserves and reflects every relation on the calibrated
range. -/
theorem recal_rel_iff (C : ExactCalibration A B Bcal T) {n : Nat} (r : σ.Rel n)
    (bs : Fin n → B.carrier) (hbs : ∀ i, Bcal (bs i)) :
    B.rel r bs ↔ A.rel r (fun i => C.recal (bs i)) := by
  rw [C.fullSubst.2 r, C.tuple_recal bs hbs]

/-- The isomorphism `𝒜 ≅ ℬ_cal` produced by an exact calibration. -/
def toIso (C : ExactCalibration A B Bcal T) :
    MeasIso A (B.restrict Bcal C.closedRange) where
  kind_eq := C.sameKind
  toFun a := ⟨T a, C.lands a⟩
  invFun b := C.recal b.val
  left_inv := C.recal_left
  right_inv b := Subtype.ext (C.recal_spec b.val b.property)
  map_op f xs := Subtype.ext (C.hom.1 f xs)
  map_rel r xs := C.fullSubst.2 r xs
  inv_map_op f ys := C.recal_preservesOperation f _ (fun i => (ys i).property)
  inv_map_rel r ys := C.recal_rel_iff r _ (fun i => (ys i).property)

/-- On the full range `B_cal = B`, an exact calibration is an isomorphism `𝒜 ≅ ℬ`. -/
def toIsoFull (C : ExactCalibration A B (fun _ => True) T) : MeasIso A B where
  kind_eq := C.sameKind
  toFun := T
  invFun := C.recal
  left_inv := C.recal_left
  right_inv b := C.recal_spec b trivial
  map_op := C.hom.1
  map_rel := C.fullSubst.2
  inv_map_op f ys := C.recal_preservesOperation f ys (fun _ => trivial)
  inv_map_rel r ys := C.recal_rel_iff r ys (fun _ => trivial)

end ExactCalibration

/-! ## §11. The Calibration–Measure Isomorphic Necessity Theorem -/

/-- Calibration–Measure Isomorphic Necessity Theorem.

An exact calibration `T : A → B` over the calibrated range `B_cal` yields
`SameKind(A, B) ∧ HomAssoc(T) ∧ FullSubstitution(T) ∧ Bijective(T : A → B_cal)`,
the reverse calibration is again a homomorphism that preserves and reflects every relation,
and `T` is an isomorphic transposition `𝒜 ≅ ℬ_cal`. -/
theorem exact_calibration_implies_isomorphic_transposition {Bcal : B.carrier → Prop}
    {T : A.carrier → B.carrier} (C : ExactCalibration A B Bcal T) :
    SameKind A B ∧
    HomomorphicAssociation A B T ∧
    FullSubstitution A B T ∧
    Injective A B T ∧
    SurjectiveOnto A B Bcal T ∧
    (∀ {n : Nat} (f : σ.Op n) (bs : Fin n → B.carrier), (∀ i, Bcal (bs i)) →
      C.recal (B.op f bs) = A.op f (fun i => C.recal (bs i))) ∧
    (∀ {n : Nat} (r : σ.Rel n) (bs : Fin n → B.carrier), (∀ i, Bcal (bs i)) →
      (B.rel r bs ↔ A.rel r (fun i => C.recal (bs i)))) ∧
    IsomorphicTransposition A (B.restrict Bcal C.closedRange) (fun a => ⟨T a, C.lands a⟩) :=
  ⟨C.sameKind, C.hom, C.fullSubst, fullSubstitution_injective C.fullSubst, C.surjectiveOnto,
    fun f bs hbs => C.recal_preservesOperation f bs hbs,
    fun r bs hbs => C.recal_rel_iff r bs hbs,
    ⟨C.toIso, fun _ => rfl⟩⟩

/-- Exact calibration ⟹ `𝒜 ≅ ℬ_cal`. -/
theorem exact_calibration_isomorphic {Bcal : B.carrier → Prop} {T : A.carrier → B.carrier}
    (C : ExactCalibration A B Bcal T) : Isomorphic A (B.restrict Bcal C.closedRange) :=
  ⟨C.toIso⟩

/-- Exact calibration over the whole of `B` ⟹ `𝒜 ≅ ℬ`, with `T` itself as the
isomorphic transposition. -/
theorem exact_full_calibration_isomorphic_transposition {T : A.carrier → B.carrier}
    (C : ExactCalibration A B (fun _ => True) T) : IsomorphicTransposition A B T :=
  ⟨C.toIsoFull, fun _ => rfl⟩

/-- Conversely, every isomorphism of measured representations is an exact calibration over
the whole of `B`: exact calibration and isomorphic transposition coincide. -/
def MeasIso.toExactCalibration (e : MeasIso A B) :
    ExactCalibration A B (fun _ => True) e.toFun where
  sameKind := e.kind_eq
  hom := ⟨e.map_op, preservesEquality_of_sameness _, fun r xs => (e.map_rel r xs).mp⟩
  fullSubst :=
    ⟨fun a₁ a₂ => ⟨fun h => h ▸ rfl, fun h => by rw [← e.left_inv a₁, h, e.left_inv]⟩,
      e.map_rel⟩
  lands _ := trivial
  recal := e.invFun
  recal_spec b _ := e.right_inv b

/-- Exact full calibration through some `T` ⟺ `𝒜 ≅ ℬ`. -/
theorem exists_exact_calibration_iff_isomorphic :
    (∃ T : A.carrier → B.carrier, Nonempty (ExactCalibration A B (fun _ => True) T)) ↔
      Isomorphic A B :=
  ⟨fun ⟨_, ⟨C⟩⟩ => ⟨C.toIsoFull⟩, fun ⟨e⟩ => ⟨e.toFun, ⟨e.toExactCalibration⟩⟩⟩

/-! ## §7. Why homomorphism is required -/

/-- A failing commutative square destroys operation preservation: if for some operation
`f` and inputs `xs` we have `T(f_A(xs)) ≠ f_B(T ∘ xs)`, i.e. `T ∘ f_A ≠ f_B ∘ (T × ⋯ × T)`,
then `T` does not preserve the operation. -/
theorem not_preservesOperation_of_noncommuting {T : A.carrier → B.carrier} {n : Nat}
    (f : σ.Op n) (xs : Fin n → A.carrier)
    (hne : T (A.op f xs) ≠ B.op f (fun i => T (xs i))) : ¬ PreservesOperation A B T :=
  fun h => hne (h f xs)

/-- No homomorphic preservation ⟹ no homomorphic association, no valid comparison and no
exact calibration through `T`. -/
theorem not_hom_implies_not_valid {T : A.carrier → B.carrier}
    (h : ¬ PreservesOperation A B T) :
    ¬ HomomorphicAssociation A B T ∧ ¬ ValidMeasurementComparison A B T ∧
      ∀ Bcal : B.carrier → Prop, ¬ Nonempty (ExactCalibration A B Bcal T) :=
  ⟨fun hh => h hh.1, fun hv => h hv.2.1, fun _ ⟨C⟩ => h C.hom.1⟩

/-- A relation not preserved by `T` likewise rules out homomorphic association. -/
theorem not_preservesRelation_implies_not_valid {T : A.carrier → B.carrier}
    (h : ¬ PreservesRelation A B T) :
    ¬ HomomorphicAssociation A B T ∧ ¬ ValidMeasurementComparison A B T ∧
      ¬ FullSubstitution A B T :=
  ⟨fun hh => h hh.2.2, fun hv => h hv.2.2.2, fun hf => h hf.preservesRelation⟩

/-! ## §8. Why isomorphism is required for complete reversible calibration -/

/-- `¬ Injective(T) ⟹ ¬ FullSubstitution(T)`: distinct quantities made indistinguishable
by `T` cannot be substituted reversibly. -/
theorem not_injective_implies_not_fullSubstitution {T : A.carrier → B.carrier}
    (h : ∃ a₁ a₂, a₁ ≠ a₂ ∧ T a₁ = T a₂) : ¬ FullSubstitution A B T :=
  fun hf => let ⟨a₁, a₂, hne, heq⟩ := h; hne (fullSubstitution_injective hf a₁ a₂ heq)

/-- Not surjective onto the calibrated range ⟹ no exact calibration: a claimed
measurement value with no representation in `A` admits no reversible substitution. -/
theorem not_surjective_implies_not_calibration {Bcal : B.carrier → Prop}
    {T : A.carrier → B.carrier} (h : ∃ b, Bcal b ∧ ∀ a, T a ≠ b) :
    ¬ Nonempty (ExactCalibration A B Bcal T) :=
  fun ⟨C⟩ => let ⟨b, hb, hno⟩ := h; hno (C.recal b) (C.recal_spec b hb)

/-- `FullReversibleCalibration(T) ⟹ Bijective(T)` onto the calibrated range. -/
theorem calibration_bijective {Bcal : B.carrier → Prop} {T : A.carrier → B.carrier}
    (C : ExactCalibration A B Bcal T) : Injective A B T ∧ SurjectiveOnto A B Bcal T :=
  ⟨fullSubstitution_injective C.fullSubst, C.surjectiveOnto⟩

/-! ## §12. Contrapositive forms -/

/-- `¬ Isomorphic(𝒜, ℬ_cal) ⟹ ¬ FullReversibleCalibration`. -/
theorem not_isomorphic_implies_not_full_calibration {Bcal : B.carrier → Prop}
    (h : ∀ hc : ClosedRange B Bcal, ¬ Isomorphic A (B.restrict Bcal hc))
    (T : A.carrier → B.carrier) : ¬ Nonempty (ExactCalibration A B Bcal T) :=
  fun ⟨C⟩ => h C.closedRange ⟨C.toIso⟩

/-- `¬ Isomorphic(𝒜, ℬ) ⟹` no exact calibration over the whole of `B`. -/
theorem not_isomorphic_implies_not_exact_calibration (h : ¬ Isomorphic A B)
    (T : A.carrier → B.carrier) : ¬ Nonempty (ExactCalibration A B (fun _ => True) T) :=
  fun ⟨C⟩ => h ⟨C.toIsoFull⟩

/-! ## §1 and §9. Different quantity kinds: the first obstruction -/

/-- Different quantity kinds ⟹ not comparable.  If `κ(A) ≠ κ(B)` then no map is a valid
measurement comparison, no exact calibration exists over any range, and `𝒜 ≇ ℬ`. -/
theorem different_quantity_kind_implies_not_comparable (h : A.kind ≠ B.kind) :
    ¬ SameKind A B ∧
    (∀ T : A.carrier → B.carrier, ¬ ValidMeasurementComparison A B T) ∧
    (∀ (Bcal : B.carrier → Prop) (T : A.carrier → B.carrier),
      ¬ Nonempty (ExactCalibration A B Bcal T)) ∧
    ¬ Isomorphic A B :=
  ⟨h, fun _ hv => h hv.1, fun _ _ ⟨C⟩ => h C.sameKind, fun ⟨e⟩ => h e.kind_eq⟩

end Theory

end Measure

end
