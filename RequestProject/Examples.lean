module

public import RequestProject.Measurement

/-!
# §9 and §10: tons, kilograms and bright smiles

* §9  `200 t` versus `41` bright smiles: `κ = Mass` versus `κ = SmileCount`.  No valid
  comparison, no exact calibration, no isomorphism.  The numerals `200` and `41` do not
  create comparability.
* §10 `200 t` versus `15 kg`: same kind.  With short tons, `T(a) = 907.18474 a`,
  `T⁻¹(b) = b / 907.18474`; `T` is an exact calibration and an isomorphism
  `ℚ_ton ≅ ℚ_kg` preserving `+`, `=`, `≤`, `<`.  The two values are comparable but unequal:
  `T(200) = 181436.948 kg`, hence `200 t > 15 kg`, and `200 t = 181436.948 kg` exactly.

* §5/§8 in integers: whole tons into `10 mg` units, `T(n) = 90718474 n`, an exact calibration
  onto the proper calibrated range `90718474 ℤ` but not onto the whole scale.

All arithmetic is exact arithmetic in core Lean (`Rat`, `Int`), discharged by kernel
evaluation (`decide`, `decide +kernel`), never by `native_decide`.  Every definition is
computable.  The rational results inherit `Classical.choice` solely from the proofs of core
Lean's `Rat` lemmas (e.g. `Rat.mul_comm`); the integer model uses no `Classical.choice`.
-/

@[expose] public section

namespace Measure

/-! ## Quantity kinds and the arithmetic–order signature -/

/-- Quantity kinds `K`. -/
inductive QuantityKind where
  | mass
  | length
  | time
  | temperature
  | smileCount
  deriving DecidableEq

/-- Operation symbols: binary addition. -/
inductive ArithOp : Nat → Type where
  | add : ArithOp 2

/-- Relation symbols: binary `≤` and `<`. -/
inductive OrderRel : Nat → Type where
  | le : OrderRel 2
  | lt : OrderRel 2

/-- The signature `Σ = {+, ≤, <}` (equality is part of the logic). -/
def arithOrder : Signature := ⟨ArithOp, OrderRel⟩

/-! ## Carriers -/

/-- Mass expressed in (short) tons. -/
structure Tons where
  /-- the numerical value in tons -/
  val : Rat

/-- Mass expressed in kilograms. -/
structure Kilograms where
  /-- the numerical value in kilograms -/
  val : Rat

/-- A count of bright smiles. -/
structure Smiles where
  /-- the number of smiles -/
  count : Nat

/-- Interpretation of the operation symbols on rationals. -/
def ratOp : {n : Nat} → ArithOp n → (Fin n → Rat) → Rat
  | _, .add, xs => xs 0 + xs 1

/-- Interpretation of the relation symbols on rationals. -/
def ratRel : {n : Nat} → OrderRel n → (Fin n → Rat) → Prop
  | _, .le, xs => xs 0 ≤ xs 1
  | _, .lt, xs => xs 0 < xs 1

/-- Interpretation of the operation symbols on natural numbers. -/
def natOp : {n : Nat} → ArithOp n → (Fin n → Nat) → Nat
  | _, .add, xs => xs 0 + xs 1

/-- Interpretation of the relation symbols on natural numbers. -/
def natRel : {n : Nat} → OrderRel n → (Fin n → Nat) → Prop
  | _, .le, xs => xs 0 ≤ xs 1
  | _, .lt, xs => xs 0 < xs 1

/-! ## The three measured representations -/

/-- `𝒜 = (ℚ_ton, +, ≤, <)`, of kind `Mass`. -/
def tonScale : MeasStructure.{0} QuantityKind arithOrder where
  carrier := Tons
  kind := .mass
  op f xs := ⟨ratOp f (fun i => (xs i).val)⟩
  rel r xs := ratRel r (fun i => (xs i).val)

/-- `ℬ = (ℚ_kg, +, ≤, <)`, of kind `Mass`. -/
def kgScale : MeasStructure.{0} QuantityKind arithOrder where
  carrier := Kilograms
  kind := .mass
  op f xs := ⟨ratOp f (fun i => (xs i).val)⟩
  rel r xs := ratRel r (fun i => (xs i).val)

/-- `(ℕ_smile, +, ≤, <)`, of kind `SmileCount`. -/
def smileScale : MeasStructure.{0} QuantityKind arithOrder where
  carrier := Smiles
  kind := .smileCount
  op f xs := ⟨natOp f (fun i => (xs i).count)⟩
  rel r xs := natRel r (fun i => (xs i).count)

/-! ## §9. 200 tons versus 41 bright smiles -/

/-- `κ(200 t) = Mass ≠ SmileCount = κ(41 smiles)`. -/
theorem tons_smiles_not_sameKind : ¬ SameKind tonScale smileScale := by
  intro h
  cases h

/-- **200 tons versus 41 bright smiles.**  No transposition `T : tons → smiles` is a valid
measurement comparison, no exact calibration exists over any calibrated range, and there is
no isomorphism of measured representations.  In particular, no map sending `200 t` to
`41` smiles — the bare numerical association — establishes comparability. -/
theorem tons_vs_smiles_not_comparable :
    ¬ SameKind tonScale smileScale ∧
    (∀ T : Tons → Smiles, ¬ ValidMeasurementComparison tonScale smileScale T) ∧
    (∀ (Bcal : Smiles → Prop) (T : Tons → Smiles),
      ¬ Nonempty (ExactCalibration tonScale smileScale Bcal T)) ∧
    ¬ Isomorphic tonScale smileScale :=
  different_quantity_kind_implies_not_comparable tons_smiles_not_sameKind

/-- **The numerical association `200 ↦ 41` does not create comparability:** a map sending
`200 t` to `41` smiles exists, yet it is neither a valid comparison nor an exact calibration
over any range. -/
theorem numerals_do_not_create_comparability :
    ∃ T : Tons → Smiles, T ⟨200⟩ = ⟨41⟩ ∧
      ¬ ValidMeasurementComparison tonScale smileScale T ∧
      ∀ Bcal : Smiles → Prop, ¬ Nonempty (ExactCalibration tonScale smileScale Bcal T) :=
  ⟨fun _ => ⟨41⟩, rfl, tons_vs_smiles_not_comparable.2.1 _,
    fun Bcal => tons_vs_smiles_not_comparable.2.2.1 Bcal _⟩

/-! ## §10. 200 tons versus 15 kilograms -/

/-- The short-ton conversion factor `907.18474 kg / t`. -/
def shortTon : Rat := 907.18474

theorem shortTon_pos : (0 : Rat) < shortTon := by decide +kernel

theorem shortTon_ne_zero : shortTon ≠ 0 := by decide +kernel

/-- `T(a) = 907.18474 a`. -/
def tonsToKg (a : Tons) : Kilograms := ⟨shortTon * a.val⟩

/-- `T⁻¹(b) = b / 907.18474`. -/
def kgToTons (b : Kilograms) : Tons := ⟨b.val / shortTon⟩

/-- `T⁻¹(T(a)) = a`. -/
theorem kgToTons_tonsToKg (a : Tons) : kgToTons (tonsToKg a) = a := by
  cases a with | mk q =>
  show (⟨shortTon * q / shortTon⟩ : Tons) = ⟨q⟩
  rw [Rat.mul_comm, Rat.mul_div_cancel shortTon_ne_zero]

/-- `T(T⁻¹(b)) = b`. -/
theorem tonsToKg_kgToTons (b : Kilograms) : tonsToKg (kgToTons b) = b := by
  cases b with | mk q =>
  show (⟨shortTon * (q / shortTon)⟩ : Kilograms) = ⟨q⟩
  rw [Rat.mul_comm, Rat.div_mul_cancel shortTon_ne_zero]

/-- `T(a + b) = T(a) + T(b)`. -/
theorem tonsToKg_add (a b : Rat) : shortTon * (a + b) = shortTon * a + shortTon * b :=
  Rat.mul_add _ _ _

/-- Multiplication by the positive factor reflects and preserves `<`. -/
theorem shortTon_lt_iff (a b : Rat) : shortTon * a < shortTon * b ↔ a < b :=
  Rat.mul_lt_mul_left shortTon_pos

/-- Multiplication by the positive factor reflects and preserves `≤`. -/
theorem shortTon_le_iff (a b : Rat) : shortTon * a ≤ shortTon * b ↔ a ≤ b := by
  constructor
  · intro h
    exact Rat.not_lt.mp fun hba => Rat.not_lt.mpr h ((shortTon_lt_iff b a).mpr hba)
  · intro h
    exact Rat.not_lt.mp fun hba => Rat.not_lt.mpr h ((shortTon_lt_iff b a).mp hba)

/-- Multiplication by the nonzero factor reflects and preserves `=`. -/
theorem shortTon_eq_iff (a b : Rat) : shortTon * a = shortTon * b ↔ a = b := by
  constructor
  · intro h
    rw [← Rat.mul_div_cancel (a := a) shortTon_ne_zero,
      ← Rat.mul_div_cancel (a := b) shortTon_ne_zero, Rat.mul_comm a, Rat.mul_comm b, h]
  · intro h
    rw [h]

/-- `T` preserves addition. -/
theorem tonsToKg_preservesOperation : PreservesOperation tonScale kgScale tonsToKg := by
  intro n f xs
  cases f
  show (⟨shortTon * ((xs 0).val + (xs 1).val)⟩ : Kilograms) =
    ⟨shortTon * (xs 0).val + shortTon * (xs 1).val⟩
  rw [tonsToKg_add]

/-- `a₁ = a₂ ⟺ T(a₁) = T(a₂)`. -/
theorem tonsToKg_eq_iff (a₁ a₂ : Tons) : a₁ = a₂ ↔ tonsToKg a₁ = tonsToKg a₂ := by
  cases a₁ with | mk p =>
  cases a₂ with | mk q =>
  constructor
  · intro h
    rw [h]
  · intro h
    have h' : shortTon * p = shortTon * q := congrArg Kilograms.val h
    rw [(shortTon_eq_iff p q).mp h']

/-- `≤` and `<` are preserved and reflected: `a ≤ b ⟺ T(a) ≤ T(b)`, `a < b ⟺ T(a) < T(b)`. -/
theorem tonsToKg_rel_iff {n : Nat} (r : OrderRel n) (xs : Fin n → Tons) :
    tonScale.rel r xs ↔ kgScale.rel r (fun i => tonsToKg (xs i)) := by
  cases r
  · exact (shortTon_le_iff _ _).symm
  · exact (shortTon_lt_iff _ _).symm

/-- `T` admits full substitution. -/
theorem tonsToKg_fullSubstitution : FullSubstitution tonScale kgScale tonsToKg :=
  ⟨tonsToKg_eq_iff, tonsToKg_rel_iff⟩

/-- **Tons to kilograms is an exact calibration over the whole kilogram scale.** -/
def tonsKgCalibration : ExactCalibration tonScale kgScale (fun _ => True) tonsToKg where
  sameKind := rfl
  hom := ⟨tonsToKg_preservesOperation, preservesEquality_of_sameness _,
    fun r xs => (tonsToKg_rel_iff r xs).mp⟩
  fullSubst := tonsToKg_fullSubstitution
  lands _ := trivial
  recal := kgToTons
  recal_spec b _ := tonsToKg_kgToTons b

/-- **`ℚ_ton ≅ ℚ_kg`**, with `T(a) = 907.18474 a` as the isomorphic transposition and
`T⁻¹(b) = b / 907.18474` as its structure-preserving inverse. -/
theorem tons_kg_isomorphic_transposition : IsomorphicTransposition tonScale kgScale tonsToKg :=
  exact_full_calibration_isomorphic_transposition tonsKgCalibration

/-- The reverse calibration of `tonsKgCalibration` is `T⁻¹`. -/
theorem tonsKgCalibration_recal : tonsKgCalibration.recal = kgToTons := rfl

/-- **`200 t = 181436.948 kg`** under `T`. -/
theorem two_hundred_tons_eq : tonsToKg ⟨200⟩ = ⟨181436.948⟩ := by
  show (⟨shortTon * 200⟩ : Kilograms) = ⟨181436.948⟩
  have h : shortTon * 200 = 181436.948 := by decide +kernel
  rw [h]

/-- **`200 t` and `15 kg` are comparable but unequal:** `T(200 t) ≠ 15 kg` and
`15 kg < T(200 t)`, i.e. `200 t > 15 kg`. -/
theorem two_hundred_tons_vs_fifteen_kg :
    SameKind tonScale kgScale ∧
    tonsToKg ⟨200⟩ ≠ ⟨15⟩ ∧
    kgScale.rel OrderRel.lt (fun i => if i = 0 then ⟨15⟩ else tonsToKg ⟨200⟩) := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [two_hundred_tons_eq]
    intro h
    have h' : (181436.948 : Rat) = 15 := congrArg Kilograms.val h
    revert h'
    decide +kernel
  · show (15 : Rat) < shortTon * 200
    decide +kernel

/-- **Equality is representation-independent:** for ton values,
`a = b ⟺ T(a) = T(b)`; for example `200 t = 200 t` and `T(200 t) = 181436.948 kg`, while
`200 t ≠ 15 kg` read in either representation. -/
theorem equality_representation_independent (a b : Tons) :
    a = b ↔ tonsToKg a = tonsToKg b :=
  tonsToKg_eq_iff a b

/-! ## §5 and §8 in exact integer arithmetic: a proper calibrated range

Whole short tons are transposed into integer multiples of `10 mg = 10⁻⁵ kg` by
`T(n) = 90718474 n`.  This `T` is not surjective onto all of `ℤ`, so by §8 it is no exact
calibration onto the whole fine-unit scale; it is an exact calibration onto the calibrated
range `B_cal = 90718474 ℤ`, and therefore (§6) an isomorphism `ℤ_ton ≅ ℬ_cal`. -/

/-- Mass expressed in whole short tons. -/
structure WholeTons where
  /-- the number of tons -/
  val : Int

/-- Mass expressed in units of `10 mg = 10⁻⁵ kg`. -/
structure FineUnits where
  /-- the number of `10 mg` units -/
  val : Int

/-- Interpretation of the operation symbols on integers. -/
def intOp : {n : Nat} → ArithOp n → (Fin n → Int) → Int
  | _, .add, xs => xs 0 + xs 1

/-- Interpretation of the relation symbols on integers. -/
def intRel : {n : Nat} → OrderRel n → (Fin n → Int) → Prop
  | _, .le, xs => xs 0 ≤ xs 1
  | _, .lt, xs => xs 0 < xs 1

/-- `(ℤ_ton, +, ≤, <)`, of kind `Mass`. -/
def wholeTonScale : MeasStructure.{0} QuantityKind arithOrder where
  carrier := WholeTons
  kind := .mass
  op f xs := ⟨intOp f (fun i => (xs i).val)⟩
  rel r xs := intRel r (fun i => (xs i).val)

/-- `(ℤ_{10 mg}, +, ≤, <)`, of kind `Mass`. -/
def fineScale : MeasStructure.{0} QuantityKind arithOrder where
  carrier := FineUnits
  kind := .mass
  op f xs := ⟨intOp f (fun i => (xs i).val)⟩
  rel r xs := intRel r (fun i => (xs i).val)

/-- The short ton in `10 mg` units. -/
def shortTonFine : Int := 90718474

/-- `T(n) = 90718474 n`. -/
def tonsToFine (a : WholeTons) : FineUnits := ⟨shortTonFine * a.val⟩

/-- The calibrated range `B_cal = 90718474 ℤ`. -/
def fineCalibrated (b : FineUnits) : Prop := shortTonFine ∣ b.val

/-- The reverse reading `T⁻¹(b) = b / 90718474`. -/
def fineToTons (b : FineUnits) : WholeTons := ⟨b.val / shortTonFine⟩

theorem shortTonFine_pos : 0 < shortTonFine := by decide

theorem shortTonFine_ne_zero : shortTonFine ≠ 0 := by decide

/-- `T` preserves addition. -/
theorem tonsToFine_preservesOperation :
    PreservesOperation wholeTonScale fineScale tonsToFine := by
  intro n f xs
  cases f
  show (⟨shortTonFine * ((xs 0).val + (xs 1).val)⟩ : FineUnits) =
    ⟨shortTonFine * (xs 0).val + shortTonFine * (xs 1).val⟩
  rw [Int.mul_add]

/-- `a₁ = a₂ ⟺ T(a₁) = T(a₂)`. -/
theorem tonsToFine_eq_iff (a₁ a₂ : WholeTons) : a₁ = a₂ ↔ tonsToFine a₁ = tonsToFine a₂ := by
  cases a₁ with | mk p =>
  cases a₂ with | mk q =>
  constructor
  · intro h
    rw [h]
  · intro h
    have h' : shortTonFine * p = shortTonFine * q := congrArg FineUnits.val h
    rw [Int.eq_of_mul_eq_mul_left shortTonFine_ne_zero h']

/-- `≤` and `<` are preserved and reflected. -/
theorem tonsToFine_rel_iff {n : Nat} (r : OrderRel n) (xs : Fin n → WholeTons) :
    wholeTonScale.rel r xs ↔ fineScale.rel r (fun i => tonsToFine (xs i)) := by
  cases r
  · exact (Int.mul_le_mul_left shortTonFine_pos).symm
  · exact (Int.mul_lt_mul_left shortTonFine_pos).symm

/-- **Whole tons to `10 mg` units is an exact calibration onto `B_cal = 90718474 ℤ`.** -/
def wholeTonsCalibration :
    ExactCalibration wholeTonScale fineScale fineCalibrated tonsToFine where
  sameKind := rfl
  hom := ⟨tonsToFine_preservesOperation, preservesEquality_of_sameness _,
    fun r xs => (tonsToFine_rel_iff r xs).mp⟩
  fullSubst := ⟨tonsToFine_eq_iff, tonsToFine_rel_iff⟩
  lands a := ⟨a.val, rfl⟩
  recal := fineToTons
  recal_spec b hb := by
    cases b with | mk q =>
    show (⟨shortTonFine * (q / shortTonFine)⟩ : FineUnits) = ⟨q⟩
    rw [Int.mul_ediv_cancel' hb]

/-- **`ℤ_ton ≅ ℬ_cal`**: the whole-ton scale is isomorphic to the calibrated range. -/
theorem wholeTons_isomorphic_calibrated_range :
    Isomorphic wholeTonScale (fineScale.restrict fineCalibrated wholeTonsCalibration.closedRange) :=
  exact_calibration_isomorphic wholeTonsCalibration

/-- **§8 instance:** `10 mg` has no whole-ton representative, so `T` is no exact calibration
onto the whole `10 mg` scale. -/
theorem tonsToFine_not_full_calibration :
    ¬ Nonempty (ExactCalibration wholeTonScale fineScale (fun _ => True) tonsToFine) :=
  not_surjective_implies_not_calibration ⟨⟨1⟩, trivial, fun a h => by
    have h' : shortTonFine * a.val = 1 := congrArg FineUnits.val h
    unfold shortTonFine at h'
    omega⟩

/-- `200 t = 18143694800 × 10 mg = 181436.948 kg`, and `15 kg = 1500000 × 10 mg < T(200 t)`. -/
theorem two_hundred_whole_tons :
    tonsToFine ⟨200⟩ = ⟨18143694800⟩ ∧
    fineScale.rel OrderRel.lt (fun i => if i = 0 then ⟨1500000⟩ else tonsToFine ⟨200⟩) := by
  refine ⟨rfl, ?_⟩
  show (1500000 : Int) < shortTonFine * 200
  decide

end Measure

end
