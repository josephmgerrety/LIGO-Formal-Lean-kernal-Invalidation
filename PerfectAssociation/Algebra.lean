import Std

/-!
# Perfect association does not entail preservation of algebra

All constructions use executable integers and explicit inverse data.
No choice, `noncomputable`, `native_decide`, or new axiom is used.
-/

namespace AssociationAlgebra

def Affine (a b : Int) (z : Int) : Int := a * z + b

def AdditiveHom (f : Int → Int) : Prop :=
  ∀ u v, f (u + v) = f u + f v

/-- An algebraic isomorphism must preserve addition and possess an explicit inverse. -/
def AdditiveIso (f : Int → Int) : Prop :=
  AdditiveHom f ∧ ∃ g : Int → Int,
    (∀ z, g (f z) = z) ∧ (∀ z, f (g z) = z)

def AdditiveDefect (f : Int → Int) (u v : Int) : Int :=
  f (u + v) - f u - f v

/- These short primitive proofs keep the principal obstructions entirely
axiom free, including propositional extensionality. -/
private theorem nat_add_left_cancel (a b c : Nat) (h : a + b = a + c) : b = c := by
  induction a with
  | zero => exact (Nat.zero_add b).symm.trans (h.trans (Nat.zero_add c))
  | succ a ih =>
    rw [Nat.succ_add, Nat.succ_add] at h
    exact ih (Nat.succ.inj h)

private theorem int_zero_add (b : Int) : (0 : Int) + b = b := by
  cases b with
  | ofNat n => exact congrArg Int.ofNat (Nat.zero_add n)
  | negSucc n => rfl

private theorem int_zero_mul (z : Int) : (0 : Int) * z = 0 := by
  cases z with
  | ofNat n =>
    change Int.ofNat (0 * n) = Int.ofNat 0
    exact congrArg Int.ofNat (Nat.zero_mul n)
  | negSucc n =>
    change Int.negOfNat (0 * (n + 1)) = Int.ofNat 0
    rw [Nat.zero_mul]
    rfl

private theorem int_add_one_ne_self (z : Int) : z + 1 ≠ z := by
  intro h
  cases z with
  | ofNat n =>
    have hh : n + 1 = n := Int.ofNat.inj h
    exact Nat.succ_ne_self n hh
  | negSucc n =>
    cases n with
    | zero => exact Int.noConfusion h
    | succ n =>
      change Int.negSucc n = Int.negSucc (n + 1) at h
      exact Nat.succ_ne_self n (Int.negSucc.inj h).symm

private theorem int_add_idempotent_zero (b : Int) (h : b = b + b) : b = 0 := by
  cases b with
  | ofNat n =>
    have hh : n + 0 = n + n := Int.ofNat.inj h
    have hn : 0 = n := nat_add_left_cancel n 0 n hh
    exact congrArg Int.ofNat hn.symm
  | negSucc n =>
    have hh : n + 0 = n + (n + 1) := Int.negSucc.inj h
    have hn : 0 = n + 1 := nat_add_left_cancel n 0 (n + 1) hh
    exact False.elim (Nat.noConfusion hn)

/-- Additive preservation forces every affine map's offset to vanish. -/
theorem affine_hom_offset_zero (a b : Int) (h : AdditiveHom (Affine a b)) : b = 0 := by
  have hz := h 0 0
  have hf : Affine a b 0 = b := by
    unfold Affine
    rw [Int.mul_zero]
    exact int_zero_add b
  change Affine a b 0 = Affine a b 0 + Affine a b 0 at hz
  rw [hf] at hz
  exact int_add_idempotent_zero b hz

/-- The offset invisible to centered association is exactly the additive defect. -/
theorem affine_defect (a b u v : Int) :
    AdditiveDefect (Affine a b) u v = -b := by
  unfold AdditiveDefect Affine
  rw [Int.mul_add, Int.add_sub_add_right]
  rw [Int.add_comm (a * u) (a * v), Int.add_sub_cancel]
  rw [← Int.sub_sub, Int.sub_self, Int.zero_sub]

/-- Complete classification of affine homomorphisms of the additive integers. -/
theorem affine_hom_iff (a b : Int) :
    AdditiveHom (Affine a b) ↔ b = 0 := by
  constructor
  · exact affine_hom_offset_zero a b
  · intro hb
    intro u v
    simp only [Affine, hb, Int.add_zero, Int.mul_add]

theorem affine_nonzero_offset_not_hom (a b : Int) (hb : b ≠ 0) :
    ¬ AdditiveHom (Affine a b) := by
  intro h
  exact hb (affine_hom_offset_zero a b h)

theorem affine_nonzero_offset_not_iso (a b : Int) (hb : b ≠ 0) :
    ¬ AdditiveIso (Affine a b) := by
  intro h
  exact affine_nonzero_offset_not_hom a b hb h.1

theorem seven_minus_four_not_hom : ¬ AdditiveHom (Affine 7 (-4)) := by
  exact affine_nonzero_offset_not_hom 7 (-4) (by decide)

theorem seven_minus_four_not_iso : ¬ AdditiveIso (Affine 7 (-4)) := by
  exact affine_nonzero_offset_not_iso 7 (-4) (by decide)

/-- Every affine map preserves a shifted target operation, which exposes why
operation choice must be explicit when speaking of homomorphism. -/
def shiftedAdd (b u v : Int) : Int := u + v - b

theorem affine_preserves_shifted_add (a b u v : Int) :
    Affine a b (u + v) = shiftedAdd b (Affine a b u) (Affine a b v) := by
  unfold Affine shiftedAdd
  rw [Int.mul_add, Int.add_sub_assoc, Int.add_sub_cancel]
  exact Int.add_right_comm (a * u) (a * v) b

theorem shifted_add_associative (b u v w : Int) :
    shiftedAdd b (shiftedAdd b u v) w =
      shiftedAdd b u (shiftedAdd b v w) := by
  simp only [shiftedAdd, Int.sub_eq_add_neg, Int.add_assoc]
  rw [Int.add_left_comm (-b) w (-b)]

theorem shifted_add_identity (b u : Int) :
    shiftedAdd b b u = u ∧ shiftedAdd b u b = u := by
  constructor
  · unfold shiftedAdd
    rw [Int.add_comm b u, Int.add_sub_cancel]
  · exact Int.add_sub_cancel u b

/-- A carrier together with a specified binary operation. -/
structure Magma where
  carrier : Type
  op : carrier → carrier → carrier

structure MagmaHom (M N : Magma) where
  toFun : M.carrier → N.carrier
  map_op : ∀ u v, toFun (M.op u v) = N.op (toFun u) (toFun v)

structure MagmaIso (M N : Magma) extends MagmaHom M N where
  invFun : N.carrier → M.carrier
  left_inv : ∀ u, invFun (toFun u) = u
  right_inv : ∀ v, toFun (invFun v) = v

abbrev intAdd : Magma := ⟨Int, Int.add⟩
abbrev intMul : Magma := ⟨Int, Int.mul⟩

/-- Equality of the full structured objects transports their entire operation. -/
def MagmaIso.refl (M : Magma) : MagmaIso M M :=
  { toFun := fun z => z,
    map_op := fun _ _ => rfl,
    invFun := fun z => z,
    left_inv := fun _ => rfl,
    right_inv := fun _ => rfl }

def MagmaIso.ofEq {M N : Magma} (h : M = N) : MagmaIso M N :=
  match h with
  | rfl => MagmaIso.refl M

theorem MagmaIso.injective {M N : Magma} (e : MagmaIso M N)
    (u v : M.carrier) (h : e.toFun u = e.toFun v) : u = v := by
  have hh := congrArg e.invFun h
  rw [e.left_inv, e.left_inv] at hh
  exact hh

/-- Intrinsic obstruction: additive integers admit cancellation, whereas
multiplicative integers contain an absorbing zero. No magma isomorphism exists. -/
theorem int_add_not_isomorphic_int_mul : ¬ Nonempty (MagmaIso intAdd intMul) := by
  intro h
  obtain ⟨e⟩ := h
  let z : Int := e.invFun (0 : Int)
  have hz : e.toFun z = (0 : Int) := e.right_inv (0 : Int)
  have hsame : e.toFun (z + 1) = e.toFun z := by
    calc
      e.toFun (z + 1) = Int.mul (e.toFun z) (e.toFun (1 : Int)) := e.map_op z (1 : Int)
      _ = (0 : Int) := by rw [hz]; exact int_zero_mul _
      _ = e.toFun z := hz.symm
  exact int_add_one_ne_self z (e.injective (z + 1) z hsame)

theorem int_add_ne_int_mul : intAdd ≠ intMul := by
  intro h
  exact int_add_not_isomorphic_int_mul ⟨MagmaIso.ofEq h⟩

/-- The identical value observation does not preserve distinct operations. -/
theorem identity_observation_not_hom :
    ¬ (∀ u v : Int, u + v = u * v) := by
  intro h
  have hbad := h 1 1
  have impossible : (2 : Int) = 1 := hbad
  exact (by decide : (2 : Int) ≠ 1) impossible

/-- A calibration map must take every supplied source measurement to its
paired target measurement. This fixes the map under discussion. -/
def CalibrationFits (h : Int → Int) : Prop :=
  ∀ s : Nat, h (2 * Int.ofNat s + 3) = 7 * Int.ofNat s - 4

/-- The finite pair of samples Q(1)=5,x(1)=3 and Q(6)=15,x(6)=38
already refutes every compatible additive homomorphism. -/
theorem no_hom_from_two_samples (h : Int → Int) (hh : AdditiveHom h)
    (h5 : h 5 = 3) (h15 : h 15 = 38) : False := by
  have h9 : h 15 = 9 := by
    calc
      h 15 = h ((5 + 5) + 5) := rfl
      _ = h (5 + 5) + h 5 := hh (5 + 5) 5
      _ = (h 5 + h 5) + h 5 :=
        congrArg (fun z : Int => z + h 5) (hh 5 5)
      _ = 9 := by rw [h5]; rfl
  have impossible : (38 : Int) = 9 := h15.symm.trans h9
  exact (by decide : (38 : Int) ≠ 9) impossible

/-- The exact supplied observables Q(s)=2s+3 and x(s)=7s−4 admit no additive
homomorphism fitting their association. Just s=1 and s=6 force a contradiction. -/
theorem no_hom_fits_supplied_observations :
    ¬ ∃ h : Int → Int, AdditiveHom h ∧ CalibrationFits h := by
  intro hex
  obtain ⟨h, hh, hfit⟩ := hex
  exact no_hom_from_two_samples h hh (hfit 1) (hfit 6)

theorem no_iso_fits_supplied_observations :
    ¬ ∃ h : Int → Int, AdditiveIso h ∧ CalibrationFits h := by
  intro hex
  obtain ⟨h, hi, hf⟩ := hex
  exact no_hom_fits_supplied_observations ⟨h, hi.1, hf⟩

/-- Perfect association can coexist with a homomorphism and isomorphism;
therefore the requested negations are non-entailment results with specified
operations and maps, never an assertion that association excludes algebra. -/
theorem identity_additive_iso : AdditiveIso (fun z : Int => z) :=
  ⟨fun _ _ => rfl, ⟨(fun z => z), (fun _ => rfl), (fun _ => rfl)⟩⟩

#print axioms affine_defect
#print axioms affine_hom_offset_zero
#print axioms affine_hom_iff
#print axioms affine_nonzero_offset_not_hom
#print axioms affine_nonzero_offset_not_iso
#print axioms seven_minus_four_not_hom
#print axioms seven_minus_four_not_iso
#print axioms affine_preserves_shifted_add
#print axioms shifted_add_associative
#print axioms shifted_add_identity
#print axioms MagmaIso.ofEq
#print axioms MagmaIso.injective
#print axioms int_add_not_isomorphic_int_mul
#print axioms int_add_ne_int_mul
#print axioms identity_observation_not_hom
#print axioms no_hom_from_two_samples
#print axioms no_iso_fits_supplied_observations
#print axioms no_hom_fits_supplied_observations
#print axioms identity_additive_iso

end AssociationAlgebra
