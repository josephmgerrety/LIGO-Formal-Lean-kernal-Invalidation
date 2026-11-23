/-!
# Equality, all information carriers, and a selected carrier

Core Lean only. Equality transports every information family along an
isomorphism. Conversely, isomorphisms for every family detect equality by
testing the family that records equality itself. An isomorphism for one
selected information family is insufficient, as the final closed example shows.

Every definition is computable. No choice, noncomputable declaration, native
decision procedure, additional axiom, or admitted proof is used.
-/

namespace EqualityBridge

universe u v w
variable {α : Sort u}

/-- Leibniz sameness: every property of `a` is also a property of `b`. -/
def Same (a b : α) : Prop := ∀ P : α → Prop, P a → P b

theorem eq_iff_same {a b : α} : a = b ↔ Same a b :=
  ⟨fun h _ pa => h ▸ pa, fun h => h (fun x => a = x) rfl⟩

theorem eq_iff_indiscernible {a b : α} :
    a = b ↔ ∀ P : α → Prop, P a ↔ P b :=
  ⟨fun h _ => h ▸ Iff.rfl,
   fun h => (h (fun x => a = x)).mp rfl⟩

/-- An isomorphism of bare carriers: a map with a two-sided inverse. -/
structure Iso (A : Sort v) (B : Sort w) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

namespace Iso

def refl (A : Sort v) : Iso A A :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def symm {A : Sort v} {B : Sort w} (e : Iso A B) : Iso B A :=
  ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩

theorem injective {A : Sort v} {B : Sort w} (e : Iso A B) {x y : A}
    (h : e.toFun x = e.toFun y) : x = y := by
  rw [← e.left_inv x, ← e.left_inv y, h]

theorem surjective {A : Sort v} {B : Sort w} (e : Iso A B) (y : B) :
    ∃ x, e.toFun x = y :=
  ⟨e.invFun y, e.right_inv y⟩

end Iso

/-- Equal carriers are isomorphic by executable equality transport. -/
def isoOfEq {A B : Sort v} (h : A = B) : Iso A B where
  toFun := cast h
  invFun := cast h.symm
  left_inv x := by cases h; rfl
  right_inv y := by cases h; rfl

/-- Equality of indices transports every information carrier. -/
def transport (F : α → Sort v) {a b : α} (h : a = b) : Iso (F a) (F b) :=
  isoOfEq (congrArg F h)

theorem transport_refl (F : α → Sort v) (a : α) (x : F a) :
    (transport F (rfl : a = a)).toFun x = x := rfl

theorem transport_trans (F : α → Sort v) {a b c : α}
    (h₁ : a = b) (h₂ : b = c) (x : F a) :
    (transport F (h₁.trans h₂)).toFun x =
      (transport F h₂).toFun ((transport F h₁).toFun x) := by
  cases h₁
  cases h₂
  rfl

theorem transport_symm (F : α → Sort v) {a b : α} (h : a = b) (y : F b) :
    (transport F h.symm).toFun y = (transport F h).invFun y := by
  cases h
  rfl

/-- Transport commutes with every operation indexed by the information family. -/
theorem transport_natural (F G : α → Sort v) (g : ∀ x, F x → G x)
    {a b : α} (h : a = b) (x : F a) :
    (transport G h).toFun (g a x) = g b ((transport F h).toFun x) := by
  cases h
  rfl

/--
The quantifier over all information families is essential. The converse uses
the carrier `F x := ULift (PLift (a = x))`; its elements record equality to `a`.
This theorem requires only existence of each isomorphism, not any choice of
isomorphisms into a data-valued function.
-/
theorem eq_iff_forall_iso {a b : α} :
    a = b ↔ ∀ F : α → Type v, Nonempty (Iso (F a) (F b)) := by
  constructor
  · intro h F
    exact ⟨transport F h⟩
  · intro H
    obtain ⟨e⟩ := H (fun x => ULift.{v} (PLift (a = x)))
    exact (e.toFun ⟨⟨rfl⟩⟩).down.down

/-- A selected information family may erase the distinction between indices. -/
def constantInfo (_n : Nat) : Type := Bool

def selectedCarrierIso : Iso (constantInfo 0) (constantInfo 1) :=
  Iso.refl Bool

theorem distinct_indices_selected_iso :
    Nonempty (Iso (constantInfo 0) (constantInfo 1)) ∧ (0 : Nat) ≠ 1 :=
  ⟨⟨selectedCarrierIso⟩, by decide⟩

/-- One carrier isomorphism cannot replace the all-family condition. -/
theorem selected_iso_does_not_entail_equality :
    ¬ (Nonempty (Iso (constantInfo 0) (constantInfo 1)) → (0 : Nat) = 1) := by
  intro h
  exact distinct_indices_selected_iso.2 (h distinct_indices_selected_iso.1)

#print axioms eq_iff_same
#print axioms eq_iff_indiscernible
#print axioms Iso.refl
#print axioms Iso.symm
#print axioms Iso.injective
#print axioms Iso.surjective
#print axioms isoOfEq
#print axioms transport
#print axioms transport_refl
#print axioms transport_trans
#print axioms transport_symm
#print axioms transport_natural
#print axioms eq_iff_forall_iso
#print axioms selectedCarrierIso
#print axioms distinct_indices_selected_iso
#print axioms selected_iso_does_not_entail_equality

end EqualityBridge
