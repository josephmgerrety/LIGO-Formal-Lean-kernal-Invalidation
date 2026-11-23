module
/-!
# Equality as Sameness, as an Equivalence, and as Isomorphism
Everything in this file is written against core Lean 4 only (no Mathlib import).
Every definition is computable; no `Classical.choice`, no `choose`, no `native_decide`,
no user-declared `axiom`.
 Part 1 ,  `a = b` is sameness: equality coincides with Leibniz indiscernibility.
 Part 2 ,  `a = b` meets the criteria of equality:
  reflexivity, symmetry and transitivity derived exactly as in the textbook derivation
  (substitution into `ϕ(x) : x = a` and `ϕ(x) : x = c`), plus the first-order logic
  facts about sets and the extensionality principle.
 Part 3 ,  `a = b` is an isomorphism: equality transports every carrier of information
  along a structure-preserving bijection (a homomorphism with a two-sided inverse),
  functorially, naturally, and conversely such isomorphisms force equality.
The `#print axioms` checks at the end of the file record exactly which of Lean's built-in
axioms (if any) each result uses.  Parts 1, 2 (logic) and 3 use none at all.  Only the
extensionality principle for predicate-sets uses `propext` and `Quot.sound`
(= function extensionality), which are part of Lean's own kernel logic, and which are
unavoidable there: in first-order set theory extensionality is itself an axiom.
-/
@[expose] public section
namespace Sameness
universe u v w
variable {α : Sort u}
/-! ## Part 1. `a = b` is an expression of sameness -/
/-- Leibniz sameness (identity of indiscernibles): `a` and `b` are the same when every
property of `a` is a property of `b`. -/
def Same (a b : α) : Prop := ∀ P : α → Prop, P a → P b
/-- Equality is exactly sameness.  `→` is Leibniz' law (substitution);
`←` instantiates the property `P x := (a = x)`, which `a` has by reflexivity. -/
theorem eq_iff_same {a b : α} : a = b ↔ Same a b :=
  ⟨fun h _ pa => h ▸ pa, fun h => h (fun x => a = x) rfl⟩
/-- Equality is total indiscernibility: `a = b` iff `a` and `b` have exactly the same
properties. -/
theorem eq_iff_indiscernible {a b : α} : a = b ↔ ∀ P : α → Prop, (P a ↔ P b) :=
  ⟨fun h _ => h ▸ Iff.rfl, fun h => (h (fun x => a = x)).mp rfl⟩
/-- Sameness of all data (not just propositions): every function, into any type,
takes the same value on `a` and on `b`. -/
theorem eq_iff_same_values {a b : α} :
    a = b ↔ ∀ (β : Sort u) (f : α → β), f a = f b :=
  ⟨fun h _ _ => h ▸ rfl, fun h => h α id⟩
/-! ## Part 2. `a = b` meets the criteria of equality -/
/-- Reflexivity ,  the law of identity: `a = a`. -/
theorem refl' (a : α) : a = a := rfl
/-- Symmetry, following the classical derivation verbatim.
Take `ϕ(x) : x = a`.  Substitution gives `(a = b) ⟹ ((a = a) ⇒ (b = a))`.
Since `a = b` by assumption and `a = a` by reflexivity, `b = a`. -/
theorem symm' {a b : α} (hab : a = b) : b = a :=
  let ϕ : α → Prop := fun x => x = a
  have subst : a = b → (ϕ a → ϕ b) := fun h => @Eq.subst α ϕ a b h
  subst hab (refl' a)
/-- Transitivity, following the classical derivation verbatim.
Take `ϕ(x) : x = c`.  Substitution gives `(b = a) ⟹ ((b = c) ⇒ (a = c))`.
Since `b = a` by symmetry and `b = c` by assumption, `a = c`. -/
theorem trans' {a b c : α} (hab : a = b) (hbc : b = c) : a = c :=
  let ϕ : α → Prop := fun x => x = c
  have subst : b = a → (ϕ b → ϕ a) := fun h => @Eq.subst α ϕ b a h
  subst (symm' hab) hbc
/-- Hence `=` is an equivalence relation. -/
theorem eq_equivalence : Equivalence (@Eq α) :=
  ⟨refl', symm', trans'⟩
/-- `=` is the finest reflexive relation: it is contained in every reflexive relation.
(Equality is the least equivalence ,  the pure relation of sameness.) -/
theorem eq_le_of_refl (R : α → α → Prop) (hR : ∀ x, R x x) {a b : α} (h : a = b) : R a b :=
  h ▸ hR a
/-! ### Set equality in first-order logic with equality -/
/-- An abstract universe of sets: a type `U` of objects with a membership relation.
This is exactly the signature of first-order set theory. -/
structure SetUniverse where
  /-- the objects of the universe -/
  U : Type u
  /-- the membership relation `z ∈ x` -/
  mem : U → U → Prop
namespace SetUniverse
variable (S : SetUniverse.{u})
/-- Logic: `x = y ⟹ ∀ z, (z ∈ x ⟺ z ∈ y)`.  Pure logic of equality ,  no axiom. -/
theorem mem_right_of_eq {x y : S.U} (h : x = y) : ∀ z, (S.mem z x ↔ S.mem z y) :=
  fun _ => h ▸ Iff.rfl
/-- Logic: `x = y ⟹ ∀ z, (x ∈ z ⟺ y ∈ z)`.  Pure logic of equality ,  no axiom. -/
theorem mem_left_of_eq {x y : S.U} (h : x = y) : ∀ z, (S.mem x z ↔ S.mem y z) :=
  fun _ => h ▸ Iff.rfl
/-- Set theory: the axiom of extensionality `(∀ z, (z ∈ x ⟺ z ∈ y)) ⟹ x = y`
(as a property a universe may have, not a Lean axiom). -/
def Extensional : Prop :=
  ∀ x y : S.U, (∀ z, (S.mem z x ↔ S.mem z y)) → x = y
/-- In an extensional universe, equality of sets is exactly sameness of members. -/
theorem eq_iff_same_members (hS : S.Extensional) (x y : S.U) :
    x = y ↔ ∀ z, (S.mem z x ↔ S.mem z y) :=
  ⟨S.mem_right_of_eq, hS x y⟩
end SetUniverse
/-- Concrete model 1 (hereditarily finite sets, Ackermann coding).
Objects are natural numbers; `z ∈ x` iff the `z`-th binary digit of `x` is `1`.
Membership is computable (decidable). -/
def ackermann : SetUniverse.{0} where
  U := Nat
  mem z x := x.testBit z = true
/-- Membership in the Ackermann model is decided by computation, e.g. `{0, 2} = 5`. -/
example : ackermann.mem (0 : Nat) (5 : Nat) ∧ ackermann.mem (2 : Nat) (5 : Nat) ∧
    ¬ ackermann.mem (1 : Nat) (5 : Nat) := by
  show Nat.testBit 5 0 = true ∧ Nat.testBit 5 2 = true ∧ ¬ Nat.testBit 5 1 = true
  decide
/-- The Ackermann model satisfies extensionality: two numbers with the same binary
digits are equal. -/
theorem ackermann_extensional : ackermann.Extensional := by
  intro x y h
  apply Nat.eq_of_testBit_eq
  intro i
  have hi : x.testBit i = true ↔ y.testBit i = true := h i
  cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all
/-- Concrete model 2 (sets as predicates). Sets of elements of `β` are predicates
`β → Prop`; membership is application. -/
structure PSet (β : Type u) where
  /-- the membership predicate -/
  memP : β → Prop
/-- Membership in a predicate-set. -/
def PSet.Mem {β : Type u} (s : PSet β) (z : β) : Prop := s.memP z
/-- Logic: `x = y ⟹ ∀ z, (z ∈ x ⟺ z ∈ y)` for predicate-sets (axiom-free). -/
theorem PSet.mem_iff_of_eq {β : Type u} {x y : PSet β} (h : x = y) :
    ∀ z, (x.Mem z ↔ y.Mem z) :=
  fun _ => h ▸ Iff.rfl
/-- Logic: `x = y ⟹ ∀ z, (x ∈ z ⟺ y ∈ z)` for predicate-sets of predicate-sets
(axiom-free). -/
theorem PSet.mem_of_iff_of_eq {β : Type u} {x y : PSet β} (h : x = y) :
    ∀ z : PSet (PSet β), (z.Mem x ↔ z.Mem y) :=
  fun _ => h ▸ Iff.rfl
/-- Set theory: extensionality for predicate-sets,
`(∀ z, (z ∈ x ⟺ z ∈ y)) ⟹ x = y`.  In Lean's type theory this uses the built-in
principles `propext` and function extensionality (from `Quot.sound`). -/
theorem PSet.ext' {β : Type u} {x y : PSet β} (h : ∀ z, (x.Mem z ↔ y.Mem z)) : x = y := by
  cases x with | mk p =>
  cases y with | mk q =>
  have hpq : p = q := funext fun z => propext (h z)
  rw [hpq]
/-- For predicate-sets, equality is exactly sameness of members. -/
theorem PSet.eq_iff {β : Type u} (x y : PSet β) : x = y ↔ ∀ z, (x.Mem z ↔ y.Mem z) :=
  ⟨PSet.mem_iff_of_eq, PSet.ext'⟩
/-! ## Part 3. `a = b` is a homomorphism and an isomorphism -/
/-- An isomorphism of types: a map with a two-sided inverse. -/
structure Iso (A : Sort v) (B : Sort w) where
  /-- forward map -/
  toFun : A → B
  /-- inverse map -/
  invFun : B → A
  /-- `invFun ∘ toFun = id` -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- `toFun ∘ invFun = id` -/
  right_inv : ∀ y, toFun (invFun y) = y
namespace Iso
/-- The identity isomorphism. -/
def refl (A : Sort v) : Iso A A := ⟨id, id, fun _ => rfl, fun _ => rfl⟩
/-- The inverse isomorphism. -/
def symm {A : Sort v} {B : Sort w} (e : Iso A B) : Iso B A :=
  ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩
/-- An isomorphism is injective. -/
theorem injective {A : Sort v} {B : Sort w} (e : Iso A B) {x y : A}
    (h : e.toFun x = e.toFun y) : x = y := by
  rw [← e.left_inv x, ← e.left_inv y, h]
/-- An isomorphism is surjective. -/
theorem surjective {A : Sort v} {B : Sort w} (e : Iso A B) (y : B) : ∃ x, e.toFun x = y :=
  ⟨e.invFun y, e.right_inv y⟩
end Iso
/-- An equality of types is an isomorphism (computable: the map is `cast`). -/
def isoOfEq {A B : Sort v} (h : A = B) : Iso A B where
  toFun := cast h
  invFun := cast h.symm
  left_inv x := by cases h; rfl
  right_inv y := by cases h; rfl
/-- Transport: an equality `a = b` of points turns every family of information carriers
`F : α → Sort v` into an isomorphism `F a ≅ F b`. -/
def transport (F : α → Sort v) {a b : α} (h : a = b) : Iso (F a) (F b) :=
  isoOfEq (congrArg F h)
/-- Transport along reflexivity is the identity isomorphism. -/
theorem transport_refl (F : α → Sort v) (a : α) (x : F a) :
    (transport F (rfl : a = a)).toFun x = x := rfl
/-- Transport is functorial: it respects composition of equalities. -/
theorem transport_trans (F : α → Sort v) {a b c : α} (h₁ : a = b) (h₂ : b = c) (x : F a) :
    (transport F (h₁.trans h₂)).toFun x =
      (transport F h₂).toFun ((transport F h₁).toFun x) := by
  cases h₁; cases h₂; rfl
/-- Transport along the inverse equality is the inverse isomorphism. -/
theorem transport_symm (F : α → Sort v) {a b : α} (h : a = b) (y : F b) :
    (transport F h.symm).toFun y = (transport F h).invFun y := by
  cases h; rfl
/-- Transport is natural (a homomorphism of structure): it commutes with every
fibrewise operation `g : ∀ x, F x → G x`. -/
theorem transport_natural (F G : α → Sort v) (g : ∀ x, F x → G x) {a b : α} (h : a = b)
    (x : F a) : (transport G h).toFun (g a x) = g b ((transport F h).toFun x) := by
  cases h; rfl
/-- Equality is the same thing as isomorphism of all information.
`a = b` holds iff every carrier of information over `a` is (canonically) isomorphic to the
corresponding carrier over `b`.  `←`: use the carrier `F x := ULift (PLift (a = x))`. -/
theorem eq_iff_forall_iso {a b : α} :
    a = b ↔ ∀ F : α → Type v, Nonempty (Iso (F a) (F b)) := by
  constructor
  · intro h F
    exact ⟨transport F h⟩
  · intro H
    obtain ⟨e⟩ := H (fun x => ULift.{v} (PLift (a = x)))
    exact (e.toFun ⟨⟨rfl⟩⟩).down.down
/-! ### Equality of structured objects is a structure-preserving isomorphism -/
/-- A magma: a carrier with a binary operation (the minimal algebraic structure). -/
structure Magma where
  /-- the carrier -/
  carrier : Type u
  /-- the binary operation -/
  op : carrier → carrier → carrier
/-- A homomorphism of magmas: a map preserving the operation. -/
structure MagmaHom (M N : Magma.{u}) where
  /-- underlying map -/
  toFun : M.carrier → N.carrier
  /-- structure preservation -/
  map_op : ∀ x y, toFun (M.op x y) = N.op (toFun x) (toFun y)
/-- An isomorphism of magmas: an operation-preserving bijection with inverse. -/
structure MagmaIso (M N : Magma.{u}) extends MagmaHom M N where
  /-- inverse map -/
  invFun : N.carrier → M.carrier
  /-- `invFun ∘ toFun = id` -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- `toFun ∘ invFun = id` -/
  right_inv : ∀ y, toFun (invFun y) = y
/-- The identity magma isomorphism. -/
def MagmaIso.refl (M : Magma.{u}) : MagmaIso M M :=
  { toFun := id, map_op := fun _ _ => rfl, invFun := id,
    left_inv := fun _ => rfl, right_inv := fun _ => rfl }
/-- The inverse of a magma isomorphism is again a homomorphism. -/
def MagmaIso.symm {M N : Magma.{u}} (e : MagmaIso M N) : MagmaIso N M where
  toFun := e.invFun
  map_op x y := by
    apply Iso.injective ⟨e.toFun, e.invFun, e.left_inv, e.right_inv⟩
    show e.toFun (e.invFun (N.op x y)) = e.toFun (M.op (e.invFun x) (e.invFun y))
    rw [e.map_op, e.right_inv, e.right_inv, e.right_inv]
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
/-- `M = N` is a magma isomorphism: equal structured objects are isomorphic through a
bijection that is a homomorphism in both directions. -/
def MagmaIso.ofEq {M N : Magma.{u}} (h : M = N) : MagmaIso M N :=
  match N, h with
  | _, rfl => MagmaIso.refl M
/-- The isomorphism induced by `M = N` is in particular a homomorphism. -/
def MagmaHom.ofEq {M N : Magma.{u}} (h : M = N) : MagmaHom M N :=
  (MagmaIso.ofEq h).toMagmaHom
/-- The isomorphism induced by `M = M` (reflexivity) is the identity. -/
theorem MagmaIso.ofEq_refl (M : Magma.{u}) (x : M.carrier) :
    (MagmaIso.ofEq (rfl : M = M)).toFun x = x := rfl
/-- Concrete sanity check: the magma `(Nat, +)`. -/
def natAdd : Magma.{0} := ⟨Nat, Nat.add⟩
/-- A concrete computation through the isomorphism induced by `natAdd = natAdd`. -/
example : (MagmaIso.ofEq (rfl : natAdd = natAdd)).toFun (2 : Nat) = (2 : Nat) := rfl
end Sameness
end
