import Init

namespace PerfectAssociation

/-- Constructor proofs keep the closed causal counterexample free of axioms. -/
private theorem zero_mul_core (z : Int) : (0 : Int) * z = 0 := by
  cases z with
  | ofNat n => exact congrArg Int.ofNat (Nat.zero_mul n)
  | negSucc n =>
    change Int.negOfNat (0 * (n + 1)) = 0
    rw [Nat.zero_mul]
    rfl

private theorem sub_self_core (z : Int) : z - z = 0 := by
  cases z with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n => exact Int.subNatNat_self (n + 1)
  | negSucc n => exact Int.subNatNat_self (n + 1)

/-- Distinct positive affine observables from the same integer source. -/
def qValue (s : Int) : Int := 2 * s + 3
def xValue (s : Int) : Int := 7 * s - 4

/-- A hidden response coefficient. Its correction vanishes on the observed graph. -/
def response (β s q : Int) : Int := xValue s + β * (q - qValue s)

def observe (β s : Int) : Int × Int := (qValue s, response β s (qValue s))

def observationalTable (β : Int) (A : List Nat) : List (Int × Int) :=
  A.map (fun a => observe β (Int.ofNat a))

/-- A Q intervention changes X at a fixed exogenous source. -/
def CausesQX (β : Int) : Prop :=
  ∃ s u v : Int, response β s u ≠ response β s v

/-- Statistical coincidence holds at every source value, for every response coefficient. -/
theorem observation_independent (β s : Int) :
    observe β s = (qValue s, xValue s) := by
  unfold observe response
  rw [sub_self_core, Int.mul_zero, Int.add_zero]

theorem tables_independent (β γ : Int) (A : List Nat) :
    observationalTable β A = observationalTable γ A := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    simp only [observationalTable, List.map_cons] at *
    rw [observation_independent, observation_independent, ih]

/-- Both observables are distinct, without assuming their inequality. -/
theorem observables_distinct : qValue ≠ xValue := by
  intro h
  have h0 := congrArg (fun f : Int → Int => f 0) h
  have hfalse : qValue 0 ≠ xValue 0 := by decide
  exact hfalse h0

/-- Absence of effect is derived from the structural equation for every intervention. -/
theorem intervention_invariant (s q : Int) : response 0 s q = xValue s := by
  unfold response
  rw [zero_mul_core, Int.add_zero]

theorem no_causation : ¬ CausesQX 0 := by
  intro h
  obtain ⟨s, u, v, huv⟩ := h
  exact huv ((intervention_invariant s u).trans (intervention_invariant s v).symm)

/-- A closed witness of an actual intervention effect in an observationally identical model. -/
theorem causation_one : CausesQX 1 := by
  refine ⟨1, 5, 6, ?_⟩
  decide

/-- Every nonzero integer coefficient is an observationally hidden causal effect. -/
theorem causation_iff_nonzero (β : Int) : CausesQX β ↔ β ≠ 0 := by
  constructor
  · intro h hz
    subst β
    exact no_causation h
  · intro hβ
    refine ⟨0, 3, 4, ?_⟩
    intro heq
    have hz : β = 0 := by
      simp [response, qValue, xValue] at heq
      exact (Int.add_left_cancel
        (show (-4 : Int) + 0 = -4 + β from heq)).symm
    exact hβ hz

/-- The effect question has an executable decision once its structural parameter is known. -/
def causalDecision (β : Int) : Bool := decide (β ≠ 0)

theorem causalDecision_spec (β : Int) : causalDecision β = true ↔ CausesQX β := by
  constructor
  · intro h
    exact (causation_iff_nonzero β).mpr (of_decide_eq_true h)
  · intro h
    exact decide_eq_true ((causation_iff_nonzero β).mp h)

/-- Two labelled interventions recover the coefficient erased by every observation. -/
theorem intervention_recovers_parameter (β : Int) :
    response β 0 4 - response β 0 3 = β := by
  change ((-4 : Int) + β * 1) - (-4 + β * 0) = β
  rw [Int.mul_one, Int.mul_zero, Int.add_zero,
      Int.add_comm (-4) β, Int.add_sub_cancel]

theorem two_interventions_identify (β γ : Int)
    (h3 : response β 0 3 = response γ 0 3)
    (h4 : response β 0 4 = response γ 0 4) : β = γ := by
  have hd : response β 0 4 - response β 0 3 =
      response γ 0 4 - response γ 0 3 := by rw [h4, h3]
  exact (intervention_recovers_parameter β).symm.trans
    (hd.trans (intervention_recovers_parameter γ))

/-- Source and intervention labels are fixed; only the outcome may be recoded. -/
def ResponseHom (β γ : Int) (h : Int → Int → Int) : Prop :=
  ∀ s q, h s (response β s q) = response γ s q

/-- An isomorphism preserves intervention responses in both directions. -/
structure ResponseIso (β γ : Int) where
  forward : Int → Int → Int
  backward : Int → Int → Int
  forward_preserves : ResponseHom β γ forward
  backward_preserves : ResponseHom γ β backward
  left_inverse : ∀ s y, backward s (forward s y) = y
  right_inverse : ∀ s y, forward s (backward s y) = y

/-- Identical observations conceal a failure of any response-preserving homomorphism. -/
theorem no_response_hom : ¬ ∃ h, ResponseHom 0 1 h := by
  intro hex
  obtain ⟨h, hh⟩ := hex
  have h5 : h 1 3 = 3 := hh 1 5
  have h6 : h 1 3 = 4 := hh 1 6
  have hfalse : (3 : Int) ≠ 4 := by decide
  exact hfalse (h5.symm.trans h6)

theorem no_response_iso : ¬ Nonempty (ResponseIso 0 1) := by
  intro hex
  obtain ⟨e⟩ := hex
  exact no_response_hom ⟨e.forward, e.forward_preserves⟩

theorem no_response_iso_reverse : ¬ Nonempty (ResponseIso 1 0) := by
  intro hex
  obtain ⟨e⟩ := hex
  exact no_response_hom ⟨e.backward, e.backward_preserves⟩

/-- The reverse homomorphism collapses each outcome fibre to its baseline. -/
def collapse (s _y : Int) : Int := xValue s

theorem reverse_response_hom : ResponseHom 1 0 collapse := by
  intro s q
  exact (intervention_invariant s q).symm

/-- Response preservation transports invariance, revealing its direction. -/
theorem response_hom_preserves_invariance (β γ : Int) (h : Int → Int → Int)
    (hh : ResponseHom β γ h)
    (hinv : ∀ s u v, response β s u = response β s v) :
    ∀ s u v, response γ s u = response γ s v := by
  intro s u v
  exact (hh s u).symm.trans
    ((congrArg (h s) (hinv s u v)).trans (hh s v))

theorem no_response_hom_to_effect (β : Int) (hβ : β ≠ 0) :
    ¬ ∃ h, ResponseHom 0 β h := by
  intro hex
  obtain ⟨h, hh⟩ := hex
  have hinv : ∀ s u v, response 0 s u = response 0 s v :=
    fun s u v => (intervention_invariant s u).trans (intervention_invariant s v).symm
  have targetInvariant := response_hom_preserves_invariance 0 β h hh hinv
  obtain ⟨s, u, v, hdiff⟩ := (causation_iff_nonzero β).mpr hβ
  exact hdiff (targetInvariant s u v)

/-- No data-only Boolean rule can correctly decide the effect in both models. -/
theorem no_observational_identifier (A : List Nat)
    (identify : List (Int × Int) → Bool) :
    ¬ ((identify (observationalTable 0 A) = true ↔ CausesQX 0) ∧
       (identify (observationalTable 1 A) = true ↔ CausesQX 1)) := by
  intro h
  have hc : identify (observationalTable 1 A) = true := h.2.mpr causation_one
  have heq := tables_independent 0 1 A
  rw [← heq] at hc
  exact no_causation (h.1.mp hc)

inductive Node where
  | source | q | x
  deriving DecidableEq, Repr

/-- The zero-coefficient common-source graph is computed from node constructors. -/
def DirectCauses (a b : Node) : Prop :=
  match a with
  | .source =>
    match b with
    | .source => False
    | .q => True
    | .x => True
  | .q => False
  | .x => False

instance (a b : Node) : Decidable (DirectCauses a b) := by
  cases a <;> cases b <;> unfold DirectCauses <;> exact inferInstance

inductive CausalPath : Node → Node → Prop where
  | edge {a b : Node} : DirectCauses a b → CausalPath a b
  | step {a b c : Node} : DirectCauses a b → CausalPath b c → CausalPath a c

theorem no_direct_causation : ¬ DirectCauses .q .x := fun h => h

theorem no_outgoing_q (n : Node) : ¬ DirectCauses .q n := by
  cases n <;> exact fun h => h

theorem no_causal_path (n : Node) : ¬ CausalPath .q n := by
  intro h
  cases h with
  | edge he => exact no_outgoing_q _ he
  | step he _ => exact no_outgoing_q _ he

theorem common_source_graph : DirectCauses .source .q ∧ DirectCauses .source .x :=
  ⟨True.intro, True.intro⟩

#print axioms observation_independent
#print axioms tables_independent
#print axioms observables_distinct
#print axioms intervention_invariant
#print axioms no_causation
#print axioms causation_one
#print axioms causation_iff_nonzero
#print axioms causalDecision_spec
#print axioms intervention_recovers_parameter
#print axioms two_interventions_identify
#print axioms no_response_hom
#print axioms no_response_iso
#print axioms no_response_iso_reverse
#print axioms reverse_response_hom
#print axioms response_hom_preserves_invariance
#print axioms no_response_hom_to_effect
#print axioms no_observational_identifier
#print axioms no_direct_causation
#print axioms no_causal_path

end PerfectAssociation
