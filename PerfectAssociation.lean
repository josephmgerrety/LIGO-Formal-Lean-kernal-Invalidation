import PerfectAssociation.Statistics
import PerfectAssociation.Model
import PerfectAssociation.Algebra
import PerfectAssociation.EqualityBridge

/-!
# Perfect association: causal and algebraic non-entailment

The same finite integer data supply all witnesses. No missing-causation
hypothesis is accepted: its absence is derived from intervention semantics.
-/
namespace PerfectAssociation

/-- All twenty observed pairs, with the given finite population. -/
def FitsPopulation (h : Int → Int) : Prop :=
  ∀ s ∈ A, h (Q s) = x s

theorem no_population_additive_hom :
    ¬ ∃ h, AssociationAlgebra.AdditiveHom h ∧ FitsPopulation h := by
  intro hex
  obtain ⟨h, hh, hfit⟩ := hex
  have h1 : 1 ∈ A := .head _
  have h6 : 6 ∈ A :=
    .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  have h5 : h 5 = 3 := hfit 1 h1
  have h15 : h 15 = 38 := hfit 6 h6
  exact AssociationAlgebra.no_hom_from_two_samples h hh h5 h15

theorem no_population_additive_iso :
    ¬ ∃ h, AssociationAlgebra.AdditiveIso h ∧ FitsPopulation h := by
  intro hex
  obtain ⟨h, hi, hf⟩ := hex
  exact no_population_additive_hom ⟨h, hi.1, hf⟩

/-- The family really generates the exact Q and x used by COR. -/
theorem model_generates_observations (β : Int) (s : Nat) :
    observe β (Int.ofNat s) = (Q s, x s) :=
  observation_independent β (Int.ofNat s)

/-- Pointwise identity for every source, together with opposite causal answers. -/
theorem identical_observation_opposite_causation :
    (∀ s : Int, observe 0 s = observe 1 s) ∧
    ¬ CausesQX 0 ∧ CausesQX 1 := by
  refine ⟨?_, no_causation, causation_one⟩
  intro s
  exact (observation_independent 0 s).trans (observation_independent 1 s).symm

/-- This is the requested new proof, with all its objects and witnesses closed. -/
theorem perfect_association_without_causation_hom_or_iso :
    COR A Q x = true ∧
    Q ≠ x ∧
    ¬ DirectCauses .q .x ∧
    ¬ CausalPath .q .x ∧
    ¬ CausesQX 0 ∧
    (¬ ∃ h, AssociationAlgebra.AdditiveHom h ∧ FitsPopulation h) ∧
    (¬ ∃ h, AssociationAlgebra.AdditiveIso h ∧ FitsPopulation h) ∧
    (¬ ∃ h, ResponseHom 0 1 h) ∧
    ¬ Nonempty (ResponseIso 0 1) :=
  ⟨perfect_correlation, Q_ne_x, no_direct_causation, no_causal_path .x,
   no_causation, no_population_additive_hom, no_population_additive_iso,
   no_response_hom, no_response_iso⟩

/-- Perfect association cannot force the effect; the zero model is a counterexample. -/
theorem perfect_association_does_not_entail_causation :
    ¬ (COR A Q x = true → CausesQX 0) :=
  fun h => no_causation (h perfect_correlation)

/-- Nor can it force a homomorphism preserving the specified additive operation. -/
theorem perfect_association_does_not_entail_additive_hom :
    ¬ (COR A Q x = true →
       ∃ h, AssociationAlgebra.AdditiveHom h ∧ FitsPopulation h) :=
  fun h => no_population_additive_hom (h perfect_correlation)

theorem perfect_association_does_not_entail_additive_iso :
    ¬ (COR A Q x = true →
       ∃ h, AssociationAlgebra.AdditiveIso h ∧ FitsPopulation h) :=
  fun h => no_population_additive_iso (h perfect_correlation)

/-- A complete table cannot decide causation uniformly over the structural family. -/
theorem no_uniform_observational_causal_rule :
    ¬ ∃ identify : List (Int × Int) → Bool,
      ∀ β : Int, identify (observationalTable β A) = true ↔ CausesQX β := by
  intro hex
  obtain ⟨identify, hcorrect⟩ := hex
  exact no_observational_identifier A identify ⟨hcorrect 0, hcorrect 1⟩

end PerfectAssociation
