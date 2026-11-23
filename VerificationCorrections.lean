import PerfectAssociation.LigoNullSpace

/-!
# Variance of a common offset and identification by an aggregate anchor

This supplement reconstructs the three propositions stated in Part I, §§38, 39
and 43 of the supplied manuscript. Its definitions come from `LigoNullSpace`.
-/

namespace VerificationCorrections

open LigoNullSpace LigoCongruence

/-- The unnormalized first and second moments of the two channels on the eight
equally weighted outcomes, for every integer common-error amplitude. -/
theorem common_error_variance_family_all (t : Int) :
    momD1 (samples t) = 0 ∧ momD2 (samples t) = 16 ∧
    momR1 (samples t) = 0 ∧ momR2 (samples t) = 32 * (t * t) + 16 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · simp only [samples, momR1]
    omega
  · simp only [samples, momR2]
    have hp : 2 * t = t + t := by omega
    have hn : 2 * (-t) = -t + -t := by omega
    simp only [hp, hn, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
      Int.mul_one, Int.one_mul]
    omega

/-- The difference moments stay fixed while the squared reconstruction channel
exceeds any prescribed natural-number bound multiplied by 32. -/
theorem reconstruction_variance_unbounded (K : Nat) :
    ∃ t : Int, momD1 (samples t) = 0 ∧ momD2 (samples t) = 16 ∧
      momR1 (samples t) = 0 ∧ 32 * (K : Int) < momR2 (samples t) := by
  let t := (K : Int) + 1
  obtain ⟨h₁, h₂, h₃, h₄⟩ := common_error_variance_family_all t
  refine ⟨t, h₁, h₂, h₃, ?_⟩
  have hpos : 1 ≤ t := by dsimp [t]; omega
  have hsq : 1 * t ≤ t * t := Int.mul_le_mul_of_nonneg_right hpos (by omega)
  have hlt : (K : Int) < t := by dsimp [t]; omega
  rw [h₄]
  omega

/-- One measurement of the sum of the four common offsets. -/
def aggregateOffset : Row := ⟨0, 1, 1, 1, 1, 0⟩

/-- Together, the total level and the aggregate offset determine the source. -/
theorem aggregate_anchor_suffices :
    IsValidFor (measureSuite [rowSum, aggregateOffset]) (ev rowP) := by
  apply (audit_exact _ rowP).mpr
  intro v hv
  have hs : 2*v.P + 2*v.gCal + 2*v.gTime + 2*v.gAct + 2*v.gSens + 0*v.d = 0 :=
    hv rowSum (.head _)
  have hg : 0*v.P + 1*v.gCal + 1*v.gTime + 1*v.gAct + 1*v.gSens + 0*v.d = 0 :=
    hv aggregateOffset (.tail _ (.head _))
  show 1*v.P + 0*v.gCal + 0*v.gTime + 0*v.gAct + 0*v.gSens + 0*v.d = 0
  omega

end VerificationCorrections
