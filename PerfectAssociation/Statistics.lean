import Init

/-!
Exact, executable finite-population statistics.  The definitions `total`,
`cross`, `centered`, `spread` and `COR` preserve the supplied foldl formulation.
All closed certificates below are kernel checked by `decide`.
-/
namespace PerfectAssociation

def total (A : List Nat) (Q : Nat → Int) : Int :=
  A.foldl (fun z a => z + Q a) 0

def cross (A : List Nat) (Q x : Nat → Int) : Int :=
  A.foldl (fun z a => z + Q a * x a) 0

def centered (A : List Nat) (Q x : Nat → Int) : Int :=
  Int.ofNat A.length * cross A Q x - total A Q * total A x

def spread (A : List Nat) (Q : Nat → Int) : Int := centered A Q Q

def COR (A : List Nat) (Q x : Nat → Int) : Bool :=
  decide (0 < centered A Q x ∧
    centered A Q x * centered A Q x = spread A Q * spread A x)

def A : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
   11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

def S (s : Nat) : Int := Int.ofNat s

def Q (s : Nat) : Int := 2 * S s + 3

def x (s : Nat) : Int := 7 * S s - 4

/-- A closed record containing every moment used by the original certificate. -/
theorem exact_moments :
    A.length = 20 ∧
    total A S = 210 ∧ cross A S S = 2870 ∧ spread A S = 13300 ∧
    total A Q = 480 ∧ cross A Q Q = 14180 ∧ spread A Q = 53200 ∧
    total A x = 1390 ∧ cross A x x = 129190 ∧ spread A x = 651700 ∧
    cross A Q x = 42670 ∧ centered A Q x = 186200 := by decide

/-- The source varies: no zero-variance degeneration occurs. -/
theorem S_changes : 0 < spread A S := by decide

/-- Affine scales multiply the covariance numerator by 2 × 7. -/
theorem covariance_scales : centered A Q x = 14 * spread A S := by decide

/-- Each variance scales by the square of its affine slope. -/
theorem variance_scales :
    spread A Q = 4 * spread A S ∧ spread A x = 49 * spread A S := by decide

/-- The exact denominator-cleared Pearson certificate returns true. -/
theorem perfect_correlation : COR A Q x = true := by decide

/-- A stronger certificate: positivity of both variances and the covariance. -/
theorem positive_exact_certificate :
    0 < spread A Q ∧ 0 < spread A x ∧ 0 < centered A Q x ∧
    centered A Q x * centered A Q x = spread A Q * spread A x := by decide

/-- The measured functions differ; the construction does not identify Q with x. -/
theorem Q_ne_x : Q ≠ x := by
  intro h
  have hzero : Q 0 = x 0 := congrArg (fun f : Nat → Int => f 0) h
  exact (by decide : ¬ (Q 0 = x 0)) hzero

/-- They already differ at the first measured individual. -/
theorem distinct_on_population : Q 1 ≠ x 1 := by decide

/-- The common-source line is observed exactly, without division. -/
theorem exact_observational_line :
    ∀ s ∈ A, 2 * x s = 7 * Q s - 29 := by decide

/-- Centering deletes the intercepts, exposing the slopes on every pair. -/
theorem pairwise_source_differences :
    ∀ s ∈ A, ∀ t ∈ A,
      Q s - Q t = 2 * (S s - S t) ∧
      x s - x t = 7 * (S s - S t) := by decide

/-- Changing the initial accumulator translates the fold result. -/
theorem foldl_accumulator (A : List Nat) (f : Nat → Int) (z : Int) :
    A.foldl (fun z a => z + f a) z = z + total A f := by
  induction A generalizing z with
  | nil => exact (Int.add_zero z).symm
  | cons a A ih =>
    change A.foldl (fun z a => z + f a) (z + f a) =
      z + A.foldl (fun z a => z + f a) (0 + f a)
    rw [ih, ih, Int.zero_add, Int.add_assoc]

/-- A recursive interface to the original foldl total. -/
theorem total_cons (a : Nat) (A : List Nat) (f : Nat → Int) :
    total (a :: A) f = f a + total A f := by
  change A.foldl (fun z a => z + f a) (0 + f a) = _
  rw [foldl_accumulator, Int.zero_add]

/-- Pointwise equality suffices; no function extensionality is used. -/
theorem total_congr (A : List Nat) (f g : Nat → Int)
    (h : ∀ a, f a = g a) : total A f = total A g := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    rw [total_cons, total_cons]
    rw [h a, ih]

/-- The exact fold total is additive. -/
theorem total_add (A : List Nat) (f g : Nat → Int) :
    total A (fun a => f a + g a) = total A f + total A g := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    rw [total_cons, total_cons, total_cons, ih]
    simp only [Int.add_assoc, Int.add_left_comm]

/-- Constant scaling commutes with the fold total. -/
theorem total_scale (A : List Nat) (f : Nat → Int) (c : Int) :
    total A (fun a => c * f a) = c * total A f := by
  induction A with
  | nil => exact (Int.mul_zero c).symm
  | cons a A ih =>
    rw [total_cons, total_cons, ih, Int.mul_add]

/-- A constant total retains every occurrence in the list population. -/
theorem total_const (A : List Nat) (c : Int) :
    total A (fun _ => c) = c * Int.ofNat A.length := by
  induction A with
  | nil => exact (Int.mul_zero c).symm
  | cons a A ih =>
    rw [total_cons, ih]
    change c + c * Int.ofNat A.length = c * Int.ofNat (A.length + 1)
    change c + c * (A.length : Int) = c * ((A.length : Int) + 1)
    rw [Int.mul_add, Int.mul_one, Int.add_comm]

/-- The affine total formula isolates slope and intercept. -/
theorem total_affine (A : List Nat) (f : Nat → Int) (c d : Int) :
    total A (fun a => c * f a + d) =
      c * total A f + d * Int.ofNat A.length := by
  rw [total_add, total_scale, total_const]

/-- Cross moments are totals of pointwise products, definitionally. -/
theorem cross_eq_total (A : List Nat) (f g : Nat → Int) :
    cross A f g = total A (fun a => f a * g a) := rfl

/-- Distribution through affine functions exposes all four cross terms. -/
theorem cross_affine (A : List Nat) (f g : Nat → Int) (a b c d : Int) :
    cross A (fun s => a * f s + b) (fun s => c * g s + d) =
      a * c * cross A f g + a * d * total A f +
      b * c * total A g + b * d * Int.ofNat A.length := by
  rw [cross_eq_total]
  have pointwise : ∀ s, (a * f s + b) * (c * g s + d) =
      ((a * c * (f s * g s) + a * d * f s) + b * c * g s) + b * d := by
    intro s
    simp only [Int.mul_add, Int.add_assoc, Int.add_left_comm,
      Int.add_comm, Int.mul_left_comm, Int.mul_comm]
  rw [total_congr A _ _ pointwise]
  rw [total_add, total_add, total_add, total_scale, total_scale,
      total_scale, total_const]
  rfl

/-- Explicit additive cancellation, retaining a constructive proof term. -/
theorem cancel_three (w z a b c : Int) :
    w + (a + (b + (c + (-z + (-a + (-b + -c)))))) = w + -z := by
  calc
    w + (a + (b + (c + (-z + (-a + (-b + -c)))))) =
        (w + -z) + ((a + -a) + ((b + -b) + (c + -c))) := by
      simp only [Int.add_assoc, Int.add_left_comm]
    _ = w + -z := by rw [Int.add_right_neg, Int.add_right_neg,
      Int.add_right_neg, Int.add_zero, Int.add_zero, Int.add_zero]

/-- Scalar polynomial calculation behind translation invariance. -/
theorem covariance_affine_algebra (n u v w a b c d : Int) :
    n * (a*c*w + a*d*u + b*c*v + b*d*n) -
      (a*u+b*n)*(c*v+d*n) = a*c*(n*w-u*v) := by
  simp only [Int.sub_eq_add_neg, Int.mul_add, Int.add_mul, Int.neg_add,
    Int.mul_neg]
  simp only [Int.add_assoc, Int.add_left_comm,
    Int.mul_left_comm, Int.mul_comm]
  exact cancel_three _ _ _ _ _

/-- Affine recoding preserves centered geometry, up to its two slopes.

The intercepts cancel identically for every list and every integer series.
The proof uses integer equalities and list induction, with no choice.
-/
theorem centered_affine (A : List Nat) (f g : Nat → Int) (a b c d : Int) :
    centered A (fun s => a * f s + b) (fun s => c * g s + d) =
      a * c * centered A f g := by
  unfold centered
  rw [cross_affine, total_affine, total_affine]
  exact covariance_affine_algebra _ _ _ _ _ _ _ _

/-- The variance of any affine recoding scales by the squared slope. -/
theorem spread_affine (A : List Nat) (f : Nat → Int) (a b : Int) :
    spread A (fun s => a * f s + b) = a * a * spread A f :=
  centered_affine A f f a b a b

/-- The supplied distinct observables have this covariance on every population. -/
theorem centered_Qx_population (B : List Nat) :
    centered B Q x = 14 * spread B S := by
  change centered B (fun s => 2 * S s + 3) (fun s => 7 * S s + (-4)) = _
  rw [centered_affine]
  rfl

/-- Their variances have these exact affine scale factors on every population. -/
theorem spread_Q_population (B : List Nat) :
    spread B Q = 4 * spread B S := by
  change spread B (fun s => 2 * S s + 3) = _
  rw [spread_affine]
  rfl

theorem spread_x_population (B : List Nat) :
    spread B x = 49 * spread B S := by
  change spread B (fun s => 7 * S s + (-4)) = _
  rw [spread_affine]
  rfl

/-- Generic exact Pearson +1: every nonconstant source population works. -/
theorem perfect_correlation_population (B : List Nat)
    (hV : 0 < spread B S) : COR B Q x = true := by
  apply decide_eq_true
  rw [centered_Qx_population, spread_Q_population, spread_x_population]
  constructor
  · exact Int.mul_pos (by decide) hV
  · calc
      (14 * spread B S) * (14 * spread B S) =
          (14 * 14) * (spread B S * spread B S) := by
        simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = (4 * 49) * (spread B S * spread B S) := rfl
      _ = (4 * spread B S) * (49 * spread B S) := by
        simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]

/-- Pair differences delete each intercept before any moment is formed. -/
theorem Q_difference (s t : Nat) : Q s - Q t = 2 * (S s - S t) := by
  unfold Q
  rw [Int.add_sub_add_right, Int.mul_sub]

theorem x_difference (s t : Nat) : x s - x t = 7 * (S s - S t) := by
  change (7 * S s + (-4)) - (7 * S t + (-4)) = _
  rw [Int.add_sub_add_right, Int.mul_sub]

/-- The difference geometry has rank one: every 2x2 minor vanishes. -/
theorem difference_determinant_zero (s t u v : Nat) :
    (Q s - Q t) * (x u - x v) =
      (x s - x t) * (Q u - Q v) := by
  rw [Q_difference, x_difference, x_difference, Q_difference]
  simp only [Int.mul_assoc, Int.mul_left_comm]

/-- An exact observational calibration holds on the entire source domain. -/
theorem observational_line (s : Nat) : 2 * x s = 7 * Q s - 29 := by
  unfold x Q
  rw [Int.mul_sub, Int.mul_add, ← Int.mul_assoc, ← Int.mul_assoc]
  change 14 * S s - 8 = (14 * S s + 21) - (21 + 8)
  rw [← Int.sub_sub, Int.add_sub_cancel]

#print axioms Q_difference
#print axioms x_difference
#print axioms difference_determinant_zero
#print axioms observational_line

#print axioms foldl_accumulator
#print axioms total_add
#print axioms total_scale
#print axioms total_const
#print axioms total_affine
#print axioms cross_affine
#print axioms covariance_affine_algebra
#print axioms centered_affine
#print axioms spread_affine
#print axioms centered_Qx_population
#print axioms spread_Q_population
#print axioms spread_x_population
#print axioms perfect_correlation_population

#eval (total A S, cross A S S, spread A S)
#eval (total A Q, cross A Q Q, spread A Q)
#eval (total A x, cross A x x, spread A x)
#eval (cross A Q x, centered A Q x, COR A Q x)

#print axioms exact_moments
#print axioms S_changes
#print axioms covariance_scales
#print axioms variance_scales
#print axioms perfect_correlation
#print axioms positive_exact_certificate
#print axioms Q_ne_x
#print axioms distinct_on_population
#print axioms exact_observational_line
#print axioms pairwise_source_differences
end PerfectAssociation
