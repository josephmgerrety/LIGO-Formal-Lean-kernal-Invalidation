# Finite population and exact covariance

Finite integer sums certify positive perfect correlation on the stated population. The affine covariance and spread identities extend the calculation to every admissible finite population.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [association export roots](../../verification/roots/association.txt)

[Full Lean source](../../PerfectAssociation/Statistics.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>PerfectAssociation.exact_moments</code></summary>

```lean
theorem exact_moments :
    A.length = 20 ∧
    total A S = 210 ∧ cross A S S = 2870 ∧ spread A S = 13300 ∧
    total A Q = 480 ∧ cross A Q Q = 14180 ∧ spread A Q = 53200 ∧
    total A x = 1390 ∧ cross A x x = 129190 ∧ spread A x = 651700 ∧
    cross A Q x = 42670 ∧ centered A Q x = 186200
```

[`PerfectAssociation.exact_moments`](../../PerfectAssociation/Statistics.lean#L36)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L551) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.S_changes</code></summary>

```lean
theorem S_changes : 0 < spread A S
```

[`PerfectAssociation.S_changes`](../../PerfectAssociation/Statistics.lean#L44)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L552) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.covariance_scales</code></summary>

```lean
theorem covariance_scales : centered A Q x = 14 * spread A S
```

[`PerfectAssociation.covariance_scales`](../../PerfectAssociation/Statistics.lean#L47)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L553) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.variance_scales</code></summary>

```lean
theorem variance_scales :
    spread A Q = 4 * spread A S ∧ spread A x = 49 * spread A S
```

[`PerfectAssociation.variance_scales`](../../PerfectAssociation/Statistics.lean#L50)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L554) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.perfect_correlation</code></summary>

```lean
theorem perfect_correlation : COR A Q x = true
```

[`PerfectAssociation.perfect_correlation`](../../PerfectAssociation/Statistics.lean#L54)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L555) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.positive_exact_certificate</code></summary>

```lean
theorem positive_exact_certificate :
    0 < spread A Q ∧ 0 < spread A x ∧ 0 < centered A Q x ∧
    centered A Q x * centered A Q x = spread A Q * spread A x
```

[`PerfectAssociation.positive_exact_certificate`](../../PerfectAssociation/Statistics.lean#L57)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L556) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.Q_ne_x</code></summary>

```lean
theorem Q_ne_x : Q ≠ x
```

[`PerfectAssociation.Q_ne_x`](../../PerfectAssociation/Statistics.lean#L62)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L557) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.distinct_on_population</code></summary>

```lean
theorem distinct_on_population : Q 1 ≠ x 1
```

[`PerfectAssociation.distinct_on_population`](../../PerfectAssociation/Statistics.lean#L68)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L558) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.exact_observational_line</code></summary>

```lean
theorem exact_observational_line :
    ∀ s ∈ A, 2 * x s = 7 * Q s - 29
```

[`PerfectAssociation.exact_observational_line`](../../PerfectAssociation/Statistics.lean#L71)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L559) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.pairwise_source_differences</code></summary>

```lean
theorem pairwise_source_differences :
    ∀ s ∈ A, ∀ t ∈ A,
      Q s - Q t = 2 * (S s - S t) ∧
      x s - x t = 7 * (S s - S t)
```

[`PerfectAssociation.pairwise_source_differences`](../../PerfectAssociation/Statistics.lean#L75)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L560) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.foldl_accumulator</code></summary>

```lean
theorem foldl_accumulator (A : List Nat) (f : Nat → Int) (z : Int) :
    A.foldl (fun z a => z + f a) z = z + total A f
```

[`PerfectAssociation.foldl_accumulator`](../../PerfectAssociation/Statistics.lean#L81)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L561) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.total_cons</code></summary>

```lean
theorem total_cons (a : Nat) (A : List Nat) (f : Nat → Int) :
    total (a :: A) f = f a + total A f
```

[`PerfectAssociation.total_cons`](../../PerfectAssociation/Statistics.lean#L91)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L562) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.total_congr</code></summary>

```lean
theorem total_congr (A : List Nat) (f g : Nat → Int)
    (h : ∀ a, f a = g a) : total A f = total A g
```

[`PerfectAssociation.total_congr`](../../PerfectAssociation/Statistics.lean#L97)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L563) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.total_add</code></summary>

```lean
theorem total_add (A : List Nat) (f g : Nat → Int) :
    total A (fun a => f a + g a) = total A f + total A g
```

[`PerfectAssociation.total_add`](../../PerfectAssociation/Statistics.lean#L106)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L564) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.total_scale</code></summary>

```lean
theorem total_scale (A : List Nat) (f : Nat → Int) (c : Int) :
    total A (fun a => c * f a) = c * total A f
```

[`PerfectAssociation.total_scale`](../../PerfectAssociation/Statistics.lean#L115)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L565) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.total_const</code></summary>

```lean
theorem total_const (A : List Nat) (c : Int) :
    total A (fun _ => c) = c * Int.ofNat A.length
```

[`PerfectAssociation.total_const`](../../PerfectAssociation/Statistics.lean#L123)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L566) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.total_affine</code></summary>

```lean
theorem total_affine (A : List Nat) (f : Nat → Int) (c d : Int) :
    total A (fun a => c * f a + d) =
      c * total A f + d * Int.ofNat A.length
```

[`PerfectAssociation.total_affine`](../../PerfectAssociation/Statistics.lean#L134)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L567) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.cross_eq_total</code></summary>

```lean
theorem cross_eq_total (A : List Nat) (f g : Nat → Int) :
    cross A f g = total A (fun a => f a * g a)
```

[`PerfectAssociation.cross_eq_total`](../../PerfectAssociation/Statistics.lean#L140)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L568) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.cross_affine</code></summary>

```lean
theorem cross_affine (A : List Nat) (f g : Nat → Int) (a b c d : Int) :
    cross A (fun s => a * f s + b) (fun s => c * g s + d) =
      a * c * cross A f g + a * d * total A f +
      b * c * total A g + b * d * Int.ofNat A.length
```

[`PerfectAssociation.cross_affine`](../../PerfectAssociation/Statistics.lean#L144)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L569) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.cancel_three</code></summary>

```lean
theorem cancel_three (w z a b c : Int) :
    w + (a + (b + (c + (-z + (-a + (-b + -c)))))) = w + -z
```

[`PerfectAssociation.cancel_three`](../../PerfectAssociation/Statistics.lean#L160)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L570) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.covariance_affine_algebra</code></summary>

```lean
theorem covariance_affine_algebra (n u v w a b c d : Int) :
    n * (a*c*w + a*d*u + b*c*v + b*d*n) -
      (a*u+b*n)*(c*v+d*n) = a*c*(n*w-u*v)
```

[`PerfectAssociation.covariance_affine_algebra`](../../PerfectAssociation/Statistics.lean#L170)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L571) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.centered_affine</code></summary>

```lean
theorem centered_affine (A : List Nat) (f g : Nat → Int) (a b c d : Int) :
    centered A (fun s => a * f s + b) (fun s => c * g s + d) =
      a * c * centered A f g
```

[`PerfectAssociation.centered_affine`](../../PerfectAssociation/Statistics.lean#L184)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L572) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.spread_affine</code></summary>

```lean
theorem spread_affine (A : List Nat) (f : Nat → Int) (a b : Int) :
    spread A (fun s => a * f s + b) = a * a * spread A f
```

[`PerfectAssociation.spread_affine`](../../PerfectAssociation/Statistics.lean#L192)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L573) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.centered_Qx_population</code></summary>

```lean
theorem centered_Qx_population (B : List Nat) :
    centered B Q x = 14 * spread B S
```

[`PerfectAssociation.centered_Qx_population`](../../PerfectAssociation/Statistics.lean#L197)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L574) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.spread_Q_population</code></summary>

```lean
theorem spread_Q_population (B : List Nat) :
    spread B Q = 4 * spread B S
```

[`PerfectAssociation.spread_Q_population`](../../PerfectAssociation/Statistics.lean#L204)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L575) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.spread_x_population</code></summary>

```lean
theorem spread_x_population (B : List Nat) :
    spread B x = 49 * spread B S
```

[`PerfectAssociation.spread_x_population`](../../PerfectAssociation/Statistics.lean#L210)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L576) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.perfect_correlation_population</code></summary>

```lean
theorem perfect_correlation_population (B : List Nat)
    (hV : 0 < spread B S) : COR B Q x = true
```

[`PerfectAssociation.perfect_correlation_population`](../../PerfectAssociation/Statistics.lean#L217)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L577) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.Q_difference</code></summary>

```lean
theorem Q_difference (s t : Nat) : Q s - Q t = 2 * (S s - S t)
```

[`PerfectAssociation.Q_difference`](../../PerfectAssociation/Statistics.lean#L232)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L578) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.x_difference</code></summary>

```lean
theorem x_difference (s t : Nat) : x s - x t = 7 * (S s - S t)
```

[`PerfectAssociation.x_difference`](../../PerfectAssociation/Statistics.lean#L236)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L579) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.difference_determinant_zero</code></summary>

```lean
theorem difference_determinant_zero (s t u v : Nat) :
    (Q s - Q t) * (x u - x v) =
      (x s - x t) * (Q u - Q v)
```

[`PerfectAssociation.difference_determinant_zero`](../../PerfectAssociation/Statistics.lean#L241)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L580) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.observational_line</code></summary>

```lean
theorem observational_line (s : Nat) : 2 * x s = 7 * Q s - 29
```

[`PerfectAssociation.observational_line`](../../PerfectAssociation/Statistics.lean#L248)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L581) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>
