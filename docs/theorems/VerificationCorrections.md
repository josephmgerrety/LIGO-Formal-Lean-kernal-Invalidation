# Supplementary variance and aggregate-anchor propositions

The unrestricted eight-outcome integer family has constant difference moments and unbounded reconstruction variance. In the six-coordinate row model, a reading of the aggregate offset suffices when the sum is known.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [compression export roots](../../verification/roots/compression.txt)

[Full Lean source](../../VerificationCorrections.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>VerificationCorrections.common_error_variance_family_all</code></summary>

```lean
theorem common_error_variance_family_all (t : Int) :
    momD1 (samples t) = 0 ∧ momD2 (samples t) = 16 ∧
    momR1 (samples t) = 0 ∧ momR2 (samples t) = 32 * (t * t) + 16
```

[`VerificationCorrections.common_error_variance_family_all`](../../VerificationCorrections.lean#L16)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L11) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>VerificationCorrections.reconstruction_variance_unbounded</code></summary>

```lean
theorem reconstruction_variance_unbounded (K : Nat) :
    ∃ t : Int, momD1 (samples t) = 0 ∧ momD2 (samples t) = 16 ∧
      momR1 (samples t) = 0 ∧ 32 * (K : Int) < momR2 (samples t)
```

[`VerificationCorrections.reconstruction_variance_unbounded`](../../VerificationCorrections.lean#L31)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L12) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>VerificationCorrections.aggregate_anchor_suffices</code></summary>

```lean
theorem aggregate_anchor_suffices :
    IsValidFor (measureSuite [rowSum, aggregateOffset]) (ev rowP)
```

[`VerificationCorrections.aggregate_anchor_suffices`](../../VerificationCorrections.lean#L47)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L14) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>
