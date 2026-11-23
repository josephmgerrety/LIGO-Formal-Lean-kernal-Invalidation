# Association and causal identification

On the same observational table, one response is insensitive to intervention and another changes with intervention. The supplied data also contradict additivity for any map fitting all observed pairs.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [association export roots](../../verification/roots/association.txt)

[Full Lean source](../../PerfectAssociation.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>PerfectAssociation.no_population_additive_hom</code></summary>

```lean
theorem no_population_additive_hom :
    ¬ ∃ h, AssociationAlgebra.AdditiveHom h ∧ FitsPopulation h
```

[`PerfectAssociation.no_population_additive_hom`](../../PerfectAssociation.lean#L18)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L2) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.no_population_additive_iso</code></summary>

```lean
theorem no_population_additive_iso :
    ¬ ∃ h, AssociationAlgebra.AdditiveIso h ∧ FitsPopulation h
```

[`PerfectAssociation.no_population_additive_iso`](../../PerfectAssociation.lean#L29)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L3) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.model_generates_observations</code></summary>

```lean
theorem model_generates_observations (β : Int) (s : Nat) :
    observe β (Int.ofNat s) = (Q s, x s)
```

[`PerfectAssociation.model_generates_observations`](../../PerfectAssociation.lean#L36)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L4) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.identical_observation_opposite_causation</code></summary>

```lean
theorem identical_observation_opposite_causation :
    (∀ s : Int, observe 0 s = observe 1 s) ∧
    ¬ CausesQX 0 ∧ CausesQX 1
```

[`PerfectAssociation.identical_observation_opposite_causation`](../../PerfectAssociation.lean#L41)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L5) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.perfect_association_without_causation_hom_or_iso</code></summary>

```lean
theorem perfect_association_without_causation_hom_or_iso :
    COR A Q x = true ∧
    Q ≠ x ∧
    ¬ DirectCauses .q .x ∧
    ¬ CausalPath .q .x ∧
    ¬ CausesQX 0 ∧
    (¬ ∃ h, AssociationAlgebra.AdditiveHom h ∧ FitsPopulation h) ∧
    (¬ ∃ h, AssociationAlgebra.AdditiveIso h ∧ FitsPopulation h) ∧
    (¬ ∃ h, ResponseHom 0 1 h) ∧
    ¬ Nonempty (ResponseIso 0 1)
```

[`PerfectAssociation.perfect_association_without_causation_hom_or_iso`](../../PerfectAssociation.lean#L49)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L6) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.perfect_association_does_not_entail_causation</code></summary>

```lean
theorem perfect_association_does_not_entail_causation :
    ¬ (COR A Q x = true → CausesQX 0)
```

[`PerfectAssociation.perfect_association_does_not_entail_causation`](../../PerfectAssociation.lean#L64)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L7) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.perfect_association_does_not_entail_additive_hom</code></summary>

```lean
theorem perfect_association_does_not_entail_additive_hom :
    ¬ (COR A Q x = true →
       ∃ h, AssociationAlgebra.AdditiveHom h ∧ FitsPopulation h)
```

[`PerfectAssociation.perfect_association_does_not_entail_additive_hom`](../../PerfectAssociation.lean#L69)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L8) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.perfect_association_does_not_entail_additive_iso</code></summary>

```lean
theorem perfect_association_does_not_entail_additive_iso :
    ¬ (COR A Q x = true →
       ∃ h, AssociationAlgebra.AdditiveIso h ∧ FitsPopulation h)
```

[`PerfectAssociation.perfect_association_does_not_entail_additive_iso`](../../PerfectAssociation.lean#L74)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L9) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.no_uniform_observational_causal_rule</code></summary>

```lean
theorem no_uniform_observational_causal_rule :
    ¬ ∃ identify : List (Int × Int) → Bool,
      ∀ β : Int, identify (observationalTable β A) = true ↔ CausesQX β
```

[`PerfectAssociation.no_uniform_observational_causal_rule`](../../PerfectAssociation.lean#L80)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L10) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>
