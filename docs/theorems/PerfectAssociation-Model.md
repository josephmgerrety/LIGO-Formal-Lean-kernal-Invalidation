# Interventions in the response model

The parameter multiplying the deviation of the intervention from the observational input disappears from the observed table. A difference of two labeled interventions returns it exactly.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [association export roots](../../verification/roots/association.txt)

[Full Lean source](../../PerfectAssociation/Model.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>PerfectAssociation.observation_independent</code></summary>

```lean
theorem observation_independent (β s : Int) :
    observe β s = (qValue s, xValue s)
```

[`PerfectAssociation.observation_independent`](../../PerfectAssociation/Model.lean#L39)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L514) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.tables_independent</code></summary>

```lean
theorem tables_independent (β γ : Int) (A : List Nat) :
    observationalTable β A = observationalTable γ A
```

[`PerfectAssociation.tables_independent`](../../PerfectAssociation/Model.lean#L44)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L515) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.observables_distinct</code></summary>

```lean
theorem observables_distinct : qValue ≠ xValue
```

[`PerfectAssociation.observables_distinct`](../../PerfectAssociation/Model.lean#L53)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L516) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.intervention_invariant</code></summary>

```lean
theorem intervention_invariant (s q : Int) : response 0 s q = xValue s
```

[`PerfectAssociation.intervention_invariant`](../../PerfectAssociation/Model.lean#L60)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L517) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.no_causation</code></summary>

```lean
theorem no_causation : ¬ CausesQX 0
```

[`PerfectAssociation.no_causation`](../../PerfectAssociation/Model.lean#L64)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L518) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.causation_one</code></summary>

```lean
theorem causation_one : CausesQX 1
```

[`PerfectAssociation.causation_one`](../../PerfectAssociation/Model.lean#L70)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L519) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.causation_iff_nonzero</code></summary>

```lean
theorem causation_iff_nonzero (β : Int) : CausesQX β ↔ β ≠ 0
```

[`PerfectAssociation.causation_iff_nonzero`](../../PerfectAssociation/Model.lean#L75)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L520) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.causalDecision_spec</code></summary>

```lean
theorem causalDecision_spec (β : Int) : causalDecision β = true ↔ CausesQX β
```

[`PerfectAssociation.causalDecision_spec`](../../PerfectAssociation/Model.lean#L92)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L522) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.intervention_recovers_parameter</code></summary>

```lean
theorem intervention_recovers_parameter (β : Int) :
    response β 0 4 - response β 0 3 = β
```

[`PerfectAssociation.intervention_recovers_parameter`](../../PerfectAssociation/Model.lean#L100)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L523) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.two_interventions_identify</code></summary>

```lean
theorem two_interventions_identify (β γ : Int)
    (h3 : response β 0 3 = response γ 0 3)
    (h4 : response β 0 4 = response γ 0 4) : β = γ
```

[`PerfectAssociation.two_interventions_identify`](../../PerfectAssociation/Model.lean#L106)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L524) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.no_response_hom</code></summary>

```lean
theorem no_response_hom : ¬ ∃ h, ResponseHom 0 1 h
```

[`PerfectAssociation.no_response_hom`](../../PerfectAssociation/Model.lean#L128)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L527) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.no_response_iso</code></summary>

```lean
theorem no_response_iso : ¬ Nonempty (ResponseIso 0 1)
```

[`PerfectAssociation.no_response_iso`](../../PerfectAssociation/Model.lean#L136)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L528) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.no_response_iso_reverse</code></summary>

```lean
theorem no_response_iso_reverse : ¬ Nonempty (ResponseIso 1 0)
```

[`PerfectAssociation.no_response_iso_reverse`](../../PerfectAssociation/Model.lean#L141)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L529) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.reverse_response_hom</code></summary>

```lean
theorem reverse_response_hom : ResponseHom 1 0 collapse
```

[`PerfectAssociation.reverse_response_hom`](../../PerfectAssociation/Model.lean#L149)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L531) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.response_hom_preserves_invariance</code></summary>

```lean
theorem response_hom_preserves_invariance (β γ : Int) (h : Int → Int → Int)
    (hh : ResponseHom β γ h)
    (hinv : ∀ s u v, response β s u = response β s v) :
    ∀ s u v, response γ s u = response γ s v
```

[`PerfectAssociation.response_hom_preserves_invariance`](../../PerfectAssociation/Model.lean#L154)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L532) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.no_response_hom_to_effect</code></summary>

```lean
theorem no_response_hom_to_effect (β : Int) (hβ : β ≠ 0) :
    ¬ ∃ h, ResponseHom 0 β h
```

[`PerfectAssociation.no_response_hom_to_effect`](../../PerfectAssociation/Model.lean#L162)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L533) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.no_observational_identifier</code></summary>

```lean
theorem no_observational_identifier (A : List Nat)
    (identify : List (Int × Int) → Bool) :
    ¬ ((identify (observationalTable 0 A) = true ↔ CausesQX 0) ∧
       (identify (observationalTable 1 A) = true ↔ CausesQX 1))
```

[`PerfectAssociation.no_observational_identifier`](../../PerfectAssociation/Model.lean#L173)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L534) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.no_direct_causation</code></summary>

```lean
theorem no_direct_causation : ¬ DirectCauses .q .x
```

[`PerfectAssociation.no_direct_causation`](../../PerfectAssociation/Model.lean#L205)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L538) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.no_outgoing_q</code></summary>

```lean
theorem no_outgoing_q (n : Node) : ¬ DirectCauses .q n
```

[`PerfectAssociation.no_outgoing_q`](../../PerfectAssociation/Model.lean#L207)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L539) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.no_causal_path</code></summary>

```lean
theorem no_causal_path (n : Node) : ¬ CausalPath .q n
```

[`PerfectAssociation.no_causal_path`](../../PerfectAssociation/Model.lean#L210)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L540) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>

<details>
<summary><code>PerfectAssociation.common_source_graph</code></summary>

```lean
theorem common_source_graph : DirectCauses .source .q ∧ DirectCauses .source .x
```

[`PerfectAssociation.common_source_graph`](../../PerfectAssociation/Model.lean#L216)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L541) · [Accepted checker runs](../../verification/evidence/checkers.log#L1)

</details>
