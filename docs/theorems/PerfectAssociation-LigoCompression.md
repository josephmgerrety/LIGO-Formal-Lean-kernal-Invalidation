# Time slides, finite tails, model pooling and extrapolation

The retained coordinates specify the fibres. Concrete joint counts, finite laws, model weights, and node polynomials give counterexamples. Extra independence or polynomial-degree hypotheses provide exact positive results.

**Verification.** Both independent checkers, `con-leche` and `con-ron`, accepted the export containing each theorem below with `--verified`. `leanchecker` accepted the same export with the default Lean kernel. Each theorem is an explicit export root. [Checker record](../../VERIFICATION.md) · [compression export roots](../../verification/roots/compression.txt)

[Full Lean source](../../PerfectAssociation/LigoCompression.lean) · [All modules](../theorem-index.md)

## Declarations

Select a declaration to read its hypotheses and conclusion. The proof link opens the source at the original line. Implicit variables and type classes introduced at section scope retain their surrounding Lean context.

<details>
<summary><code>LigoCompression.frechet_bounds</code></summary>

```lean
theorem frechet_bounds (w : Coupling) :
    zeroLag w ≤ w.trigH ∧ zeroLag w ≤ w.trigL ∧ w.trigH + w.trigL ≤ w.total + zeroLag w
```

[`LigoCompression.frechet_bounds`](../../PerfectAssociation/LigoCompression.lean#L68)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L154) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.frechet_move</code></summary>

```lean
theorem frechet_move (a b c d t : Nat) :
    slideData ⟨a, b + t, c + t, d⟩ = slideData ⟨a + t, b, c, d + t⟩
```

[`LigoCompression.frechet_move`](../../PerfectAssociation/LigoCompression.lean#L76)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L155) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.slide_fibre_coordinate</code></summary>

```lean
theorem slide_fibre_coordinate : ∀ w w' : Coupling,
    slideData w = slideData w' → zeroLag w = zeroLag w' → w = w'
```

[`LigoCompression.slide_fibre_coordinate`](../../PerfectAssociation/LigoCompression.lean#L84)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L156) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.slides_invalid_for_zeroLag</code></summary>

```lean
theorem slides_invalid_for_zeroLag : IsInvalidFor slideData zeroLag
```

[`LigoCompression.slides_invalid_for_zeroLag`](../../PerfectAssociation/LigoCompression.lean#L102)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L157) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.slides_any_statistic_invalid</code></summary>

```lean
theorem slides_any_statistic_invalid {β : Sort u} (K : Nat) (S : List Coupling → β) :
    IsInvalidFor (fun w => S (List.replicate K (slid w))) zeroLag
```

[`LigoCompression.slides_any_statistic_invalid`](../../PerfectAssociation/LigoCompression.lean#L107)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L158) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.marginal_statistics_invalid</code></summary>

```lean
theorem marginal_statistics_invalid {β : Sort u} (S : Nat × Nat → Nat × Nat → β) :
    IsInvalidFor (fun w : Coupling => S (w.total, w.trigH) (w.total, w.trigL)) zeroLag
```

[`LigoCompression.marginal_statistics_invalid`](../../PerfectAssociation/LigoCompression.lean#L115)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L159) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.slides_valid_on_independence</code></summary>

```lean
theorem slides_valid_on_independence :
    IsValidFor (fun w : {w : Coupling // SlideExact w ∧ 0 < w.total} => slideData w.1)
      (fun w => zeroLag w.1)
```

[`LigoCompression.slides_valid_on_independence`](../../PerfectAssociation/LigoCompression.lean#L130)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L161) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.anchor_repairs_iff</code></summary>

```lean
theorem anchor_repairs_iff {δ : Type} (A : Coupling → δ) :
    IsValidFor (fun w => (slideData w, A w)) zeroLag ↔
      ∀ w w', slideData w = slideData w' → A w = A w' → w = w'
```

[`LigoCompression.anchor_repairs_iff`](../../PerfectAssociation/LigoCompression.lean#L145)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L162) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.slide_estimate_not_a_bound</code></summary>

```lean
theorem slide_estimate_not_a_bound :
    ∃ w w' : Coupling, slideData w = slideData w' ∧
      w.total * w.n11 < w.trigH * w.trigL ∧ w'.trigH * w'.trigL < w'.total * w'.n11
```

[`LigoCompression.slide_estimate_not_a_bound`](../../PerfectAssociation/LigoCompression.lean#L156)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L163) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.frechet_ends</code></summary>

```lean
theorem frechet_ends (r m : Nat) : slideData ⟨r, m, m, 0⟩ = slideData ⟨r + m, 0, 0, m⟩
```

[`LigoCompression.frechet_ends`](../../PerfectAssociation/LigoCompression.lean#L163)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L164) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.coincident_end_excess</code></summary>

```lean
theorem coincident_end_excess (N m : Nat) : m * (N * m) = N * (m * m)
```

[`LigoCompression.coincident_end_excess`](../../PerfectAssociation/LigoCompression.lean#L169)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L165) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.gw150914_frechet_scale</code></summary>

```lean
theorem gw150914_frechet_scale :
    slideData ⟨92159968, 16, 16, 0⟩ = slideData ⟨92159984, 0, 0, 16⟩ ∧
    92160000 * 16 = 5760000 * (16 * 16)
```

[`LigoCompression.gw150914_frechet_scale`](../../PerfectAssociation/LigoCompression.lean#L174)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L166) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.gw150914_slide_ledger</code></summary>

```lean
theorem gw150914_slide_ledger :
    16 * 86400 = 1382400 ∧ 1382400 * 10 = 13824000 ∧
    13824000 * 1382400 = 19110297600000 ∧ 19110297600000 / 31557600 = 605568 ∧
    608000 / 3 = 202666 ∧ 1382400 * 1000 / 15 = 92160000
```

[`LigoCompression.gw150914_slide_ledger`](../../PerfectAssociation/LigoCompression.lean#L181)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L167) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.chebyshev</code></summary>

```lean
theorem chebyshev (t : Nat) : ∀ L : NoiseLaw, t * t * tail t L ≤ power L
```

[`LigoCompression.chebyshev`](../../PerfectAssociation/LigoCompression.lean#L211)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L173) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.psd_invalid_for_tail</code></summary>

```lean
theorem psd_invalid_for_tail : IsInvalidFor psd (tail 5)
```

[`LigoCompression.psd_invalid_for_tail`](../../PerfectAssociation/LigoCompression.lean#L224)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L174) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.chebyshev_interval_5p1</code></summary>

```lean
theorem chebyshev_interval_5p1 :
    psd [(10, 2601)] = psd [(0, 2501), (51, 100)] ∧
    tail 51 [(10, 2601)] = 0 ∧ tail 51 [(0, 2501), (51, 100)] = 100 ∧
    51 * 51 * tail 51 [(0, 2501), (51, 100)] = power [(0, 2501), (51, 100)]
```

[`LigoCompression.chebyshev_interval_5p1`](../../PerfectAssociation/LigoCompression.lean#L229)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L175) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.tail_max_5p1</code></summary>

```lean
theorem tail_max_5p1 (L : NoiseLaw) (h : power L = 260100) : tail 51 L ≤ 100
```

[`LigoCompression.tail_max_5p1`](../../PerfectAssociation/LigoCompression.lean#L235)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L176) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.overall_invalid_for_bma</code></summary>

```lean
theorem overall_invalid_for_bma : IsInvalidFor overall bma
```

[`LigoCompression.overall_invalid_for_bma`](../../PerfectAssociation/LigoCompression.lean#L258)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L180) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.bma_witness_not_rescaled</code></summary>

```lean
theorem bma_witness_not_rescaled : ¬ SameRatio 1 1 1 5
```

[`LigoCompression.bma_witness_not_rescaled`](../../PerfectAssociation/LigoCompression.lean#L262)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L181) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.bma_shift</code></summary>

```lean
theorem bma_shift (zE zP mE mP : Int) :
    2 * (zE * mE + zP * mP) - (zE + zP) * (mE + mP) = (zP - zE) * (mP - mE)
```

[`LigoCompression.bma_shift`](../../PerfectAssociation/LigoCompression.lean#L268)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L182) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.gw150914_m1_bma_shift</code></summary>

```lean
theorem gw150914_m1_bma_shift :
    2 * (1 * 363 + 5 * 353) - (1 + 5) * (363 + 353) = (-40 : Int) ∧
    (5 - 1) * (353 - 363) = (-40 : Int)
```

[`LigoCompression.gw150914_m1_bma_shift`](../../PerfectAssociation/LigoCompression.lean#L274)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L183) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.sigmaSys2_blind</code></summary>

```lean
theorem sigmaSys2_blind (xE xP xO g : Int) :
    sigmaSys2 (xE + g) (xP + g) (xO + g) = sigmaSys2 xE xP xO
```

[`LigoCompression.sigmaSys2_blind`](../../PerfectAssociation/LigoCompression.lean#L283)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L185) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.sigmaSys2_invalid_for_common_error</code></summary>

```lean
theorem sigmaSys2_invalid_for_common_error (xE xP xO : Int) :
    IsInvalidFor (fun g : Int => sigmaSys2 (xE + g) (xP + g) (xO + g)) (fun g => g)
```

[`LigoCompression.sigmaSys2_invalid_for_common_error`](../../PerfectAssociation/LigoCompression.lean#L289)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L186) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.firstSample_equivariant</code></summary>

```lean
theorem firstSample_equivariant : ShiftEquivariant firstSample
```

[`LigoCompression.firstSample_equivariant`](../../PerfectAssociation/LigoCompression.lean#L303)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L189) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.sigmaSys_samples_blind</code></summary>

```lean
theorem sigmaSys_samples_blind (Q : List Int → Int) (hQ : ShiftEquivariant Q)
    (e p : Int) (E P : List Int) (g : Int) :
    sigmaSys2 (Q ((e :: E).map (· + g))) (Q ((p :: P).map (· + g)))
        (Q ((e :: E ++ p :: P).map (· + g))) =
      sigmaSys2 (Q (e :: E)) (Q (p :: P)) (Q (e :: E ++ p :: P))
```

[`LigoCompression.sigmaSys_samples_blind`](../../PerfectAssociation/LigoCompression.lean#L308)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L190) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.sigmaSys_samples_invalid</code></summary>

```lean
theorem sigmaSys_samples_invalid (Q : List Int → Int) (hQ : ShiftEquivariant Q)
    (e p : Int) (E P : List Int) :
    IsInvalidFor
      (fun g : Int => sigmaSys2 (Q ((e :: E).map (· + g))) (Q ((p :: P).map (· + g)))
        (Q ((e :: E ++ p :: P).map (· + g))))
      (fun g => g)
```

[`LigoCompression.sigmaSys_samples_invalid`](../../PerfectAssociation/LigoCompression.lean#L318)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L191) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.tableI_m1_sigmaSys</code></summary>

```lean
theorem tableI_m1_sigmaSys :
    sigmaSys2 416 405 411 = 61 ∧ sigmaSys2 318 319 319 = 1 ∧
    85 * 85 * 200 < 164 * 164 * 61 ∧ 164 * 164 * 61 < 95 * 95 * 200 ∧
    5 * 5 * 200 < 164 * 164 * 1 ∧ 164 * 164 * 1 < 15 * 15 * 200 ∧
    (∀ g ∈ List.range 101,
      sigmaSys2 (416 + Int.ofNat g) (405 + Int.ofNat g) (411 + Int.ofNat g) = 61)
```

[`LigoCompression.tableI_m1_sigmaSys`](../../PerfectAssociation/LigoCompression.lean#L330)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L192) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.peval_padd</code></summary>

```lean
theorem peval_padd : ∀ (p q : List Int) (x : Int), peval (padd p q) x = peval p x + peval q x
```

[`LigoCompression.peval_padd`](../../PerfectAssociation/LigoCompression.lean#L366)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L198) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.peval_pscale</code></summary>

```lean
theorem peval_pscale (a : Int) : ∀ (p : List Int) (x : Int), peval (pscale a p) x = a * peval p x
```

[`LigoCompression.peval_pscale`](../../PerfectAssociation/LigoCompression.lean#L374)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L199) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.peval_pquot</code></summary>

```lean
theorem peval_pquot (a : Int) : ∀ (p : List Int) (x : Int),
    peval p x = peval p a + (x - a) * peval (pquot a p) x
```

[`LigoCompression.peval_pquot`](../../PerfectAssociation/LigoCompression.lean#L381)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L200) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.length_padd_le</code></summary>

```lean
theorem length_padd_le : ∀ (p q : List Int) (k : Nat),
    p.length ≤ k → q.length ≤ k → (padd p q).length ≤ k
```

[`LigoCompression.length_padd_le`](../../PerfectAssociation/LigoCompression.lean#L393)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L201) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.length_pscale</code></summary>

```lean
theorem length_pscale (a : Int) : ∀ p : List Int, (pscale a p).length = p.length
```

[`LigoCompression.length_pscale`](../../PerfectAssociation/LigoCompression.lean#L404)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L202) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.length_pquot_le_self</code></summary>

```lean
theorem length_pquot_le_self (a : Int) : ∀ p : List Int, (pquot a p).length ≤ p.length
```

[`LigoCompression.length_pquot_le_self`](../../PerfectAssociation/LigoCompression.lean#L408)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L203) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.length_pquot_cons</code></summary>

```lean
theorem length_pquot_cons (a c : Int) (p : List Int) : (pquot a (c :: p)).length ≤ p.length
```

[`LigoCompression.length_pquot_cons`](../../PerfectAssociation/LigoCompression.lean#L417)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L204) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.length_pquot_pred</code></summary>

```lean
theorem length_pquot_pred (a : Int) (p : List Int) (k : Nat) (hp : p.length ≤ k + 1) :
    (pquot a p).length ≤ k
```

[`LigoCompression.length_pquot_pred`](../../PerfectAssociation/LigoCompression.lean#L423)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L205) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.vanish_everywhere</code></summary>

```lean
theorem vanish_everywhere : ∀ (nodes : List Int), Distinct nodes → ∀ (p : List Int),
    p.length ≤ nodes.length → (∀ a ∈ nodes, peval p a = 0) → ∀ x, peval p x = 0
```

[`LigoCompression.vanish_everywhere`](../../PerfectAssociation/LigoCompression.lean#L435)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L207) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.map_eq_of_mem</code></summary>

```lean
theorem map_eq_of_mem {α β : Type} (f g : α → β) :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.map f = l.map g
```

[`LigoCompression.map_eq_of_mem`](../../PerfectAssociation/LigoCompression.lean#L457)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L208) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.eq_of_map_eq</code></summary>

```lean
theorem eq_of_map_eq {α β : Type} (f g : α → β) :
    ∀ l : List α, l.map f = l.map g → ∀ a ∈ l, f a = g a
```

[`LigoCompression.eq_of_map_eq`](../../PerfectAssociation/LigoCompression.lean#L464)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L209) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.anchors_valid</code></summary>

```lean
theorem anchors_valid (nodes : List Int) (hd : Distinct nodes) (θ : Int) :
    IsValidFor (fun p : PolyLe nodes.length => nodes.map (peval p.1)) (fun p => peval p.1 θ)
```

[`LigoCompression.anchors_valid`](../../PerfectAssociation/LigoCompression.lean#L480)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L212) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.peval_nodePoly_cons</code></summary>

```lean
theorem peval_nodePoly_cons (a : Int) (l : List Int) (x : Int) :
    peval (nodePoly (a :: l)) x = (x - a) * peval (nodePoly l) x
```

[`LigoCompression.peval_nodePoly_cons`](../../PerfectAssociation/LigoCompression.lean#L498)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L213) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.nodePoly_zero</code></summary>

```lean
theorem nodePoly_zero : ∀ (l : List Int) (a : Int), a ∈ l → peval (nodePoly l) a = 0
```

[`LigoCompression.nodePoly_zero`](../../PerfectAssociation/LigoCompression.lean#L505)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L214) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.nodePoly_ne_zero</code></summary>

```lean
theorem nodePoly_ne_zero : ∀ (l : List Int) (x : Int), x ∉ l → peval (nodePoly l) x ≠ 0
```

[`LigoCompression.nodePoly_ne_zero`](../../PerfectAssociation/LigoCompression.lean#L513)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L215) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.peval_nodePoly</code></summary>

```lean
theorem peval_nodePoly : ∀ (l : List Int) (x : Int),
    peval (nodePoly l) x = l.foldr (fun b acc => (x - b) * acc) 1
```

[`LigoCompression.peval_nodePoly`](../../PerfectAssociation/LigoCompression.lean#L529)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L216) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.length_nodePoly</code></summary>

```lean
theorem length_nodePoly : ∀ l : List Int, (nodePoly l).length ≤ l.length + 1
```

[`LigoCompression.length_nodePoly`](../../PerfectAssociation/LigoCompression.lean#L538)

Lean reports no axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L217) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.anchors_invalid_one_degree_up</code></summary>

```lean
theorem anchors_invalid_one_degree_up (nodes : List Int) (θ : Int) (hθ : θ ∉ nodes) :
    IsInvalidFor (fun p : PolyLe (nodes.length + 1) => nodes.map (peval p.1))
      (fun p => peval p.1 θ)
```

[`LigoCompression.anchors_invalid_one_degree_up`](../../PerfectAssociation/LigoCompression.lean#L548)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L218) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.anchor_threshold</code></summary>

```lean
theorem anchor_threshold (nodes : List Int) (hd : Distinct nodes) (θ : Int) (hθ : θ ∉ nodes) :
    IsValidFor (fun p : PolyLe nodes.length => nodes.map (peval p.1)) (fun p => peval p.1 θ) ∧
    IsInvalidFor (fun p : PolyLe (nodes.length + 1) => nodes.map (peval p.1))
      (fun p => peval p.1 θ)
```

[`LigoCompression.anchor_threshold`](../../PerfectAssociation/LigoCompression.lean#L556)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L219) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.finite_anchors_invalid</code></summary>

```lean
theorem finite_anchors_invalid (nodes : List Int) (θ : Int) (hθ : θ ∉ nodes) :
    IsInvalidFor (fun g : Int → Int => nodes.map g) (fun g => g θ)
```

[`LigoCompression.finite_anchors_invalid`](../../PerfectAssociation/LigoCompression.lean#L563)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L220) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.double_blind</code></summary>

```lean
theorem double_blind (P nodes : List Int) (θ : Int) (hθ : θ ∉ nodes) :
    IsInvalidFor (validationView P nodes) (fun e => e.1 θ)
```

[`LigoCompression.double_blind`](../../PerfectAssociation/LigoCompression.lean#L577)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L222) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.nineteen_nodes</code></summary>

```lean
theorem nineteen_nodes :
    peval (nodePoly [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]) 7 = 0 ∧
    peval (nodePoly [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]) 20 =
      121645100408832000
```

[`LigoCompression.nineteen_nodes`](../../PerfectAssociation/LigoCompression.lean#L593)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L223) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.adj_fst</code></summary>

```lean
theorem adj_fst (a b c d x y : Int) :
    d * (a * x + b * y) - b * (c * x + d * y) = (a * d - b * c) * x
```

[`LigoCompression.adj_fst`](../../PerfectAssociation/LigoCompression.lean#L612)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L227) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.adj_snd</code></summary>

```lean
theorem adj_snd (a b c d x y : Int) :
    a * (c * x + d * y) - c * (a * x + b * y) = (a * d - b * c) * y
```

[`LigoCompression.adj_snd`](../../PerfectAssociation/LigoCompression.lean#L617)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L228) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.respond_zero</code></summary>

```lean
theorem respond_zero (F : Resp) : respond F (0, 0) = (0, 0)
```

[`LigoCompression.respond_zero`](../../PerfectAssociation/LigoCompression.lean#L622)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L229) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.respond_faithful_of_det</code></summary>

```lean
theorem respond_faithful_of_det (F : Resp) (hd : det F ≠ 0) :
    IsValidFor (respond F) (fun h => h)
```

[`LigoCompression.respond_faithful_of_det`](../../PerfectAssociation/LigoCompression.lean#L627)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L230) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.respond_kernel_of_det_zero</code></summary>

```lean
theorem respond_kernel_of_det_zero (F : Resp) (hd : det F = 0) :
    ∃ h : Int × Int, h ≠ (0, 0) ∧ respond F h = (0, 0)
```

[`LigoCompression.respond_kernel_of_det_zero`](../../PerfectAssociation/LigoCompression.lean#L641)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L231) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.network_valid_iff_det</code></summary>

```lean
theorem network_valid_iff_det (F : Resp) : IsValidFor (respond F) (fun h => h) ↔ det F ≠ 0
```

[`LigoCompression.network_valid_iff_det`](../../PerfectAssociation/LigoCompression.lean#L672)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L232) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.coaligned_det</code></summary>

```lean
theorem coaligned_det (a b : Int) : det ((a, b), (-a, -b)) = 0
```

[`LigoCompression.coaligned_det`](../../PerfectAssociation/LigoCompression.lean#L679)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L233) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.coaligned_not_valid</code></summary>

```lean
theorem coaligned_not_valid (a b : Int) :
    ¬ IsValidFor (respond ((a, b), (-a, -b))) (fun h => h)
```

[`LigoCompression.coaligned_not_valid`](../../PerfectAssociation/LigoCompression.lean#L683)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L234) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.dot_cross_left</code></summary>

```lean
theorem dot_cross_left (r s : Pol3) : dot3 r (cross3 r s) = 0
```

[`LigoCompression.dot_cross_left`](../../PerfectAssociation/LigoCompression.lean#L697)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L239) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.dot_cross_right</code></summary>

```lean
theorem dot_cross_right (r s : Pol3) : dot3 s (cross3 r s) = 0
```

[`LigoCompression.dot_cross_right`](../../PerfectAssociation/LigoCompression.lean#L703)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L240) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.dot_cross_swap</code></summary>

```lean
theorem dot_cross_swap (r s e : Pol3) : dot3 s (cross3 r e) = - dot3 e (cross3 r s)
```

[`LigoCompression.dot_cross_swap`](../../PerfectAssociation/LigoCompression.lean#L709)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L241) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.kernel_of_cross_zero</code></summary>

```lean
theorem kernel_of_cross_zero (r s e : Pol3) (h : cross3 r s = (0, 0, 0)) :
    respond3 r s (cross3 r e) = (0, 0)
```

[`LigoCompression.kernel_of_cross_zero`](../../PerfectAssociation/LigoCompression.lean#L717)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L242) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.cross_basis</code></summary>

```lean
theorem cross_basis (r : Pol3) (hr : r ≠ (0, 0, 0)) :
    cross3 r (1, 0, 0) ≠ (0, 0, 0) ∨ cross3 r (0, 1, 0) ≠ (0, 0, 0)
```

[`LigoCompression.cross_basis`](../../PerfectAssociation/LigoCompression.lean#L724)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L243) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.two_detectors_three_modes</code></summary>

```lean
theorem two_detectors_three_modes (r s : Pol3) :
    ∃ h : Pol3, h ≠ (0, 0, 0) ∧ respond3 r s h = (0, 0)
```

[`LigoCompression.two_detectors_three_modes`](../../PerfectAssociation/LigoCompression.lean#L748)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L244) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.two_detectors_invalid_for_polarization</code></summary>

```lean
theorem two_detectors_invalid_for_polarization (r s : Pol3) :
    IsInvalidFor (respond3 r s) (fun h => h)
```

[`LigoCompression.two_detectors_invalid_for_polarization`](../../PerfectAssociation/LigoCompression.lean#L773)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L245) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.centered_congr</code></summary>

```lean
theorem centered_congr (A : List Nat) (f f' g g' : Nat → Int)
    (hf : ∀ s, f s = f' s) (hg : ∀ s, g s = g' s) :
    PerfectAssociation.centered A f g = PerfectAssociation.centered A f' g'
```

[`LigoCompression.centered_congr`](../../PerfectAssociation/LigoCompression.lean#L785)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L246) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.proportional_streams_perfect</code></summary>

```lean
theorem proportional_streams_perfect (A : List Nat) (f g : Nat → Int) (k : Int) (hk : 0 < k)
    (hg : ∀ s, g s = k * f s) (hV : 0 < PerfectAssociation.spread A f) :
    PerfectAssociation.COR A f g = true
```

[`LigoCompression.proportional_streams_perfect`](../../PerfectAssociation/LigoCompression.lean#L799)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L247) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.proportional_minors_vanish</code></summary>

```lean
theorem proportional_minors_vanish (f g : Nat → Int) (k : Int) (hg : ∀ s, g s = k * f s)
    (s t u v : Nat) : (f s - f t) * (g u - g v) = (g s - g t) * (f u - f v)
```

[`LigoCompression.proportional_minors_vanish`](../../PerfectAssociation/LigoCompression.lean#L819)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L248) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.coaligned_streams</code></summary>

```lean
theorem coaligned_streams (a b k : Int) (hp hx : Nat → Int) (s : Nat) :
    (k * a) * hp s + (k * b) * hx s = k * (a * hp s + b * hx s)
```

[`LigoCompression.coaligned_streams`](../../PerfectAssociation/LigoCompression.lean#L824)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L249) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.coaligned_perfect_association</code></summary>

```lean
theorem coaligned_perfect_association (A : List Nat) (a b k : Int) (hk : 0 < k)
    (hp hx : Nat → Int) (hV : 0 < PerfectAssociation.spread A (fun s => a * hp s + b * hx s)) :
    PerfectAssociation.COR A (fun s => a * hp s + b * hx s)
      (fun s => (k * a) * hp s + (k * b) * hx s) = true
```

[`LigoCompression.coaligned_perfect_association`](../../PerfectAssociation/LigoCompression.lean#L830)

Lean lists `propext` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L250) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>

<details>
<summary><code>LigoCompression.ligo_compression_obstructions</code></summary>

```lean
theorem ligo_compression_obstructions :
    IsInvalidFor slideData zeroLag ∧
    IsInvalidFor psd (tail 5) ∧
    IsInvalidFor overall bma ∧
    (∀ xE xP xO : Int,
      IsInvalidFor (fun g : Int => sigmaSys2 (xE + g) (xP + g) (xO + g)) (fun g => g)) ∧
    (∀ (P nodes : List Int) (θ : Int), θ ∉ nodes →
      IsInvalidFor (validationView P nodes) (fun e => e.1 θ)) ∧
    (∀ r s : Pol3, IsInvalidFor (respond3 r s) (fun h => h))
```

[`LigoCompression.ligo_compression_obstructions`](../../PerfectAssociation/LigoCompression.lean#L840)

Lean lists `propext`, `Quot.sound` as axiom dependencies. [Axiom audit](../../verification/evidence/axioms.log#L251) · [Accepted checker runs](../../verification/evidence/checkers.log#L21)

</details>
