# LIGO — Formal Lean Kernel Invalidation

**Joseph M. Gerrety** 
*Measure, Error, and Information* · 23 November 2026

DISCRIPTION:

When a gravitational wave explanation and a no-gravitational wave explanation yield identical predictions and identical likelihoods for every possible dataset, LIGO cannot use those data alone to establish that a gravitational wave occurred.
Calibration and probability are based upon a condition of a reference of a previous verifiable known event. The event itself and importantly the behavior of related elements surrounding can then offer attunement of what's more likely to happen the next time. Without this transitive reference it becomes extremely difficult to establish probability of behavior.
Our theorem exposes that limitation. Every subsequent procedure using only indistinguishable information inherits this failure; establishing a gravitational wave requires evidence that separates alternatives.
We did not invent the cancellation of shared error. It's built into Ligo's comparison operation itself. Our formalization exposes that limitation and proves its persistence.

Any claim that LIGO’s model agreement alone establishes a bound on shared systematic error is mathematically unjustified. Further processing of those comparisons cannot supply the missing information. That failure belongs to the inference being claimed. 
Here taken on its own, we establish a rigorous impossibility result. An explicit pair of indistinguishable states rules out every uniformly correct recovery map for a target that distinguishes those states. The obstruction survives subsequent processing, we offer a resolution, a reference anchor that gives the precise, necessary and sufficient condition of resolution.

## Formally Proven Mathematical Invalidations

Write $\Phi$ for the observation and $R$ for the target. An invalidation supplies states $a,b$ with $\Phi(a)=\Phi(b)$ and $R(a)\ne R(b)$. A procedure using only $\Phi$ receives the same input in both cases. Consequently, every proposed reconstruction gives an incorrect answer on at least one of those states. Each result below names the observable and target to which this reasoning applies. For every theorem linked below, `con-leche` and `con-ron` accepted the export in verified mode, and `leanchecker` accepted the same export using Lean’s default kernel. [Theorem index](docs/theorem-index.md) · [Verification record](VERIFICATION.md)

### 1. Agreement between models and the magnitude of common error

For integer outputs $X=(x_1,x_2)$, define $D=x_1-x_2$ and $S=x_1+x_2$. Increasing both coordinates by $g$ leaves $D$ fixed and changes $S$ by $2g$. Thus $D=0$ is compatible with arbitrarily large positive values of $S$. No integer function $B$ can make $S(X)\le B(D(X))$ true for every $X$. More precisely, the linear target $a x_1+b x_2$ is determined by $D$ exactly when $a+b=0$. The same obstruction holds for any statistic of a finite list of pairwise differences of any positive number of model errors. [`LigoNullSpace.no_finite_bound`](PerfectAssociation/LigoNullSpace.lean#L284) · [`LigoNullSpace.linT_valid_iff`](PerfectAssociation/LigoNullSpace.lean#L238) · [`LigoCongruence.pairwise_invalid_for_common_mode_list`](PerfectAssociation/LigoCongruence.lean#L200)

The equal-weight mixture variance, the squared discrepancies of the component summaries from the pooled summary, and the inter-model mean difference are all unchanged by the same shift. The corrected order of the three summary arguments is $(x_E,x_P,x_O)$. At $(416,405,411)$, the squared-discrepancy sum is $5^2+(-6)^2=61$. At $(318,319,319)$ it is $1$. Both values remain fixed as the common error varies. [`LigoCongruence.uncertainty_triple_invalid_for_shared_error`](PerfectAssociation/LigoCongruence.lean#L320) · [`LigoCompression.tableI_m1_sigmaSys`](PerfectAssociation/LigoCompression.lean#L330) · [Derivation, Part I §19](docs/part-1.md#s19)

### 2. Recovery of a source value in the presence of a shared offset

Let $X_1=P+g+d$ and $X_2=P+g-d$. The difference determines $d$. The sum also determines $P+g$, yet $(P,g,d)$ and $(P+c,g-c,d)$ have the same pair of readings. An extra linear reference $A=\alpha P+\beta g$ separates the source $P$ and offset $g$ exactly when $\alpha\ne\beta$. Indeed, $(\alpha-\beta)P=A-\beta(P+g)$ and $(\alpha-\beta)g=\alpha(P+g)-A$. The determinant of the specified anchored Gram block is $4(\alpha-\beta)^2$. [`LigoNullSpace.information_hierarchy`](PerfectAssociation/LigoNullSpace.lean#L422) · [`LigoNullSpace.anchor_valid_iff`](PerfectAssociation/LigoNullSpace.lean#L448) · [`LigoNullSpace.fisher_anchored_det`](PerfectAssociation/LigoNullSpace.lean#L597)

For an arbitrary observable and target with decidable equality, the corresponding criterion is that the added reading separate every target-changing pair in the old fibre. For a finite suite of integer linear measurements with row matrix $M$ and target row $t$, validity is equivalent to $\ker M\subseteq\ker t$. The six-coordinate example identifies the source after the four named offsets are anchored and exhibits the direction restored by each deletion from that particular suite. [`LigoCongruence.anchor_valid`](PerfectAssociation/LigoCongruence.lean#L83) · [`LigoNullSpace.audit_exact`](PerfectAssociation/LigoNullSpace.lean#L950) · [`LigoNullSpace.each_anchor_necessary`](PerfectAssociation/LigoNullSpace.lean#L1080) · [Part I §§40–43](docs/part-1.md#s40)

Two supplementary constructions sharpen these statements. One reading of the *sum* of the four offsets, together with the total level, already determines $P$. In a separate family of eight equally weighted outcomes, the difference variance is exactly 2 for every integer $t$, while the reconstruction error has variance $t^2+1/2$. Every proposed finite upper bound on that error variance therefore fails within the family. The supplement gives Lean proofs reconstructed from the manuscript's derivations. [`VerificationCorrections.aggregate_anchor_suffices`](VerificationCorrections.lean#L47) · [`VerificationCorrections.common_error_variance_family_all`](VerificationCorrections.lean#L16) · [`VerificationCorrections.reconstruction_variance_unbounded`](VerificationCorrections.lean#L31)

### 3. Detection rules and an observationally identical alternative

The formal detection example admits $(d,\mathrm{gw})$ and $(d,\mathrm{corr})$ for the same data value $d$. Every calibration, ranking and decision computed from $d$ takes the same value on those states. A uniform decision therefore fails on at least one label. An environmental monitor in the model distinguishes the labels on the restricted class where every correlated transient couples to the monitor. Permitting an uncoupled transient supplies an explicit counterexample. An application to an event must justify that both alternatives belong to the relevant physical model and give the stipulated readings. [`LigoCongruence.detection_pipeline_blind`](PerfectAssociation/LigoCongruence.lean#L469) · [`LigoCongruence.pem_fails_on_uncoupled`](PerfectAssociation/LigoCongruence.lean#L435) · [`LigoCongruence.pem_repairs_when_coupled`](PerfectAssociation/LigoCongruence.lean#L440)

### 4. Calibration marginalization, posterior odds and the KS comparison

A likelihood of the form $L(P+g)$ is constant along $(P,g)\mapsto(P+c,g-c)$. Translating a calibration prior $\pi$ by $c$ transports the joint weight $\pi(g)L(P+g)$ along this same line. With a factorized prior on the level pair and the differential error and a finite likelihood depending on the differential error, all marginal weights of the level pair acquire the same multiplicative factor. The Lean statement uses cross-products, so it also covers zero weights. [`LigoNullSpace.calibration_marginalisation_transports_bias`](PerfectAssociation/LigoNullSpace.lean#L1259) · [`LigoNullSpace.level_posterior_odds_frozen`](PerfectAssociation/LigoNullSpace.lean#L697)

In the binary example, one prior couples $P$ to $d$ and a second prior makes them independent. The likelihood selects $d=1$ in both cases. The posterior probability of $P=1$ becomes $1$ under the first prior and stays at $1/2$ under the second. Thus the defined prior/posterior change flag is not determined by the likelihood alone. Independently, the finite KS supremum takes the same value on a discrepancy list and its sign reversal. For the specified basis-point decision $p<500$, the interval $[77,750]$ contains both verdicts. These propositions concern different statistics and specify each one explicitly. [`LigoNullSpace.ks_test_not_informativeness`](PerfectAssociation/LigoNullSpace.lean#L1273) · [`LigoSpecious.ligo_ks_phi12_verdict_split`](RequestProject/LIGO_published_ledger.lean#L229)

### 5. Effective spin, waveform coefficients and lost coordinates

In the integer-scaled model for $\chi_p$, the numerator is the maximum of two weighted in-plane terms. Neither input azimuth appears. With all other injection fields fixed, azimuths $30.9^\circ$ and $100.0^\circ$ give identical readings. Under the two stated sine bounds at the injection tilts, the secondary term dominates throughout primary amplitudes $0$ through $0.83$ on the hundredth grid. Every primary amplitude from $0.84$ changes the reading. The same bounds give $0.268093\le\chi_p\le0.268094$ at the injection. The numerical conclusions use the given bounds on the sine inputs. [`LigoSpecious.ligo_chiP_azimuth_fibre`](RequestProject/LIGO_specious_measures.lean#L528) · [`LigoSpecious.ligo_chiP_real_values`](RequestProject/LIGO_specious_measures.lean#L458) · [`LigoSpecious.ligo_chiP_primarySpin_fibre`](RequestProject/LIGO_specious_measures.lean#L584) · [`LigoSpecious.ligo_chiP_primarySpin_threshold`](RequestProject/LIGO_specious_measures.lean#L603)

For the separate phase-coefficient model $c+4\beta+\delta$, $(\beta,\delta)=(0,4)$ and $(1,0)$ give identical weighted phase functions at every input. Equal masses also permit exchanged spins to give identical readings for any body-exchange-symmetric observable. In the explicit six-to-four spin projection, the transverse components of the two bodies enter through their sums, so opposite transverse changes cancel. [`LigoCongruence.waveform_invalid_for_spin`](PerfectAssociation/LigoCongruence.lean#L149) · [`LigoCongruence.lockpoint_any_symmetric`](PerfectAssociation/LigoCongruence.lean#L375) · [`LigoSpecious.ligo_imrPhenom_spinCompression_fibre`](RequestProject/LIGO_specious_measures.lean#L1148)

### 6. Time-slide background and noise tails

In the finite count model, retaining the total number of windows and the two single-detector trigger counts discards the joint zero-lag count. With four windows and two triggers per detector, zero and two coincidences have identical retained data. Every statistic of repetitions of the defined product-marginal slide law remains identical. Under the additional restriction $N n_{11}=HL$ and $N>0$, the marginals determine $n_{11}$. These conclusions turn on exactly which information the modeled slide retains. [`LigoCompression.slides_invalid_for_zeroLag`](PerfectAssociation/LigoCompression.lean#L102) · [`LigoCompression.slides_any_statistic_invalid`](PerfectAssociation/LigoCompression.lean#L107) · [`LigoCompression.slides_valid_on_independence`](PerfectAssociation/LigoCompression.lean#L130)

The pair consisting of the total mass and second-moment numerator of a finite noise law also fails to identify its tail. The law with weight 50 at amplitude 1 and the law with weights 48 at 0 and 2 at 5 have the same mass and power, yet give tail weights 0 and 2 at threshold 5. The inequality $t^2\,\mathrm{tail}(t)\le\mathrm{power}$ still holds for every law in this class. [`LigoCompression.psd_invalid_for_tail`](PerfectAssociation/LigoCompression.lean#L224) · [`LigoCompression.chebyshev`](PerfectAssociation/LigoCompression.lean#L211)

### 7. Numerical relativity, finite calibration and extrapolation

At $k$ distinct integer calibration nodes, the values of an integer polynomial of degree less than $k$ determine its value elsewhere. Allow degree $k$ and the node polynomial $\prod_{i=1}^k(x-a_i)$ vanishes on all the nodes and is nonzero at every other integer. Adding this same polynomial to two error functions preserves both their differences and their values at the nodes. For nodes 1 through 19, its value at 20 is $19!$. The class of admissible errors thus determines what calibration on a finite set implies. [`LigoCompression.anchor_threshold`](PerfectAssociation/LigoCompression.lean#L556) · [`LigoCompression.double_blind`](PerfectAssociation/LigoCompression.lean#L577) · [`LigoCompression.nineteen_nodes`](PerfectAssociation/LigoCompression.lean#L593)

For the separately defined spin calibration region, the point $(0.84,0.54,0)$ belongs to the stated domain but lacks a preimage under the region inclusion. Injectivity and operation preservation of the inclusion therefore cannot establish exact calibration onto any range containing the point. A further result bounds the marginal mass above $0.5$ by at least 10 percent under the stated monotonicity and 90-percent quantile hypotheses. [`LigoSpecious.ligo_calibration_scope_not_exact`](RequestProject/LIGO_published_ledger.lean#L334) · [`LigoSpecious.ligo_calibration_injection_outside`](RequestProject/LIGO_published_ledger.lean#L367) · [`LigoSpecious.ligo_calibration_posterior_mass_outside`](RequestProject/LIGO_published_ledger.lean#L392)

### 8. Posterior pooling and componentwise medians

Two component allocations $(100,0,80,20)$ and $(90,10,90,10)$ give the same pooled totals $(180,20)$. The component distributions cannot be reconstructed from those totals. Equal-weight pooling likewise omits the evidence weights required for evidence-weighted model averaging. Keeping the same two component bins and changing the evidence ratio produces posterior odds $1:1$ and $1:5$. [`LigoSpecious.ligo_modelAverage_fibre`](RequestProject/LIGO_specious_measures.lean#L704) · [`LigoCompression.overall_invalid_for_bma`](PerfectAssociation/LigoCompression.lean#L258) · [`LigoCompression.bma_witness_not_rescaled`](PerfectAssociation/LigoCompression.lean#L262)

For the three specified IMRPhenom intervals, the sum of the two component mass readings is at most 7080 while the separately reported total is at least 7085, in hundredths of a solar mass. These three summaries cannot obey the proposed additive identity. Four analogous interval arguments exclude the proposed redshift identity for the indicated componentwise summaries under the stated source-relation and rounding hypotheses. The propositions concern the medians and leave the physical identities between the underlying quantities intact. [`LigoSpecious.ligo_tableI_imrphenom_median_not_additive`](RequestProject/LIGO_published_ledger.lean#L101) · [`LigoSpecious.ligo_tableI_eobnr_totalMass_not_redshift`](RequestProject/LIGO_published_ledger.lean#L151) · [All four endpoint calculations, Part II §§35–39](docs/part-2.md#s35)

### 9. Exact association, causal intervention and measurement structure

On $s=1,\ldots,20$, the functions $Q(s)=2s+3$ and $x(s)=7s-4$ have exact positive correlation. Every model $x(s)+\beta(q-Q(s))$ gives the same table at $q=Q(s)$. Intervening on $q$ changes the response precisely for $\beta\ne0$. Consequently, even the entire table fails to identify the causal answer across this family. Two labeled interventions recover $\beta$ by subtraction. Nor does an additive map fit the observed pairs: $h(5)=3$ forces $h(15)=9$ while the observations require $h(15)=38$. [`PerfectAssociation.positive_exact_certificate`](PerfectAssociation/Statistics.lean#L57) · [`PerfectAssociation.no_uniform_observational_causal_rule`](PerfectAssociation.lean#L80) · [`PerfectAssociation.intervention_recovers_parameter`](PerfectAssociation/Model.lean#L100) · [`PerfectAssociation.no_population_additive_hom`](PerfectAssociation.lean#L18)

An exact calibration in the specified signature carries a quantity kind, its operations and relations, full substitution, and a reverse reading on the calibrated range. These hypotheses yield an isomorphism with that range. For example, $(x-y,x+y)$ recovers $(x,y)$ on the integer parity range, whereas $x-y$ alone merges every diagonal pair $(g,g)$. The full treatment also exhibits the fibres of the mode projection, the integer Gaussian exponent, two-sided statistics, and fixed linear detector-response maps. [`Measure.exact_calibration_implies_isomorphic_transposition`](RequestProject/Measurement.lean#L339) · [`LigoSpecious.ligo_modelDifference_anchor_isomorphism`](RequestProject/LIGO_specious_measures.lean#L288) · [`LigoSpecious.ligo_likelihood_sign_fibre`](RequestProject/LIGO_specious_measures.lean#L943) · [`LigoCompression.network_valid_iff_det`](PerfectAssociation/LigoCompression.lean#L672) · [Theorem index](docs/theorem-index.md)

The unit example fixes what “calibrated range” means in practice. One short ton is exactly $907.18474$ kg. Rational short-ton and kilogram readings therefore admit a reversible conversion. Restrict the source to whole tons and express the target in 10 mg units, and the image becomes $90{,}718{,}474\,\mathbb Z$. Every value on that subrange has a reverse reading. The single fine unit 1 has none. [`Measure.tons_kg_isomorphic_transposition`](RequestProject/Examples.lean#L233) · [`Measure.wholeTons_isomorphic_calibrated_range`](RequestProject/Examples.lean#L365) · [`Measure.tonsToFine_not_full_calibration`](RequestProject/Examples.lean#L371)

## Full mathematical development

| Manuscript | Contents |
| --- | --- |
| [Part I · Observation, common error, and recovery](docs/part-1.md) | 46 sections. Exact witnesses, odds, finite couplings, response matrices, kernel directions, and reference anchors. |
| [Part II · Measurement structure and calibration range](docs/part-2.md) | 47 sections. Reversible calibration, integer spin certificates, posterior projections, table intervals, and the domain of the calibration map. |
| [Index of Lean theorems](docs/theorem-index.md) | Named propositions arranged by subject, with links to their source lines, proofs and verification record. |

## Independent checks and reproduction

All 16 research modules compiled with Lean 4.36.0. The four exports include 899 named public project declarations as explicit roots, including all 562 named theorems. Both independent checkers accepted all four exports with `--verified`. The Lean checker accepted the same four exports, and the axiom audit covers every named root. [Verification record, axiom audits and reproduction commands](VERIFICATION.md)

From the repository root, build the complete release with the toolchain in [`lean-toolchain`](lean-toolchain).

```sh
lake build
```

The independent exports use the public roots listed in the [declaration manifest](verification/declarations.tsv).

With the verifier tools and PowerShell prerequisites described in the verification record, re-run the export, axiom audit and all three checks.

```sh
pwsh -File verification/Run.ps1
```

## Observational reference

B. P. Abbott et al. (LIGO Scientific Collaboration and Virgo Collaboration), “Improved Analysis of GW150914 Using a Fully Spin-Precessing Waveform Model,” *Physical Review X* **6**, 041014 (2016). Table I and the specified sections provide the reported quantities used for comparison in the integer encodings. [Published article](https://doi.org/10.1103/PhysRevX.6.041014)
