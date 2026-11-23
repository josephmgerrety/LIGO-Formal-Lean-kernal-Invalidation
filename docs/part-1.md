# Observation, common error, and recovery

**Exact Measurement, Common Error, and Information Recovery · Part I**  
Joseph M. Gerrety · 23 November 2026

An observable identifies a target exactly to the extent that equal readings force equal target values. The argument begins with this definition, constructs explicit pairs with equal readings and different targets, then asks which additional measurements separate the pairs. The examples use integers, finite tables and explicitly defined response maps.

[Project and principal results](../README.md) · [Lean theorem index](theorem-index.md) · [Verification record](../VERIFICATION.md)

## Contents

**Equality, calibration and recovery**  
[1. Mathematical setting and the meaning of identification](#s01) · [2. Factorization through an observation](#s02) · [3. Why deterministic post-processing preserves an invalidity witness](#s03) · [4. Additional observations and the exact repair criterion](#s04) · [5. Equality as agreement of predicates](#s05) · [6. Equality and isomorphisms of indexed carriers](#s06) · [7. Faithful maps and substitution](#s07) · [8. Affine maps: injectivity and addition preservation](#s08) · [9. Tolerance relations and affine calibration points](#s09)

**Association and causal intervention**  
[10. Exact finite-population association](#s10) · [11. General affine covariance identities](#s11) · [12. Why the observed pairs admit no fitting additive homomorphism](#s12) · [13. An observationally identical causal family](#s13) · [14. Response-preserving maps and the common-source graph](#s14)

**Likelihood, spin and common error**  
[15. Equal likelihood factors and cross-multiplied odds](#s15) · [16. The modeled phase coefficient and its exact fibre](#s16) · [17. Symmetric masses and exchanged spins](#s17) · [18. Common shifts in suites of model errors](#s18) · [19. Mixture variance and common-shift summaries](#s19) · [20. Reference-relative error and calibration-distance fibres](#s20) · [21. A finite prior calculation on an exact likelihood fibre](#s21)

**Coincidence, background and extrapolation**  
[22. Marginal counts and joint coincidence](#s22) · [23. The supplied count and time scales](#s23) · [24. Second moments and discrete tails](#s24) · [25. Evidence weighting and posterior summaries](#s25) · [26. Finite polynomial anchors](#s26) · [27. Fixed linear-response maps](#s27)

**Null spaces, anchors and uncertainty**  
[28. Sum, difference, and common-direction decomposition](#s28) · [29. Complete fibres of the difference and the linear-target classification](#s29) · [30. No uniform bound or bounded-error reconstruction from the difference](#s30) · [31. Source value, common error, and differential error](#s31) · [32. The exact anchor criterion](#s32) · [33. The Gram-form calculation and anchored determinant](#s33) · [34. Equal difference-channel laws and equal test weights](#s34) · [35. Factorized prior mass and unchanged level odds](#s35) · [36. Prior coupling and the posterior-prior comparison flag](#s36) · [37. Calibration-prior transport](#s37) · [38. Common error and the eight-outcome variance family](#s38) · [39. Unbounded reconstruction variance with fixed difference moments](#s39)

**Validation suites and statistical summaries**  
[40. Six-coordinate validation suites](#s40) · [41. The exact kernel criterion for linear targets](#s41) · [42. Dedicated offset anchors and their exact role](#s42) · [43. Recovery from one aggregate offset anchor](#s43) · [44. The exact encoded common-offset witness](#s44) · [45. Two-sided statistics, effect size, squared norms, and direction](#s45) · [46. Assembly of the Part 1 conclusions](#s46)

<a name="s01" id="s01"></a>

## 1. Mathematical setting and the meaning of identification

[`LigoCongruence.invalid_not_valid`](../PerfectAssociation/LigoCongruence.lean#L22) · [`LigoCongruence.valid_iff_not_invalid`](../PerfectAssociation/LigoCongruence.lean#L27)

The development works with explicitly defined types, functions, operations, relations, finite lists, integer encodings, and proof terms.

Write Int for the integers and Nat for the natural numbers.

Let

```text
Phi : A → B
```

be an observation map, and let

```text
R : A → C
```

be the target quantity.

Define the equality kernel of Phi by

```text
Ker Phi a b  ↔  Phi(a) = Phi(b).
```

Define validity for the target R by

```text
IsValidFor Phi R
↔
for every a,b : A,
Phi(a) = Phi(b) implies R(a) = R(b).
```

Thus validity says that the target is constant on every observation fibre.

Define an explicit invalidity certificate by

```text
IsInvalidFor Phi R
↔
there exist a,b : A such that
Phi(a) = Phi(b) and R(a) ≠ R(b).
```

The two states a and b, the equality of their observations, and the inequality of their targets constitute the witness.

Proof that invalidity contradicts validity:

Suppose validity and an invalidity witness both hold. Apply validity to the witness equality Phi(a)=Phi(b). It gives R(a)=R(b), contradicting the supplied inequality R(a)≠R(b).

With decidable equality on the target, absence of an invalidity witness also implies validity.

Indeed, take a,b with equal observations. Decide whether R(a)=R(b). The equality case supplies the required conclusion. In the inequality case, a,b would constitute the excluded invalidity witness.

This establishes the formal connection between valid recovery and the absence of a witnessed collision for the target.

<a name="s02" id="s02"></a>

## 2. Factorization through an observation

[`LigoCongruence.invalid_no_factor`](../PerfectAssociation/LigoCongruence.lean#L39) · [`LigoCongruence.valid_iff_factor`](../PerfectAssociation/LigoCongruence.lean#L50)

Suppose there is a function

```text
w : B → C
```

such that

```text
R(a) = w(Phi(a))
```

for every a.

Then Phi is valid for R.

Proof:

If Phi(a)=Phi(b), applying w gives

```text
w(Phi(a)) = w(Phi(b)).
```

Substituting the factorization equations gives R(a)=R(b).

An explicit invalidity witness therefore excludes every such factorization.

For the converse construction, suppose validity is given together with an explicit right inverse

```text
s : B → A
```

satisfying

```text
Phi(s(b)) = b
```

for every b.

Define

```text
w(b) = R(s(b)).
```

For any a, the right-inverse equation gives

```text
Phi(s(Phi(a))) = Phi(a).
```

Validity now gives

```text
R(s(Phi(a))) = R(a).
```

Consequently,

```text
w(Phi(a)) = R(a).
```

The factor is constructed directly from the supplied right inverse.

<a name="s03" id="s03"></a>

## 3. Why deterministic post-processing preserves an invalidity witness

[`LigoCongruence.invalid_postcompose`](../PerfectAssociation/LigoCongruence.lean#L62) · [`LigoCongruence.chain_blind`](../PerfectAssociation/LigoCongruence.lean#L68) · [`LigoCongruence.every_procedure_errs`](../PerfectAssociation/LigoCongruence.lean#L456)

Suppose

```text
Phi(a) = Phi(b),
R(a) ≠ R(b).
```

For every function h on the observation space,

```text
h(Phi(a)) = h(Phi(b)).
```

The target inequality is unchanged. Therefore

```text
IsInvalidFor Phi R
```

implies

```text
IsInvalidFor (h composed with Phi) R.
```

The same argument applies repeatedly to any finite chain of deterministic post-processing functions.

A closely related statement concerns a proposed decision or reconstruction rule

```text
rule : B → C.
```

It is impossible for both equations

```text
rule(Phi(a)) = R(a),
rule(Phi(b)) = R(b)
```

to hold on an invalidity witness.

If both held, equality of the rule inputs would imply equality of the rule outputs, and hence R(a)=R(b), a contradiction.

This proof applies to every rule of the specified type.

<a name="s04" id="s04"></a>

## 4. Additional observations and the exact repair criterion

[`LigoCongruence.ker_pair`](../PerfectAssociation/LigoCongruence.lean#L76) · [`LigoCongruence.anchor_valid`](../PerfectAssociation/LigoCongruence.lean#L83)

Let Aobs be an additional observation.

The paired observation is

```text
a ↦ (Phi(a), Aobs(a)).
```

Two states have equal paired observations exactly when both of the following hold:

```text
Phi(a) = Phi(b),
Aobs(a) = Aobs(b).
```

Therefore the kernel of the paired observation is the intersection of the two individual kernels.

With decidable equality on the target, the paired observation is valid for R exactly when the additional observation separates every pair satisfying

```text
Phi(a) = Phi(b),
R(a) ≠ R(b).
```

Proof of necessity:

If such a pair also had Aobs(a)=Aobs(b), its paired observations would be equal. Validity would force R(a)=R(b), contradicting the target inequality.

Proof of sufficiency:

Take equal paired observations. If the targets differed, the separation condition would force unequal Aobs values, contradicting the second coordinate of the paired-observation equality.

Thus the additional observation restores identification precisely by separating the relevant merged states.

<a name="s05" id="s05"></a>

## 5. Equality as agreement of predicates

[`EqualityBridge.eq_iff_same`](../PerfectAssociation/EqualityBridge.lean#L21) · [`EqualityBridge.eq_iff_indiscernible`](../PerfectAssociation/EqualityBridge.lean#L24) · [`Sameness.eq_iff_same_values`](../RequestProject/Equality.lean#L39)

For a,b in a type alpha, define

```text
Same(a,b)
↔
for every predicate P : alpha → Prop,
P(a) implies P(b).
```

Then

```text
a=b  ↔  Same(a,b).
```

Forward proof:

Equality permits substitution in every predicate. A proof of P(a) therefore becomes a proof of P(b).

Reverse proof:

Choose the predicate

```text
P(x) := a=x.
```

Its value at a is proved by reflexivity. Same(a,b) therefore supplies a proof of a=b.

It follows that a=b is equivalent to agreement of all predicate truth values at a and b.

Equality is also equivalent to equality of all function values, with the codomain universe quantified as in the Lean statement.

The forward implication is congruence: functions preserve equality.

For the reverse implication, instantiate the quantified function with the identity function on alpha.

Reflexivity, symmetry, and transitivity follow from equality elimination and substitution. These are proofs about equality itself.

<a name="s06" id="s06"></a>

## 6. Equality and isomorphisms of indexed carriers

[`EqualityBridge.eq_iff_forall_iso`](../PerfectAssociation/EqualityBridge.lean#L94) · [`EqualityBridge.selected_iso_does_not_entail_equality`](../PerfectAssociation/EqualityBridge.lean#L114)

An isomorphism Iso A B contains:

```text
toFun : A → B,
invFun : B → A,
```

with equations

```text
invFun(toFun(a)) = a,
toFun(invFun(b)) = b.
```

Its forward map is injective.

If toFun(a)=toFun(a'), apply invFun and use the left-inverse equations to obtain a=a'.

Its forward map is surjective.

For a given b, the explicit preimage is invFun(b), and the right-inverse equation proves that its image is b.

An equality a=b transports every indexed family F from F(a) to F(b). Eliminating the equality reduces this transport to the identity map, so the inverse equations follow by reflexivity.

Conversely, suppose that for every family

```text
F : alpha → Type v
```

there exists an isomorphism between F(a) and F(b).

Use the particular family

```text
F(x) = ULift(PLift(a=x)).
```

The carrier F(a) contains the element recording the reflexive equality a=a. An isomorphism sends this element to F(b). Unpacking the two lifts produces a proof of a=b.

Hence the checked equivalence is

```text
a=b
↔
for every F : alpha → Type v,
Nonempty(Iso(F(a),F(b))).
```

The universal quantifier over families is part of the proposition.

The development also gives a concrete distinction between this condition and an isomorphism of one selected carrier. The constant Bool family has isomorphic carriers at 0 and 1, although 0≠1.

<a name="s07" id="s07"></a>

## 7. Faithful maps and substitution

[`LigoCalibration.faithful_characterisation`](../PerfectAssociation/LigoCalibration.lean#L65) · [`LigoCalibration.faithful_comp`](../PerfectAssociation/LigoCalibration.lean#L103) · [`LigoCalibration.carriers_gap`](../PerfectAssociation/LigoCalibration.lean#L138)

A map C is called faithful when it is injective:

```text
C(a)=C(b) implies a=b.
```

Faithfulness implies that every source predicate can be substituted through an equality of calibrated readings.

If C(a)=C(b), faithfulness gives a=b, and equality substitution transfers every predicate from a to b.

Conversely, suppose equal calibrated readings permit substitution of every source predicate. Choose P(x):=a=x. The reflexive proof at a then transfers to a proof of a=b.

Thus this predicate-substitution property is equivalent to faithfulness.

The development also defines a condition Chains C requiring that

```text
C(a)=C(b) and C(b)=C(c)
```

imply a=c.

A faithful map satisfies this condition by transitivity of the two image equalities followed by injectivity.

Conversely, apply Chains C to

```text
C(a)=C(b),
C(b)=C(b)
```

to derive a=b.

Faithfulness is also equivalent to validity for the identity target.

A faithful observation is valid for every target, since equal observations first give equal source states and then equal target values.

Faithful maps compose. Explicit isomorphisms are faithful. A collision between distinct source states remains a collision after every post-processing map.

Combining faithfulness with the all-family isomorphism criterion gives the corresponding calibrated-carrier characterization of source equality.

<a name="s08" id="s08"></a>

## 8. Affine maps: injectivity and addition preservation

[`LigoCalibration.affine_faithful_iff`](../PerfectAssociation/LigoCalibration.lean#L175) · [`AssociationAlgebra.affine_hom_iff`](../PerfectAssociation/Algebra.lean#L93) · [`AssociationAlgebra.affine_defect`](../PerfectAssociation/Algebra.lean#L85)

For a,b,z : Int, define

```text
Affine(a,b,z) = a z + b.
```

The exact injectivity classification is

```text
Affine(a,b,·) is injective  ↔  a≠0.
```

If a≠0 and

```text
a x+b = a y+b,
```

cancel b, then cancel the nonzero integer factor a, obtaining x=y.

If a=0, the map is constant with value b. In particular, it maps 0 and 1 to the same value, so it is not injective.

The exact addition-preservation classification is

```text
Affine(a,b,·) preserves addition  ↔  b=0.
```

For necessity, apply addition preservation to 0 and 0. The resulting equation is

```text
b = b+b.
```

Integer cancellation gives b=0.

For sufficiency, set b=0 and use distributivity:

```text
a(u+v) = au+av.
```

The additive defect is

```text
Affine(a,b,u+v)
  - (Affine(a,b,u)+Affine(a,b,v))

= a(u+v)+b - (au+b+av+b)

= -b.
```

Thus the four parameter pairs

```text
(a,b)=(1,0),
(a,b)=(1,1),
(a,b)=(0,0),
(a,b)=(0,1)
```

realize all four combinations of injectivity and addition preservation.

For the shifted target operation

```text
shiftedAdd(b,u,v) = u+v-b,
```

every affine map satisfies

```text
Affine(a,b,u+v)
=
shiftedAdd(b,Affine(a,b,u),Affine(a,b,v)).
```

Both sides expand to au+av+b.

Affine maps compose by

```text
Affine(a2,b2,Affine(a1,b1,z))
=
Affine(a2 a1, a2 b1+b2, z).
```

Translation by c has inverse translation by -c. When c≠0, its additive defect is -c, so it does not preserve ordinary addition.

The unit-gain, unit-offset certificate gives

```text
Affine(1,1,2) = 3,
Affine(1,1,2+2) = 5,
Affine(1,1,2)+Affine(1,1,2) = 6.
```

The defect is exactly -1.

<a name="s09" id="s09"></a>

## 9. Tolerance relations and affine calibration points

[`LigoCalibration.within_not_a_kernel`](../PerfectAssociation/LigoCalibration.lean#L275) · [`LigoCalibration.one_anchor_invalid_for_gain`](../PerfectAssociation/LigoCalibration.lean#L298) · [`LigoCalibration.zero_unit_anchors_valid`](../PerfectAssociation/LigoCalibration.lean#L326)

For natural numbers, define

```text
Within(epsilon,a,b)
↔
a ≤ b+epsilon and b ≤ a+epsilon.
```

Reflexivity follows from a≤a+epsilon. Symmetry exchanges the two inequalities.

For epsilon>0, consider

```text
0, epsilon, 2 epsilon.
```

The first two are within epsilon, as are the last two. However, 0 and 2 epsilon are not within epsilon, since that would require

```text
2 epsilon ≤ epsilon,
```

contradicting epsilon>0.

Therefore Within epsilon is not transitive when epsilon>0.

Every equality kernel of a function is transitive. Consequently, Within epsilon cannot be such a kernel when epsilon>0.

The supplied scale certificate records

```text
1000000000000000
=
500000000000000 × 2,
```

together with

```text
Within(1,0,1),
Within(1,1,2),
not Within(1,0,2).
```

For affine calibration, one reading at a known input u does not identify the gain.

The parameter pairs

```text
(a,b)=(0,0),
(a,b)=(1,-u)
```

both give reading 0 at u, while their gains differ.

If u≠0, their offsets also differ, proving the corresponding offset non-identification.

At input 0, the reading is exactly b, so it identifies the offset.

At inputs 0 and 1, the readings are

```text
r0=b,
r1=a+b.
```

Thus

```text
b=r0,
a=r1-r0.
```

Equal readings at these two inputs force equal gains and offsets.

<a name="s10" id="s10"></a>

## 10. Exact finite-population association

[`PerfectAssociation.exact_moments`](../PerfectAssociation/Statistics.lean#L36) · [`PerfectAssociation.positive_exact_certificate`](../PerfectAssociation/Statistics.lean#L57)

Take the population

```text
A=[1,2,3,...,20]
```

and define

```text
S(s)=s,
Q(s)=2s+3,
x(s)=7s-4.
```

For a finite population of size n, define

```text
centered(A,f,g)
=
n sum(fg) - sum(f) sum(g),
```

and

```text
spread(A,f)
=
centered(A,f,f).
```

The exact base sums are

```text
n=20,
sum(S)=210,
sum(S²)=2870.
```

Therefore

```text
spread(A,S)
=
20×2870 - 210²
=
13300.
```

The affine sums are

```text
sum(Q)
= 2×210 + 3×20
= 480,

sum(Q²)
= 4×2870 + 12×210 + 9×20
= 14180,

sum(x)
= 7×210 - 4×20
= 1390,

sum(x²)
= 49×2870 - 56×210 + 16×20
= 129190.
```

Since

```text
(2s+3)(7s-4)=14s²+13s-12,
```

the mixed sum is

```text
sum(Qx)
= 14×2870 + 13×210 - 12×20
= 42670.
```

Consequently,

```text
spread(A,Q)
= 20×14180 - 480²
= 53200,

spread(A,x)
= 20×129190 - 1390²
= 651700,

centered(A,Q,x)
= 20×42670 - 480×1390
= 186200.
```

All three quantities are positive. Their exact identity is

```text
186200²
=
34670440000
=
53200×651700.
```

These are the four conjuncts of

```text
PerfectAssociation.positive_exact_certificate.
```

The defined positive-correlation certificate COR therefore evaluates to true.

<a name="s11" id="s11"></a>

## 11. General affine covariance identities

[`PerfectAssociation.centered_affine`](../PerfectAssociation/Statistics.lean#L184) · [`PerfectAssociation.spread_affine`](../PerfectAssociation/Statistics.lean#L192) · [`PerfectAssociation.perfect_correlation_population`](../PerfectAssociation/Statistics.lean#L217)

Let f,g be integer streams on an arbitrary finite population.

Adding constants to either stream does not change its centered contribution, because the constant terms cancel between

```text
n sum(fg)
```

and

```text
sum(f) sum(g).
```

For integer slopes a,c and offsets b,d, expansion gives

```text
centered(A, a f+b, c g+d)
=
a c centered(A,f,g).
```

Taking both streams equal gives

```text
spread(A, a f+b)
=
a² spread(A,f).
```

These identities follow by distributivity and the finite-sum rules for addition, multiplication by a constant, and constant streams.

For Q=2S+3 and x=7S-4, they give

```text
centered(A,Q,x)=14 spread(A,S),

spread(A,Q)=4 spread(A,S),

spread(A,x)=49 spread(A,S).
```

Whenever spread(A,S)>0, the resulting spreads and centered cross-product are positive, and

```text
centered(A,Q,x)²
=
spread(A,Q) spread(A,x).
```

Thus the defined positive-correlation certificate holds on every such population.

The observational line and pairwise differences are exact:

```text
2x(s)=7Q(s)-29,

Q(s)-Q(t)=2(s-t),

x(s)-x(t)=7(s-t).
```

These also force the corresponding two-by-two difference determinants to vanish.

<a name="s12" id="s12"></a>

## 12. Why the observed pairs admit no fitting additive homomorphism

[`PerfectAssociation.no_population_additive_hom`](../PerfectAssociation.lean#L18) · [`PerfectAssociation.no_population_additive_iso`](../PerfectAssociation.lean#L29) · [`AssociationAlgebra.int_add_not_isomorphic_int_mul`](../PerfectAssociation/Algebra.lean#L177)

Suppose h : Int → Int preserves addition and fits every observed pair.

At source index 1,

```text
Q(1)=5,
x(1)=3,
```

so fitting requires

```text
h(5)=3.
```

At source index 6,

```text
Q(6)=15,
x(6)=38,
```

so fitting requires

```text
h(15)=38.
```

But additivity gives

```text
h(15)
= h(5+5+5)
= h(5)+h(5)+h(5)
= 3+3+3
= 9.
```

This contradicts 38≠9.

Therefore no additive homomorphism fits the population. An additive isomorphism would supply such a homomorphism, so no additive isomorphism fits it either.

The development additionally proves that the additive and multiplicative integer magmas are not isomorphic.

For a direct proof, suppose an operation-preserving bijection f from integer addition to integer multiplication existed. Choose k with f(k)=0 using its inverse. Then, for every x,

```text
f(k+x)=f(k)f(x)=0=f(k).
```

Injectivity would give k+x=k for every x, and hence x=0 for every x. Taking x=1 is a contradiction.

<a name="s13" id="s13"></a>

## 13. An observationally identical causal family

[`PerfectAssociation.tables_independent`](../PerfectAssociation/Model.lean#L44) · [`PerfectAssociation.causation_iff_nonzero`](../PerfectAssociation/Model.lean#L75) · [`PerfectAssociation.no_uniform_observational_causal_rule`](../PerfectAssociation.lean#L80) · [`PerfectAssociation.intervention_recovers_parameter`](../PerfectAssociation/Model.lean#L100)

Define

```text
response(beta,s,q)
=
x(s) + beta(q-Q(s)).
```

At the observed input q=Q(s),

```text
response(beta,s,Q(s))
=
x(s)+beta×0
=
x(s).
```

Therefore every beta has the same observations

```text
(Q(s),x(s))
```

and the same finite observational tables.

Define CausesQX(beta) to mean that some intervention on q changes the response while s is held fixed.

If beta=0, the response equals x(s) for every q. Thus CausesQX(0) is false.

If beta≠0, choose s=0 and interventions q=3 and q=4.

Since Q(0)=3 and x(0)=-4,

```text
response(beta,0,3)=-4,

response(beta,0,4)=-4+beta.
```

These values are different exactly when beta≠0.

Hence

```text
CausesQX(beta)  ↔  beta≠0.
```

The intervention difference also gives the explicit reconstruction

```text
response(beta,0,4)-response(beta,0,3)=beta.
```

Thus two labelled interventions identify beta.

No Boolean rule using only the observational table can correctly decide CausesQX for both beta=0 and beta=1.

Those two tables are equal, so the rule must return the same value on both. The causal properties differ, so both answers cannot be correct.

<a name="s14" id="s14"></a>

## 14. Response-preserving maps and the common-source graph

[`PerfectAssociation.no_response_hom_to_effect`](../PerfectAssociation/Model.lean#L162) · [`PerfectAssociation.reverse_response_hom`](../PerfectAssociation/Model.lean#L149) · [`PerfectAssociation.no_causal_path`](../PerfectAssociation/Model.lean#L210)

A response-preserving map from beta to gamma keeps the source and intervention labels fixed and satisfies

```text
h(s,response(beta,s,q))
=
response(gamma,s,q).
```

There is no such map from beta=0 to beta=1.

At s=1, the beta=0 response is 3 for both q=5 and q=6.

The beta=1 responses at those interventions are respectively 3 and 4.

Preservation would therefore require

```text
h(1,3)=3,
h(1,3)=4,
```

a contradiction.

An isomorphism in either direction would include a forbidden response-preserving map from 0 to 1, so neither response isomorphism exists.

The reverse homomorphism does exist:

```text
collapse(s,y)=x(s).
```

It sends every outcome to the baseline response and preserves responses from beta=1 to beta=0.

More generally, response-preserving maps transport intervention invariance. If the source response is constant in q, applying a fixed outcome map keeps it constant. Consequently, no response-preserving map from beta=0 to a nonzero beta can exist.

The explicitly defined common-source graph has arrows

```text
source → q,
source → x,
```

and no outgoing arrow from q.

Every causal path from q would need an initial outgoing edge from q. No such edge exists, so no such path exists in that graph.

<a name="s15" id="s15"></a>

## 15. Equal likelihood factors and cross-multiplied odds

[`LigoCongruence.posterior_odds_frozen`](../PerfectAssociation/LigoCongruence.lean#L97) · [`LigoCongruence.within_class_prior_echo_norm`](../PerfectAssociation/LigoCongruence.lean#L108)

Define

```text
SameRatio(a,b,c,d)  ↔  a d = c b.
```

For arbitrary integer weights pi1, pi2 and ell,

```text
SameRatio(pi1 ell, pi2 ell, pi1, pi2)
```

holds because

```text
(pi1 ell)pi2
=
pi1(pi2 ell).
```

Both sides are the same product after associativity and commutativity.

Multiplication by a further common integer factor preserves the same cross-multiplied identity.

For within-pair conditional weights, the corresponding identity follows from

```text
pi1 ell (pi1+pi2)
=
pi1 ((pi1 ell)+(pi2 ell)).
```

These identities do not divide by a weight or a normalizer.

When the weights represent probabilities and the relevant normalizers are nonzero, they yield the corresponding normalized ratio statements.

<a name="s16" id="s16"></a>

## 16. The modeled phase coefficient and its exact fibre

[`LigoCongruence.psi15_eq_iff`](../PerfectAssociation/LigoCongruence.lean#L134) · [`LigoCongruence.waveform_invalid_for_spin`](../PerfectAssociation/LigoCongruence.lean#L149) · [`LigoCongruence.spin_triangle`](../PerfectAssociation/LigoCongruence.lean#L334)

Define

```text
psi15(c,beta,delta)=c+4beta+delta.
```

For every integer t,

```text
psi15(c,beta+t,delta-4t)
=
c+4beta+4t+delta-4t
=
psi15(c,beta,delta).
```

Two coefficients are equal exactly when their values of

```text
4beta+delta
```

are equal.

In particular,

```text
psi15(c,beta,4k)
=
psi15(c,beta+k,0).
```

Define the weighted phase function by

```text
phase15(pref,c,(beta,delta))(w)
=
pref psi15(c,beta,delta) w.
```

Applying the function

```text
z ↦ (w ↦ pref z w)
```

to an equality of coefficients gives equality of the entire phase functions.

Take the two states

```text
(beta,delta)=(0,4),
(beta,delta)=(1,0).
```

Their coefficients both equal c+4. Their phase functions are therefore equal for every pref and c. Their beta coordinates are 0 and 1.

This is the explicit invalidity witness for the beta coordinate.

Any likelihood depending on these states only through the equal modeled output also takes equal values on the witness pair.

For coefficient errors delta+d and delta-d,

```text
[psi15(c,beta,delta+d)-c]
  - [psi15(c,beta,delta-d)-c]
=
2d,
```

whereas

```text
[psi15(c,beta,delta+d)-c]
  + [psi15(c,beta,delta-d)-c]
  - 8beta
=
2delta.
```

Thus the difference removes the common coefficient error.

If the coefficient equations are written as 4 betaHat, averaging the two equations gives an average betaHat bias of delta/4 in a domain permitting that division.

<a name="s17" id="s17"></a>

## 17. Symmetric masses and exchanged spins

[`LigoCongruence.eta_invalid_for_q`](../PerfectAssociation/LigoCongruence.lean#L277) · [`LigoCongruence.lockpoint_any_symmetric`](../PerfectAssociation/LigoCongruence.lean#L375) · [`LigoCongruence.gw150914_attribution_weight`](../PerfectAssociation/LigoCongruence.lean#L405)

The symmetric mass observation is

```text
(m1,m2) ↦ (m1+m2,m1m2).
```

It gives the same result on

```text
(2,1),
(1,2),
```

while their first labelled mass coordinates differ.

Therefore the symmetric observation is invalid for that labelled coordinate on the stated integer domain.

For all integer masses,

```text
4m1m2
=
(m1+m2)²-(m1-m2)².
```

Proof:

Expand both squares. Their m1² and m2² terms cancel, while the two mixed terms contribute 4m1m2.

At fixed total M, changing a difference Delta to Delta+e changes

```text
M²-Delta²
```

by

```text
[M²-Delta²]-[M²-(Delta+e)²]
=
2Delta e+e²
=
e(2Delta+e).
```

At Delta=0 this is e².

The numerical certificates are

```text
712²-62²-(712²-72²)=1340,

4×387×325=503100,

(387-325)²=3844.
```

For any observable invariant under exchanging two bodies, the equal-mass states

```text
((a,x),(a,y)),
((a,y),(a,x))
```

have equal observations.

If x≠y, their first labelled spins differ.

For the effective-spin numerator

```text
effNum(a,b,x,y)=ax+by,
```

the exchange difference is

```text
effNum(a,b,x,y)-effNum(a,b,y,x)
=
ax+by-ay-bx
=
(a-b)(x-y).
```

At masses 387 and 325, exchanging spins 10 and 0 changes the numerator by

```text
(387-325)×10=620.
```

Changing both spins from 0 to 10 changes it by

```text
(387+325)×10=7120.
```

<a name="s18" id="s18"></a>

## 18. Common shifts in suites of model errors

[`LigoCongruence.pairwise_invalid_for_common_mode_list`](../PerfectAssociation/LigoCongruence.lean#L200) · [`LigoCongruence.pairwise_invalid_for_common_mode`](../PerfectAssociation/LigoCongruence.lean#L215) · [`LigoNullSpace.two_hundred_thousand_channels_blind`](../PerfectAssociation/LigoNullSpace.lean#L842)

Let epsilon : Nat → Int be a model-error function.

For every common integer shift g and every i,j,

```text
(epsilon(i)+g)-(epsilon(j)+g)
=
epsilon(i)-epsilon(j).
```

Therefore every finite list of pairwise differences is unchanged by the common shift.

Every deterministic statistic of that list is unchanged as well.

For a statistic whose input is the entire function table of pairwise differences, the corresponding theorem retains its supplied extensionality hypothesis: pointwise equal tables must give equal statistic values.

For every N>0, these observations are invalid for the sum of the first N errors.

Take the constant-zero error function and the constant-one error function.

Every pairwise difference is zero for both functions. Therefore every specified difference-list statistic has equal values on them.

The target sums are

```text
0
```

and

```text
N,
```

which differ because N>0.

The argument applies to any positive number of channels, including the explicit 200000-channel instance.

<a name="s19" id="s19"></a>

## 19. Mixture variance and common-shift summaries

[`LigoCongruence.mixVar4_from_moments`](../PerfectAssociation/LigoCongruence.lean#L250) · [`LigoCompression.tableI_m1_sigmaSys`](../PerfectAssociation/LigoCompression.lean#L330) · [`LigoCompression.sigmaSys_samples_invalid`](../PerfectAssociation/LigoCompression.lean#L318)

Define

```text
mixVar4(m1,m2,v1,v2)
=
2(v1+v2)+(m1-m2)².
```

A common shift b of m1 and m2 leaves their difference unchanged:

```text
(m1+b)-(m2+b)=m1-m2.
```

Hence mixVar4 is invariant under that shift.

When m1,m2 are component means and v1,v2 their variances, the equal-weight mixture variance V satisfies the denominator-cleared identity

```text
4V=2(v1+v2)+(m1-m2)².
```

To derive this, write the mixture second moment as

```text
(v1+m1²+v2+m2²)/2
```

and the mixture mean as

```text
(m1+m2)/2.
```

Subtract the squared mean and multiply by 4. The remaining mean terms are

```text
2m1²+2m2²-(m1+m2)²
=
(m1-m2)².
```

At the supplied values,

```text
mixVar4(22,32,529,529)
=
2(529+529)+(22-32)²
=
2116+100
=
2216.
```

The universal common-shift identity proves the same value after every integer common shift.

Both saved squared-difference definitions use the argument order

```text
(xE,xP,xO).
```

They are

```text
LigoCongruence.sysVar2(xE,xP,xO)
=
(xE-xO)²+(xP-xO)²,
```

and

```text
LigoCompression.sigmaSys2(xE,xP,xO)
=
(xE-xO)²+(xP-xO)².
```

A common shift of all three arguments cancels from both differences. Therefore both functions are invariant under that shift.

The exact evaluations are

```text
sysVar2(416,405,411)
=
sigmaSys2(416,405,411)
=
(416-411)²+(405-411)²
=
5²+(-6)²
=
61,
```

and

```text
sysVar2(318,319,319)
=
sigmaSys2(318,319,319)
=
(318-319)²+(319-319)²
=
(-1)²+0²
=
1.
```

The stored squared rounding inequalities are

```text
85²×200 < 164²×61 < 95²×200,

5²×200 < 164²×1 < 15²×200.
```

Their exact numerical forms are

```text
1445000 < 1640656 < 1805000,

5000 < 26896 < 45000.
```

Thus the positive quantities

```text
1.64 sqrt(61/2)
```

and

```text
1.64 sqrt(1/2)
```

lie strictly inside

```text
(8.5,9.5)
```

and

```text
(0.5,1.5),
```

respectively.

A summary Q is shift-equivariant on nonempty lists when

```text
Q(map (x ↦ x+g) L)=Q(L)+g
```

for every nonempty L and every integer g.

Apply this property to two nonempty sample lists and to their concatenation. Their three summary values all increase by g, so sigmaSys2 is unchanged.

The first-sample summary satisfies the stated shift-equivariance property directly.

Taking common shifts 0 and 1 gives equal summary observations and different shift parameters. This supplies the explicit invalidity witness for the common shift.

The combined observation consisting of the displayed variance summaries and the inter-model mean difference has the same common-shift invariance.

<a name="s20" id="s20"></a>

## 20. Reference-relative error and calibration-distance fibres

[`LigoAnchors.calibration_distance_fibre`](../PerfectAssociation/LigoAnchors.lean#L44) · [`LigoAnchors.reference_shift_invisible`](../PerfectAssociation/LigoAnchors.lean#L157) · [`LigoAnchors.anchor_identifies`](../PerfectAssociation/LigoAnchors.lean#L162)

Define the integer log-amplitude model by

```text
logAmp(kappa,delta)=kappa-delta.
```

Then

```text
logAmp(kappa+c,delta+c)
=
kappa+c-delta-c
=
logAmp(kappa,delta).
```

This gives its exact common-shift fibre.

Define reference-relative error by

```text
err(meas,ref)=meas-ref.
```

For two measurements and a shared reference shift,

```text
err(m1,r+c)-err(m2,r+c)
=
m1-r-c-m2+r+c
=
m1-m2.
```

The same value is obtained without the shift.

For fixed meas and truth, suppose

```text
err(meas,truth+c)
=
err(meas,truth+c').
```

Cancel meas, truth, and the signs in the two expressions. The result is

```text
c=c'.
```

Thus the stated external-reference reading identifies the offset.

<a name="s21" id="s21"></a>

## 21. A finite prior calculation on an exact likelihood fibre

[`LigoAnchors.same_data_different_beta`](../PerfectAssociation/LigoAnchors.lean#L134) · [`LigoAnchors.fibre_prior_echo`](../PerfectAssociation/LigoAnchors.lean#L142)

Define a likelihood on integers by

```text
lik(psi)=1 if psi=1, and 0 otherwise.
```

The observed combination is

```text
psi=beta+ell.
```

Sum ell over [0,1] and beta over [0,1,2].

First use the prior concentrated at ell=0.

The only contributing state is

```text
beta=1, ell=0.
```

Therefore

```text
mass(beta=1)=1,
total mass=1.
```

The normalized mass at beta=1 is 1.

Now give equal prior weight to the two summed ell values.

The contributing states are

```text
beta=1, ell=0,
beta=0, ell=1.
```

Therefore

```text
mass(beta=1)=1,
total mass=2.
```

The normalized mass at beta=1 is 1/2.

The likelihood is the same in both calculations.

For the general fibre identity, define

```text
post(prior,L,u,b,ell)
=
prior(b,ell) L(b+ell u).
```

Suppose

```text
b+ell u = b'+ell' u.
```

Then the likelihood factor is equal on the two states. Associativity and commutativity give

```text
post(b,ell) prior(b',ell')
=
post(b',ell') prior(b,ell).
```

This is the exact cross-multiplied posterior identity.

<a name="s22" id="s22"></a>

## 22. Marginal counts and joint coincidence

[`LigoCompression.slides_invalid_for_zeroLag`](../PerfectAssociation/LigoCompression.lean#L102) · [`LigoCompression.slides_valid_on_independence`](../PerfectAssociation/LigoCompression.lean#L130) · [`LigoCompression.slide_estimate_not_a_bound`](../PerfectAssociation/LigoCompression.lean#L156)

A coupling consists of four natural counts

```text
(n00,n01,n10,n11).
```

Define

```text
N=n00+n01+n10+n11,

H=n10+n11,

L=n01+n11.
```

The retained observation is

```text
slideData=(N,H,L),
```

and the joint target is

```text
zeroLag=n11.
```

The following bounds hold:

```text
n11≤H,
n11≤L,
H+L≤N+n11.
```

The first two follow because the omitted summands are nonnegative.

For the third,

```text
H+L=n10+n01+2n11,
```

whereas

```text
N+n11=n00+n01+n10+2n11.
```

The latter differs from the former by n00≥0.

The observation slideData together with n11 determines the full coupling.

Equality of n11 and H gives equality of n10 by cancellation. Equality of n11 and L gives equality of n01. Equality of N then gives equality of n00.

For a redistribution parameter t that keeps all counts nonnegative, replace the four counts by

```text
(n00+t, n01-t, n10-t, n11+t).
```

The total and both marginals remain unchanged.

A fixed invalidity witness is

```text
(0,2,2,0),
(2,0,0,2).
```

Both have

```text
slideData=(4,2,2),
```

but their joint counts are 0 and 2.

Consequently, the defined product-law representation of the marginals, any finite repetition of it, and every statistic of that repetition remain invalid for the joint count.

On the restricted subtype satisfying

```text
N n11 = H L
```

and N>0, the marginal data do determine n11.

If two such couplings have equal N,H,L, their restriction equations give

```text
N n11 = N n11'.
```

Cancel the positive, hence nonzero, factor N to obtain n11=n11'.

The unrestricted counterexamples also show that H L/N is neither a universal upper bound nor a universal lower bound for the joint count.

<a name="s23" id="s23"></a>

## 23. The supplied count and time scales

[`LigoCompression.gw150914_frechet_scale`](../PerfectAssociation/LigoCompression.lean#L174) · [`LigoCompression.gw150914_slide_ledger`](../PerfectAssociation/LigoCompression.lean#L181)

At

```text
N=92160000,
H=L=16,
```

the two valid couplings

```text
(92159968,16,16,0),

(92159984,0,0,16)
```

have the same N,H,L.

Their joint counts are respectively 0 and 16.

At the second endpoint,

```text
N n11
=
92160000×16
=
1474560000,
```

while

```text
H L=256.
```

Therefore

```text
N n11 = 5760000 H L.
```

The time arithmetic is

```text
16×86400=1382400 seconds,

1382400/0.1=13824000 ticks,

1382400×13824000
=
19110297600000 seconds.
```

Natural-number division gives

```text
19110297600000 / 31557600 = 605568,
```

and the separately supplied quotient is

```text
608000 / 3 = 202666.
```

A cyclic grid with 13824000 ticks has 13824000 offsets when zero is included and 13823999 nonzero offsets.

<a name="s24" id="s24"></a>

## 24. Second moments and discrete tails

[`LigoCompression.psd_invalid_for_tail`](../PerfectAssociation/LigoCompression.lean#L224) · [`LigoCompression.chebyshev_interval_5p1`](../PerfectAssociation/LigoCompression.lean#L229) · [`LigoCompression.tail_max_5p1`](../PerfectAssociation/LigoCompression.lean#L235)

A NoiseLaw is a finite list of pairs

```text
(a,w)
```

with a,w : Nat.

Define

```text
mass = sum w,

power = sum w a²,

tail(t) = sum of w over entries satisfying t≤a.
```

For every threshold t and every such list,

```text
t² tail(t) ≤ power.
```

Proof by induction on the list:

For the empty list, both sides are zero.

For a head entry (a,w), split on whether t≤a.

If t≤a, then t²≤a², and multiplication by w≥0 gives

```text
t²w≤a²w=wa².
```

If t≤a is false, the head contributes zero to the tail, and

```text
0≤wa².
```

Add this head inequality to the induction hypothesis for the remaining list.

The pair (mass,power) does not identify the tail.

The laws

```text
[(1,50)]
```

and

```text
[(0,48),(5,2)]
```

both have mass 50 and power 50.

At threshold 5, their tail weights are 0 and 2.

At threshold 51, use

```text
L1=[(10,2601)],

L2=[(0,2501),(51,100)].
```

Their masses are both 2601.

Their powers are

```text
2601×10²=260100,

2501×0²+100×51²=260100.
```

Their tail weights at 51 are 0 and 100.

The second law attains the bound:

```text
51²×100
=
2601×100
=
260100.
```

For every law with power 260100, the universal inequality gives

```text
2601 tail(51)≤260100,
```

and hence

```text
tail(51)≤100.
```

When the mass is 2601, the displayed normalized endpoint tails are 0 and 100/2601.

<a name="s25" id="s25"></a>

## 25. Evidence weighting and posterior summaries

[`LigoCompression.overall_invalid_for_bma`](../PerfectAssociation/LigoCompression.lean#L258) · [`LigoCompression.bma_shift`](../PerfectAssociation/LigoCompression.lean#L268) · [`LigoCompression.gw150914_m1_bma_shift`](../PerfectAssociation/LigoCompression.lean#L274)

Let two component posterior pairs be given, together with evidence weights zE and zP.

The defined unweighted overall combination adds the corresponding posterior entries.

The evidence-weighted combination multiplies the component entries by their respective evidence weights before adding.

Take component pairs

```text
(1,0),
(0,1).
```

Evidence weights

```text
(1,1)
```

and

```text
(1,5)
```

leave the unweighted combination equal to (1,1), but give weighted combinations

```text
(1,1),
(1,5).
```

These pairs are not proportional: the required cross-product equality would be 5=1.

For component values mE,mP, the exact identity is

```text
2(zE mE+zP mP)
  -(zE+zP)(mE+mP)

=
zE mE+zP mP-zE mP-zP mE

=
(zP-zE)(mP-mE).
```

At

```text
zE=1,
zP=5,
mE=363,
mP=353,
```

the value is

```text
(5-1)(353-363)
=
4×(-10)
=
-40.
```

When mE,mP are component means and the corresponding normalizers are nonzero, this is the denominator-cleared comparison of the weighted and equal-weighted means.

<a name="s26" id="s26"></a>

## 26. Finite polynomial anchors

[`LigoCompression.anchor_threshold`](../PerfectAssociation/LigoCompression.lean#L556) · [`LigoCompression.double_blind`](../PerfectAssociation/LigoCompression.lean#L577) · [`LigoCompression.nineteen_nodes`](../PerfectAssociation/LigoCompression.lean#L593)

Represent an integer polynomial by a finite coefficient list, evaluated by Horner evaluation.

A list of length at most k represents the polynomial class used in the k-anchor validity theorem.

Let nodes be a list of k distinct integers.

Suppose a polynomial r in this class vanishes at every node.

We prove that r vanishes at every integer argument.

For k=0, its coefficient list has length zero, so r is the zero polynomial.

For a nonempty node list a::rest, synthetic division gives

```text
r(x)=r(a)+(x-a)q(x),
```

where the quotient q has at most one fewer coefficient.

Since r(a)=0,

```text
r(x)=(x-a)q(x).
```

At another node b,

```text
0=r(b)=(b-a)q(b).
```

Distinctness gives b-a≠0. Integer cancellation therefore gives q(b)=0.

The induction hypothesis applies to q and rest, so q vanishes everywhere. The displayed factorization then proves that r vanishes everywhere.

Now take two polynomials p,q with at most k coefficients and equal readings at all nodes.

Their coefficientwise difference has at most k coefficients and vanishes at every node. The result just proved gives

```text
p(theta)-q(theta)=0
```

at every theta.

Thus the node readings determine every evaluation in this class.

For the next coefficient bound, define the node polynomial

```text
nodePoly(x)=product over a in nodes of (x-a).
```

It has at most k+1 coefficients and vanishes at every node.

If theta is outside the node list, every factor theta-a is nonzero. A finite product of nonzero integers is nonzero, so nodePoly(theta)≠0.

Therefore the zero polynomial and nodePoly give an explicit invalidity witness for evaluation at theta when k+1 coefficients are allowed.

Without restricting the function class, use the zero function and the function equal to 1 at theta and 0 elsewhere. They agree at every node and differ at theta.

Adding the same node polynomial to two model-error functions leaves every inter-model difference and every listed node reading unchanged.

For nodes 1 through 19,

```text
nodePoly(7)=0,
```

and

```text
nodePoly(20)
=
19!
=
121645100408832000.
```

<a name="s27" id="s27"></a>

## 27. Fixed linear-response maps

[`LigoCompression.network_valid_iff_det`](../PerfectAssociation/LigoCompression.lean#L672) · [`LigoCompression.two_detectors_invalid_for_polarization`](../PerfectAssociation/LigoCompression.lean#L773) · [`LigoCompression.coaligned_perfect_association`](../PerfectAssociation/LigoCompression.lean#L830)

For the integer matrix

```text
M = [[a,b],
     [c,d]],
```

define

```text
det(M)=ad-bc.
```

If Mx=My, let v=x-y. Then Mv=0.

Eliminating one coordinate from the two equations gives

```text
det(M) v1=0,
det(M) v2=0.
```

If det(M)≠0, integer cancellation yields v1=v2=0, so x=y.

Conversely, if det(M)=0, an explicit nonzero kernel vector exists.

If the first row is nonzero, use

```text
v=(b,-a).
```

Its first row reading is zero, and its second is

```text
cb-da=-det(M)=0.
```

If the first row is zero and the second is nonzero, use

```text
v=(d,-c).
```

If both rows are zero, use

```text
v=(1,0).
```

Hence

```text
M is injective  ↔  det(M)≠0.
```

Rows (a,b) and (-a,-b) have determinant zero.

For two integer rows of length three, their cross product is orthogonal to both rows.

If that cross product is nonzero, it is the required nonzero kernel vector.

If the cross product is zero, the vanishing minors permit explicit alternatives.

For a row (a,b,c) with (a,b)≠(0,0), the vector

```text
(b,-a,0)
```

is nonzero, orthogonal to that row, and orthogonal to the other row by the corresponding vanishing minor.

If a=b=0 and c≠0, the zero cross product forces the first two coordinates of the other row to vanish, and (1,0,0) is a common kernel vector.

If the first row is zero, apply the same construction to the other row. If both are zero, use (1,0,0).

Therefore every such two-by-three integer response has a nonzero kernel vector and fails to identify an unrestricted three-coordinate input.

For proportional finite streams g=kf,

```text
centered(f,g)=k spread(f),

spread(g)=k² spread(f).
```

If k>0 and spread(f)>0, these identities prove the defined positive correlation certificate.

The proportionality also makes every corresponding two-by-two difference minor zero.

<a name="s28" id="s28"></a>

## 28. Sum, difference, and common-direction decomposition

[`LigoNullSpace.sd_inverse`](../PerfectAssociation/LigoNullSpace.lean#L73) · [`LigoNullSpace.projector_resolution`](../PerfectAssociation/LigoNullSpace.lean#L198) · [`LigoNullSpace.projector_squares`](../PerfectAssociation/LigoNullSpace.lean#L205)

For X=(x1,x2), define

```text
S(X)=x1+x2,

D(X)=x1-x2.
```

The transformation laws are

```text
D(x1+g,x2+g)=D(x1,x2),

S(x1+g,x2+g)=S(x1,x2)+2g.
```

The sum-difference matrix

```text
[[1,1],
 [1,-1]]
```

has determinant -2.

Its inverse identities, expressed without integer division, are

```text
S+D=2x1,

S-D=2x2.
```

Therefore equal S and D values force equal input pairs.

Define the twice-scaled common and differential maps by

```text
C(x1,x2)=(x1+x2,x1+x2),

M(x1,x2)=(x1-x2,x2-x1).
```

Direct substitution gives

```text
C(X)+M(X)=2X,

C(C(X))=2C(X),

M(M(X))=2M(X),

M(C(X))=(0,0),

C(M(X))=(0,0).
```

In particular,

```text
M(c,c)=(0,0)
```

for every common level c.

<a name="s29" id="s29"></a>

## 29. Complete fibres of the difference and the linear-target classification

[`LigoNullSpace.difC_fibre`](../PerfectAssociation/LigoNullSpace.lean#L95) · [`LigoNullSpace.linT_valid_iff`](../PerfectAssociation/LigoNullSpace.lean#L238)

The full fibre characterization is

```text
D(x1,x2)=D(y1,y2)
```

if and only if there exists an integer g such that

```text
y1=x1+g,
y2=x2+g.
```

For the forward direction, choose

```text
g=y1-x1.
```

The first equation is immediate.

The equal-difference equation rearranges to

```text
y2=x2+y1-x1=x2+g.
```

The reverse direction follows by cancelling the common shift.

In particular,

```text
D(x1,x2)=0  ↔  x1=x2.
```

For a,b : Int, define the linear target

```text
T(x1,x2)=a x1+b x2.
```

Then

```text
IsValidFor D T  ↔  a+b=0.
```

Necessity:

The states (0,0) and (1,1) have equal differences.

Validity would give equality of their target values:

```text
0=a+b.
```

Sufficiency:

If a+b=0, then b=-a, and

```text
T(x1,x2)=a(x1-x2)=aD(x1,x2).
```

The target factors through D, so it is valid.

This classifies every linear target of the stated form.

<a name="s30" id="s30"></a>

## 30. No uniform bound or bounded-error reconstruction from the difference

[`LigoNullSpace.no_finite_bound`](../PerfectAssociation/LigoNullSpace.lean#L284) · [`LigoNullSpace.difference_estimator_unbounded`](../PerfectAssociation/LigoNullSpace.lean#L304)

There is no integer-valued function B of D satisfying

```text
S(X)≤B(D(X))
```

for every integer pair X.

To prove this, start with any proposed B and write

```text
m=B(0).
```

If m≥0, take

```text
X=(m+1,m+1).
```

Then

```text
D(X)=0,

S(X)=2m+2>m=B(D(X)).
```

If m<0, take X=(0,0). Then

```text
D(X)=0,

S(X)=0>m=B(D(X)).
```

Every proposed B therefore has an explicit counterexample.

The estimator statement is also explicit.

For every f : Int → Int and every K : Int, there exists X with D(X)=0 such that

```text
K≤f(D(X))-S(X)
```

or

```text
K≤S(X)-f(D(X)).
```

If K≤f(0), use X=(0,0), which satisfies the first inequality.

Otherwise f(0)<K. Use X=(K,K). Then

```text
S(X)-f(D(X))
=
2K-f(0)
>
K,
```

which supplies the second inequality.

The related error-splitting identity says that for any e,S1,S2,

```text
S2-S1≤2(e-S1)
```

or

```text
S2-S1≤2(S2-e).
```

If the first inequality fails, rearranging its strict reverse proves the second.

<a name="s31" id="s31"></a>

## 31. Source value, common error, and differential error

[`LigoNullSpace.information_hierarchy`](../PerfectAssociation/LigoNullSpace.lean#L422) · [`LigoNullSpace.obsSD_orbit`](../PerfectAssociation/LigoNullSpace.lean#L397)

Let

```text
theta=(P,g,d)
```

and define

```text
X1=P+g+d,

X2=P+g-d.
```

Then

```text
D=2d,

S=2(P+g).
```

The difference identifies d because multiplication by 2 is injective on the integers.

It does not identify P, g, or P+g.

Explicit witness pairs are

```text
(P,g,d)=(0,0,0) and (1,0,0)
```

for P and P+g, and

```text
(P,g,d)=(0,0,0) and (0,1,0)
```

for g.

Both witnesses keep D=0.

The paired observation (S,D) identifies d and P+g.

Equality of the two observations gives

```text
2d=2d',

2(P+g)=2(P'+g').
```

Cancelling 2 gives equality of d and of the combined level.

The transformation

```text
(P,g,d) ↦ (P+c,g-c,d)
```

preserves both observations.

In particular,

```text
(0,0,0),
(1,-1,0)
```

have the same (S,D)=(0,0), but different P and different g.

These identities, validities, and invalidity witnesses are combined in LigoNullSpace.information_hierarchy.

<a name="s32" id="s32"></a>

## 32. The exact anchor criterion

[`LigoNullSpace.anchor_valid_iff`](../PerfectAssociation/LigoNullSpace.lean#L448) · [`LigoNullSpace.anchor_inversion`](../PerfectAssociation/LigoNullSpace.lean#L475)

Suppose the combined level

```text
L=P+g
```

is observed, together with the linear anchor

```text
A=alpha P+beta g.
```

Then the pair (L,A) identifies (P,g) exactly when

```text
alpha≠beta.
```

The reconstruction identities are

```text
(alpha-beta)P=A-beta L,

(alpha-beta)g=alpha L-A.
```

If two states have equal L and A, these equations give equal multiples of their P and g coordinates.

When alpha-beta≠0, integer cancellation proves equality of both coordinates.

For necessity, let alpha=beta.

The distinct states

```text
(P,g)=(0,0),
(P,g)=(1,-1)
```

both have L=0 and A=0.

Thus the observation is not injective in this case.

The exact checked statement is

```text
IsValidFor (levelAnchor alpha beta) identity
↔
alpha≠beta.
```

<a name="s33" id="s33"></a>

## 33. The Gram-form calculation and anchored determinant

[`LigoNullSpace.fisher_null`](../PerfectAssociation/LigoNullSpace.lean#L532) · [`LigoNullSpace.fisher_anchored_det`](../PerfectAssociation/LigoNullSpace.lean#L597)

For a finite list of integer rows, define

```text
I_rows(u,v)
=
sum over r in rows of (r·u)(r·v).
```

If every row annihilates v, then every summand contains the zero factor r·v. Hence

```text
I_rows(u,v)=0
```

for every u.

For the difference row

```text
rowD=(0,0,2),
```

the P and g diagonal entries are zero, and the d diagonal entry is 4.

Add the sum row

```text
rowS=(2,2,0).
```

The P,g block becomes

```text
[[4,4],
 [4,4]],
```

whose determinant is zero.

Add the anchor row

```text
rowA=(alpha,beta,0).
```

The P,g block is then

```text
[[4+alpha², 4+alpha beta],
 [4+alpha beta, 4+beta²]].
```

Its determinant is

```text
(4+alpha²)(4+beta²)-(4+alpha beta)²

=
16+4alpha²+4beta²+alpha²beta²
  -16-8alpha beta-alpha²beta²

=
4(alpha²-2alpha beta+beta²)

=
4(alpha-beta)².
```

This determinant is zero exactly when alpha=beta.

If alpha=beta, substitution gives zero.

Conversely, if 4(alpha-beta)²=0, cancellation of 4 gives a zero square. An integer square can be zero only when its base is zero. Thus alpha=beta.

The determinant identity and the anchor-identification equivalence are assembled in LigoNullSpace.fisher_anchored_det for the defined Gram form.

<a name="s34" id="s34"></a>

## 34. Equal difference-channel laws and equal test weights

[`LigoNullSpace.d_channel_tests_blind`](../PerfectAssociation/LigoNullSpace.lean#L657) · [`LigoNullSpace.tvNum_of_pointwise`](../PerfectAssociation/LigoNullSpace.lean#L632) · [`LigoNullSpace.acceptMass_congr`](../PerfectAssociation/LigoNullSpace.lean#L647)

Let

```text
noise : Int → Nat
```

be arbitrary, and define

```text
lawD(theta,y)=noise(y-D(theta)).
```

Since D(theta)=2d,

```text
lawD(theta,y)=noise(y-2d).
```

The expression is independent of P and g.

Therefore states with the same d have equal weights at every y.

The encoded levels 4 am and 400 nm differ by the factor

```text
100000000000,
```

but have identical difference-channel weights when d is held fixed.

For a finite outcome list, the defined total-variation numerator sums the absolute differences of the two weights.

Pointwise equality makes every summand zero, so the numerator is zero.

For any Boolean test, accepted mass is the sum of the weights at accepted outcomes.

Pointwise equality also makes these accepted masses equal.

Both finite-list claims follow by recursion: the empty-list values agree, and equality of the head weights combines with the induction hypothesis.

<a name="s35" id="s35"></a>

## 35. Factorized prior mass and unchanged level odds

[`LigoNullSpace.postPG_factor`](../PerfectAssociation/LigoNullSpace.lean#L689) · [`LigoNullSpace.level_posterior_odds_frozen`](../PerfectAssociation/LigoNullSpace.lean#L697)

Let

```text
piPG : Int×Int → Nat,

pid : Int → Nat,

lik : Int → Int → Nat,
```

and let ds be a finite list of differential-error values.

For an observed y, define

```text
postPG(p)
=
sum over d in ds of
piPG(p) pid(d) lik(y,d).
```

The factor piPG(p) does not depend on d, so

```text
postPG(p)=piPG(p) C,
```

where

```text
C=sum over d in ds of pid(d) lik(y,d).
```

The finite-sum factorization is proved recursively.

For the empty list, both sides are zero.

For a head d and tail ds, apply the induction hypothesis and distributivity:

```text
c f(d)+c sum_ds(f)
=
c(f(d)+sum_ds(f)).
```

For every p,q,

```text
postPG(p) piPG(q)
=
piPG(p) C piPG(q)

=
piPG(q) C piPG(p)

=
postPG(q) piPG(p).
```

This is LigoNullSpace.level_posterior_odds_frozen.

It holds for arbitrary natural weights and finite lists, including zero weights and empty lists.

When the relevant denominators and normalizing mass are nonzero, the cross-multiplied equality yields equality of the corresponding divided odds.

<a name="s36" id="s36"></a>

## 36. Prior coupling and the posterior-prior comparison flag

[`LigoNullSpace.prior_coupling_moves_blind_coordinate`](../PerfectAssociation/LigoNullSpace.lean#L729) · [`LigoNullSpace.ks_flag_not_function_of_likelihood`](../PerfectAssociation/LigoNullSpace.lean#L750)

Take P,d in {0,1} and a likelihood that is 1 exactly when d=1.

First use a prior that gives weight 1 exactly when P=d.

Before conditioning, P=0 and P=1 each have mass 1, so the prior probability of P=1 is 1/2.

After multiplying by the likelihood, only

```text
(P,d)=(1,1)
```

remains.

Thus the posterior probability of P=1 is 1.

Now use a flat prior on the four states.

Before conditioning, both P values have equal mass 2.

After conditioning on d=1, both P values have equal mass 1.

The probability of P=1 remains 1/2.

The likelihood is identical in these two constructions and depends only on d.

The source defines a Boolean flag by a cross-multiplied comparison of the prior and posterior mass at P=0.

It is true for the tied prior and false for the flat prior.

The two configurations therefore give an explicit invalidity witness for recovering that flag from the likelihood alone.

<a name="s37" id="s37"></a>

## 37. Calibration-prior transport

[`LigoNullSpace.calibration_prior_transport`](../PerfectAssociation/LigoNullSpace.lean#L766) · [`LigoNullSpace.hanford_transport`](../PerfectAssociation/LigoNullSpace.lean#L777)

Define the joint weight

```text
W_pi(P,g)=pi(g)L(P+g),
```

with pi,L : Int → Nat.

For an integer c, shift the calibration prior by

```text
pi_c(t)=pi(t-c).
```

Then

```text
W_pi_c(P,g)
=
pi(g-c)L(P+g).
```

On the other hand,

```text
W_pi(P+c,g-c)
=
pi(g-c)L((P+c)+(g-c))

=
pi(g-c)L(P+g).
```

Hence, for every c,P,g,

```text
W_pi_c(P,g)=W_pi(P+c,g-c).
```

The proof is a pointwise equality of the defined weights.

For the encoded numerical witness,

```text
rStar=3969245147706565,

am=1000000000000000,

c=100 am=100000000000000000.
```

Then

```text
rStar-c=-96030754852293435,
```

and

```text
(rStar-c)+c=rStar.
```

A point prior at calibration offset 0, together with a likelihood selecting the level rStar, gives weight 1 at (P,g)=(rStar,0).

The prior shifted to calibration offset c gives weight 1 at

```text
(P,g)=(-96030754852293435,100000000000000000)
```

and weight 0 at the former point (rStar,0).

These are the exact finite point-mass evaluations in hanford_transport.

<a name="s38" id="s38"></a>

## 38. Common error and the eight-outcome variance family

[`LigoNullSpace.common_error_variance_family`](../PerfectAssociation/LigoNullSpace.lean#L824) · [`VerificationCorrections.common_error_variance_family_all`](../VerificationCorrections.lean#L16) The supplementary declaration is a reconstruction from the manuscript. Its provenance and checker coverage are documented in the [verification record](../VERIFICATION.md).

For arbitrary integers P,g,e1,e2, set

```text
X1=P+g+e1,

X2=P+g+e2.
```

Then

```text
D=X1-X2=e1-e2,
```

and

```text
S-2P=2g+e1+e2.
```

For every integer t, take the eight samples

```text
(t, 1, 1),
(t, 1,-1),
(t,-1, 1),
(t,-1,-1),

(-t, 1, 1),
(-t, 1,-1),
(-t,-1, 1),
(-t,-1,-1).
```

For a sample (g,e1,e2), define

```text
D=e1-e2,

Z=2g+e1+e2.
```

The eight D values are

```text
[0,2,-2,0,0,2,-2,0].
```

Therefore

```text
sum D=0,

sum D²=16.
```

The eight Z values are

```text
[2t+2,2t,2t,2t-2,
 -2t+2,-2t,-2t,-2t-2].
```

Their sum is zero by pairing opposite linear terms and cancelling the constant terms.

Put z=2t. Their squared sum is

```text
2((z+2)²+(z-2)²)+4z².
```

Using

```text
(x+y)²+(x-y)²=2x²+2y²,
```

this becomes

```text
2(2z²+8)+4z²

=8z²+16

=32t²+16.
```

Thus, for every t : Int,

```text
momD1(samples(t))=0,

momD2(samples(t))=16,

momR1(samples(t))=0,

momR2(samples(t))=32t²+16.
```

These four universal identities are proved in

```text
VerificationCorrections.common_error_variance_family_all.
```

The original finite-range certificate is retained. The separately named supplement proves the identities for every integer t.

With equal probability 1/8 on the eight outcomes and reconstruction error E=Z/2, the zero means give

```text
Var(D)=16/8=2,

Var(E)=(32t²+16)/(8×4)=t²+1/2.
```

<a name="s39" id="s39"></a>

## 39. Unbounded reconstruction variance with fixed difference moments

[`VerificationCorrections.reconstruction_variance_unbounded`](../VerificationCorrections.lean#L31) The supplementary declaration is a reconstruction from the manuscript. Its provenance and checker coverage are documented in the [verification record](../VERIFICATION.md).

For every K : Nat, choose the explicit integer

```text
t=K+1.
```

Then

```text
0≤t,
1≤t,
K<t.
```

Multiplying 1≤t by the nonnegative t gives

```text
t≤t².
```

Hence

```text
K<t².
```

Multiplication by 32 and addition of 16 give

```text
32K<32t²+16.
```

The universal moment identity now yields

```text
32K<momR2(samples(t)).
```

At the same t,

```text
momD1=0,
momD2=16,
momR1=0.
```

This is the existential certificate in

```text
VerificationCorrections.reconstruction_variance_unbounded.
```

Under the equal-weight interpretation just stated,

```text
Var(E)>K
```

while

```text
Var(D)=2.
```

<a name="s40" id="s40"></a>

## 40. Six-coordinate validation suites

[`LigoNullSpace.measure_shift`](../PerfectAssociation/LigoNullSpace.lean#L937) · [`LigoNullSpace.audit_invalid`](../PerfectAssociation/LigoNullSpace.lean#L944)

The latent integer state is

```text
theta=(P,gCal,gTime,gAct,gSens,d).
```

A Row consists of six integer coefficients.

Its evaluation is the dot product

```text
ev(row,theta).
```

A finite suite returns the list of row evaluations.

Define InKernel(suite,v) to mean that every row in the suite evaluates to zero on v.

Linearity gives

```text
ev(row,theta+v)
=
ev(row,theta)+ev(row,v),
```

and

```text
ev(row,theta-theta')
=
ev(row,theta)-ev(row,theta').
```

If v is in the suite kernel, then

```text
measureSuite(suite,theta+v)
=
measureSuite(suite,theta).
```

Therefore, whenever a target T satisfies

```text
T(theta+v)≠T(theta),
```

the states theta+v and theta are an explicit invalidity witness.

This applies to arbitrary targets of the stated type.

<a name="s41" id="s41"></a>

## 41. The exact kernel criterion for linear targets

[`LigoNullSpace.audit_exact`](../PerfectAssociation/LigoNullSpace.lean#L950) · [`LigoNullSpace.kernel_extend`](../PerfectAssociation/LigoNullSpace.lean#L972)

For every finite suite and every target row t,

```text
IsValidFor(measureSuite(suite),ev(t))
↔
for every v,
InKernel(suite,v) implies ev(t,v)=0.
```

Forward proof:

Assume validity and take a suite-kernel vector v.

Every row evaluates to zero on v and on the zero latent state. Thus those two states have equal suite observations.

Validity gives

```text
ev(t,v)=ev(t,0)=0.
```

Reverse proof:

Assume every suite-kernel vector is annihilated by the target row.

Take theta,theta' with equal suite observations, and set

```text
v=theta-theta'.
```

For every suite row r, equal readings and linearity give

```text
ev(r,v)
=
ev(r,theta)-ev(r,theta')
=
0.
```

Thus v is in the suite kernel. The hypothesis yields

```text
ev(t,v)=0.
```

Linearity then gives

```text
ev(t,theta)-ev(t,theta')=0,
```

so the target readings are equal.

This is LigoNullSpace.audit_exact.

In matrix notation, the same statement is

```text
ker(M) is contained in ker(t).
```

Duplicating or reordering existing rows leaves the relevant kernel obstruction in place.

Adding further rows also leaves a particular obstruction in place when those added rows annihilate the same witness direction.

<a name="s42" id="s42"></a>

## 42. Dedicated offset anchors and their exact role

[`LigoNullSpace.level_suite_invalid`](../PerfectAssociation/LigoNullSpace.lean#L1048) · [`LigoNullSpace.anchored_suite_valid_for_P`](../PerfectAssociation/LigoNullSpace.lean#L1061) · [`LigoNullSpace.each_anchor_necessary`](../PerfectAssociation/LigoNullSpace.lean#L1080)

Use the rows

```text
rowDiff=(0,0,0,0,0,2),

rowSum=(2,2,2,2,2,0),

rowP=(1,0,0,0,0,0).
```

The four dedicated anchors read the four offsets individually.

The suite consisting of rowDiff alone is invalid for P and for each offset.

The suite consisting of rowDiff and rowSum is also invalid for P.

For example, the direction

```text
vCal=(1,-1,0,0,0,0)
```

has zero difference reading and zero sum reading, but changes P by 1.

The analogous directions are

```text
vTime=(1,0,-1,0,0,0),

vAct=(1,0,0,-1,0,0),

vSens=(1,0,0,0,-1,0).
```

The suite containing rowDiff, rowSum, and all four dedicated offset anchors does identify P.

For a kernel vector of that suite, each anchored offset is zero.

The sum equation then reduces to

```text
2P=0,
```

which implies P=0.

The exact kernel criterion therefore proves validity for P.

Within this specified suite, deleting the calibration anchor reopens vCal. Deleting the timing anchor reopens vTime. Deleting the actuation anchor reopens vAct. Deleting the sensing anchor reopens vSens.

Each deletion consequently has an explicit invalidity witness for P.

Every finite repetition of rowDiff remains invalid for P, because the same P-changing direction is annihilated by every repeated row.

<a name="s43" id="s43"></a>

## 43. Recovery from one aggregate offset anchor

[`VerificationCorrections.aggregate_anchor_suffices`](../VerificationCorrections.lean#L47) The supplementary declaration is a reconstruction from the manuscript. Its provenance and checker coverage are documented in the [verification record](../VERIFICATION.md).

Define the aggregate offset row by

```text
aggregateOffset=(0,1,1,1,1,0).
```

It reads

```text
Aagg=gCal+gTime+gAct+gSens.
```

The sum row satisfies

```text
S=2(P+Aagg).
```

Equivalently,

```text
2P=S-2Aagg.
```

Suppose two states have equal sum readings and equal aggregate-offset readings.

Then

```text
2(P+Aagg)=2(P'+Aagg'),
```

and

```text
Aagg=Aagg'.
```

Cancel 2, substitute the equal aggregate offsets, and cancel the common offset. The result is P=P'.

Therefore

```text
IsValidFor
  (measureSuite [rowSum,aggregateOffset])
  (ev rowP).
```

This is the separately checked theorem

```text
VerificationCorrections.aggregate_anchor_suffices.
```

Its target is the source coordinate P.

<a name="s44" id="s44"></a>

## 44. The exact encoded common-offset witness

[`LigoNullSpace.hanford_suite_witness`](../PerfectAssociation/LigoNullSpace.lean#L1104) · [`LigoNullSpace.hanford_levels_merged`](../PerfectAssociation/LigoNullSpace.lean#L174)

The integer encoding uses units of 10^(-33) metres.

The fixed value is

```text
rStar=3969245147706565.
```

For the state with P=rStar and every offset zero, the difference-and-sum suite reads

```text
[0,7938490295413130].
```

Now change the source and calibration offset to

```text
P=-96030754852293435,

gCal=100000000000000000,
```

with all other offsets and d equal to zero.

Their sum is still rStar, so the suite gives exactly the same readings

```text
[0,7938490295413130].
```

The source coordinates differ.

The additional encoded value is

```text
rStarBig
=
rStar×100000000000

=
396924514770656500000000000.
```

The states with source rStar and zero offset, and with source rStar-rStarBig and calibration offset rStarBig, also have identical suite readings.

For the equal-pair observations,

```text
(rStar,rStar),

(rStarBig,rStarBig),
```

the differences are both zero, while the sums differ.

These are closed integer witnesses.

<a name="s45" id="s45"></a>

## 45. Two-sided statistics, effect size, squared norms, and direction

[`LigoNullSpace.twoSided_invalid_for_direction`](../PerfectAssociation/LigoNullSpace.lean#L1122) · [`LigoNullSpace.zstat_invalid_for_effect`](../PerfectAssociation/LigoNullSpace.lean#L1146) · [`LigoNullSpace.ks_invalid_for_direction`](../PerfectAssociation/LigoNullSpace.lean#L1203)

For any function f on natural numbers, define

```text
twoSided(f,z)=f(abs(z)).
```

The integers 2 and -2 have the same absolute value. Therefore every such two-sided statistic takes equal values on them.

Their directions are respectively 1 and -1.

Thus every statistic of this form is invalid for direction.

Applying a significance threshold is deterministic post-processing, so it preserves the same invalidity witness.

For the defined integer ratio statistic,

```text
zStat(effect,scale)=effect/scale,
```

the two inputs

```text
(200,100),

(2,1)
```

both give 2.

Their absolute effects are 200 and 2. Hence this statistic is invalid for the named absolute-effect target.

For the squared norm

```text
chi2(a,b)=a²+b²,
```

the distinct pairs

```text
(1,-1),

(-1,1)
```

have the same value 2.

Negating either coordinate or exchanging coordinates also preserves the squared norm.

For the finite-list statistic ksSup, the value is the maximum absolute entry, with the specified empty-list base case.

Negating every entry preserves each absolute value, so induction on the list proves

```text
ksSup(map negation xs)=ksSup(xs).
```

The lists

```text
[3,1],

[-3,-1]
```

have the same maximum absolute entry, while their leading entries are 3 and -3.

They are an explicit invalidity witness for the leading-direction target.

<a name="s46" id="s46"></a>

## 46. Assembly of the Part 1 conclusions

[`LigoNullSpace.ligo_null_space_invalidation`](../PerfectAssociation/LigoNullSpace.lean#L1297)

The source constructs the combined theorem LigoNullSpace.ligo_null_space_invalidation from the previously proved components.

Its conclusions include:

```text
The difference is invalid for the sum.

No integer-valued function of the difference uniformly bounds the sum.

A linear target a x1+b x2 is valid for the difference exactly when
a+b=0.

In the model X1=P+g+d and X2=P+g-d, the paired sum and difference
determine P+g and d, while explicit fibres preserve the observations
and change P or g.

The additional anchor alpha P+beta g identifies the level pair exactly
when alpha≠beta.

The determinant of the defined anchored Gram block is
4(alpha-beta)².

Difference-channel weights are independent of the common level for
the stated noise-weight construction.

Under the stated factorized prior, finite posterior level masses
differ from their prior masses by a common factor.

Calibration-prior translation satisfies the proved pointwise
transport identity.

The defined posterior-prior comparison flag is not determined by the
likelihood alone in the explicit finite prior example.

A suite is invalid for any target changed by a supplied direction in
the suite kernel.

A suite determines a linear target exactly when its kernel is
contained in the target kernel.

The specified dedicated-anchor suite determines P, with explicit
counterexamples for each of the four listed anchor deletions.
```

The separate supplemental certificates establish aggregate-offset recovery and the unrestricted integer variance family, including the explicit unboundedness witness t=K+1.

Each implication retains its stated hypotheses. Each existential conclusion contains an explicit witness. Each universal conclusion is proved over the domain stated above.

[Return to contents](#contents) · [Verification and reproducibility](../VERIFICATION.md)
