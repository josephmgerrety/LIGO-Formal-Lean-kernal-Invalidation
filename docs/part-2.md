# Measurement structure and calibration range

**Exact Measurement, Common Error, and Information Recovery · Part II**  
Joseph M. Gerrety · 23 November 2026

A reversible calibration carries values, operations and relations through a specified map on a specified range. The applications below identify the exact field of this definition that fails in each example. The integer and finite-grid encodings, bounds on trigonometric inputs and assumptions about printed intervals are part of the individual propositions.

[Project and principal results](../README.md) · [Lean theorem index](theorem-index.md) · [Verification record](../VERIFICATION.md)

## Contents

**Equality, structure and calibration**  
[1. Logical foundation: equality and preservation](#s01) · [2. Extensional sets and structured isomorphisms](#s02) · [3. Measurement signatures and representations](#s03) · [4. Same quantity kind](#s04) · [5. Homomorphic association](#s05) · [6. Full substitution and injectivity](#s06) · [7. Exact calibration: supplied data](#s07) · [8. The reverse map is a left inverse](#s08) · [9. The calibrated range is closed under operations](#s09) · [10. The reverse map preserves operations](#s10) · [11. The reverse map preserves and reflects relations](#s11) · [12. Construction of the calibrated isomorphism](#s12) · [13. General operation, relation, collision, and coverage obstructions](#s13) · [14. Quantity-kind and exact unit-conversion examples](#s14) · [15. Whole tons and the proper integer calibrated range](#s15)

**Differences and parity-range recovery**  
[16. The integer model-difference map](#s16) · [17. Explicit difference collisions and their consequences](#s17) · [18. Completion by the sum coordinate](#s18) · [19. Failure to reflect the error-width relation](#s19)

**Effective precession spin**  
[20. The integer-scaled effective-spin definition](#s20) · [21. Exact coefficient and numerator calculations](#s21) · [22. The exact scaled chiP enclosure](#s22) · [23. Azimuth invariance and the explicit azimuth collision](#s23) · [24. The primary-spin fibre through amplitude 83](#s24) · [25. The primary-spin threshold from amplitude 84](#s25)

**Posterior, mode and residual projections**  
[26. Two-bin posterior combination](#s26) · [27. The monotone-function bound segment](#s27) · [28. The four-to-two mode projection](#s28) · [29. The integer Gaussian exponent](#s29) · [30. Gaussian sign witnesses and equal-exponent residuals](#s30) · [31. Failure of addition preservation for the exponent](#s31) · [32. The six-to-four spin projection](#s32)

**Printed intervals and threshold rules**  
[33. The generic interval obstruction for addition](#s33) · [34. The supplied addition certificate](#s34) · [35. The generic redshift-relation obstruction](#s35) · [36. EOBNR total-mass redshift certificate](#s36) · [37. IMRPhenom total-mass redshift certificate](#s37) · [38. IMRPhenom secondary-mass redshift certificate](#s38) · [39. IMRPhenom final-mass redshift certificate](#s39) · [40. The defined basis-point threshold verdict](#s40)

**Calibration domain and marginal tails**  
[41. The stated domain and calibrated region](#s41) · [42. The calibrated-region inclusion](#s42) · [43. The uncovered calibration point](#s43) · [44. General spin exclusion from the calibrated region](#s44) · [45. The injection and credible-spin grid certificates](#s45) · [46. The exact marginal-tail theorem](#s46) · [47. Assembly of the Part 2 conclusions](#s47)

<a name="s01" id="s01"></a>

## 1. Logical foundation: equality and preservation

[`Sameness.eq_iff_same`](../RequestProject/Equality.lean#L31) · [`Sameness.eq_iff_same_values`](../RequestProject/Equality.lean#L39) · [`Measure.preservesEquality_of_sameness`](../RequestProject/Measurement.lean#L232)

The equality foundation is expressed in the namespace Sameness.

For elements a,b of a type alpha, define

```text
Same(a,b)
↔
for every predicate P : alpha → Prop,
P(a) implies P(b).
```

The equivalence

```text
a=b  ↔  Same(a,b)
```

is proved in both directions.

If a=b, equality substitution transfers every proof of P(a) to a proof of P(b).

Conversely, instantiate the predicate with

```text
P(x):=a=x.
```

Reflexivity supplies P(a), so Same(a,b) supplies a=b.

Equality is also equivalent to agreement of all predicate truth values, and to equality of all function values with the codomain universe quantified as in the Lean declaration.

For the function-value converse, take the identity function.

Every map T therefore preserves equality:

```text
a=b implies T(a)=T(b).
```

This follows from equality congruence and requires no injectivity hypothesis.

<a name="s02" id="s02"></a>

## 2. Extensional sets and structured isomorphisms

[`Sameness.ackermann_extensional`](../RequestProject/Equality.lean#L104) · [`Sameness.PSet.eq_iff`](../RequestProject/Equality.lean#L135) · [`Sameness.MagmaIso.symm`](../RequestProject/Equality.lean#L226)

For the natural-number bit-membership representation, define membership by

```text
z belongs to x
↔
testBit(x,z)=true.
```

Suppose x and y have equivalent membership at every z.

For each z, their Boolean testBit values must agree: the two possible Boolean values are determined by whether the value is true.

Equality of all bits gives x=y by the natural-number bit-extensionality lemma used in the source.

For predicate sets, suppose that for every x,

```text
x belongs to A  ↔  x belongs to B.
```

Propositional extensionality turns each equivalence into equality of the two propositions. Function extensionality then gives equality of the two membership predicates.

An isomorphism contains a forward map, an inverse map, and both inverse equations.

These equations prove injectivity and surjectivity, as follows.

If the forward images of a and b agree, apply the inverse and use its left-inverse equations to obtain a=b.

For a target value y, its explicit preimage is the inverse image of y. The right-inverse equation proves that this preimage maps to y.

For a magma isomorphism, the forward map also preserves the designated binary operation.

Its inverse preserves that operation as well.

Apply the forward map to the two sides of the proposed inverse-operation equation. Operation preservation and the right-inverse laws make the forward images equal. Injectivity then gives the desired equation.

Equal magmas have the canonical isomorphism obtained by equality transport.

<a name="s03" id="s03"></a>

## 3. Measurement signatures and representations

[`Measure.Signature`](../RequestProject/Measurement.lean#L63) · [`Measure.MeasStructure`](../RequestProject/Measurement.lean#L72)

A measurement signature specifies operation and relation symbols by arity.

For every natural n, it contains types

```text
Op(n),

Rel(n).
```

A measured representation A supplies:

```text
A.carrier, the type of values;

A.kind, the quantity-kind label;

A.op, an interpretation of every operation symbol;

A.rel, an interpretation of every relation symbol.
```

For an n-ary operation symbol f and an input tuple

```text
xs : Fin n → A.carrier,
```

the interpreted operation is

```text
A.op(f,xs).
```

For an n-ary relation symbol r, the interpreted proposition is

```text
A.rel(r,xs).
```

Two measured representations A and B use the same signature in each comparison considered below.

<a name="s04" id="s04"></a>

## 4. Same quantity kind

[`Measure.different_quantity_kind_implies_not_comparable`](../RequestProject/Measurement.lean#L448)

Define

```text
SameKind(A,B)
↔
A.kind=B.kind.
```

A valid measurement comparison contains this equality.

An exact calibration also contains this equality.

A measured-structure isomorphism contains the same equality in its kind_eq field.

Therefore, if

```text
A.kind≠B.kind,
```

none of those structures can exist between A and B in the specified sense.

Proof:

Project the required equality of quantity kinds from any proposed comparison, calibration, or isomorphism. It contradicts the given inequality.

This is the quantity-kind obstruction.

<a name="s05" id="s05"></a>

## 5. Homomorphic association

[`Measure.HomomorphicAssociation`](../RequestProject/Measurement.lean#L112) · [`Measure.ValidMeasurementComparison`](../RequestProject/Measurement.lean#L145)

For a map

```text
T : A.carrier → B.carrier,
```

operation preservation means that, for every operation symbol f and every source tuple xs,

```text
T(A.op(f,xs))
=
B.op(f, i ↦ T(xs(i))).
```

Equality preservation means

```text
a=b implies T(a)=T(b).
```

Relation preservation means that, for every relation symbol r and source tuple xs,

```text
A.rel(r,xs)
implies
B.rel(r, i ↦ T(xs(i))).
```

HomomorphicAssociation is the conjunction of those three preservation conditions.

ValidMeasurementComparison is the conjunction of

```text
SameKind(A,B)
```

and

```text
HomomorphicAssociation(A,B,T).
```

These are the precise fields used by the subsequent obstruction theorems.

<a name="s06" id="s06"></a>

## 6. Full substitution and injectivity

[`Measure.fullSubstitution_injective`](../RequestProject/Measurement.lean#L255) · [`Measure.FullSubstitution.reflectsRelation`](../RequestProject/Measurement.lean#L242)

FullSubstitution requires equivalence of source and image equalities:

```text
a=b  ↔  T(a)=T(b),
```

and equivalence of every designated source and image relation:

```text
A.rel(r,xs)
↔
B.rel(r, i ↦ T(xs(i))).
```

Its equality component immediately implies injectivity.

Given T(a)=T(b), apply the reverse direction of

```text
a=b  ↔  T(a)=T(b).
```

The result is a=b.

Its relation component gives both preservation and reflection.

Preservation uses the forward implication of the relation equivalence.

Reflection uses its reverse implication.

Thus injectivity and relation reflection are derived directly from the specified substitution property.

<a name="s07" id="s07"></a>

## 7. Exact calibration: supplied data

[`Measure.ExactCalibration`](../RequestProject/Measurement.lean#L209)

Let

```text
Bcal : B.carrier → Prop
```

describe the calibrated range.

An ExactCalibration through T contains:

```text
sameKind:
    A.kind=B.kind;

hom:
    T preserves the designated operations, equality, and relations;

fullSubst:
    T preserves and reflects equality and the designated relations;

lands:
    Bcal(T(a)) for every a;

recal:
    an explicit function B.carrier → A.carrier;

recal_spec:
    T(recal(b))=b whenever Bcal(b).
```

The reverse function recal is part of the calibration data.

The following sections derive its left-inverse and structural properties from these fields.

<a name="s08" id="s08"></a>

## 8. The reverse map is a left inverse

[`Measure.ExactCalibration.recal_left`](../RequestProject/Measurement.lean#L271) · [`Measure.ExactCalibration.surjectiveOnto`](../RequestProject/Measurement.lean#L266)

Take any a : A.carrier.

The landing field gives

```text
Bcal(T(a)).
```

Apply recal_spec to T(a). This yields

```text
T(recal(T(a)))=T(a).
```

Full substitution supplies injectivity of T.

Apply that injectivity to the displayed equality. The result is

```text
recal(T(a))=a.
```

Thus recal is a left inverse on the entire source carrier.

Its right-inverse equation on the calibrated range is the supplied recal_spec.

For every b satisfying Bcal(b), the explicit source preimage is recal(b). This proves surjectivity onto the calibrated range.

<a name="s09" id="s09"></a>

## 9. The calibrated range is closed under operations

[`Measure.ExactCalibration.closedRange`](../RequestProject/Measurement.lean#L283)

Let f be an n-ary operation symbol.

Let

```text
bs : Fin n → B.carrier
```

be a tuple whose entries all satisfy Bcal.

For every i,

```text
T(recal(bs(i)))=bs(i).
```

Function extensionality packages these coordinate equations as equality of the complete tuples.

Operation preservation gives

```text
T(A.op(f, i ↦ recal(bs(i))))
=
B.op(f, i ↦ T(recal(bs(i)))).
```

Substituting the tuple equality gives

```text
T(A.op(f, i ↦ recal(bs(i))))
=
B.op(f,bs).
```

The left-hand side is an image under T, so the landing property proves

```text
Bcal(B.op(f,bs)).
```

Hence the calibrated range is closed under every designated operation.

<a name="s10" id="s10"></a>

## 10. The reverse map preserves operations

[`Measure.ExactCalibration.recal_preservesOperation`](../RequestProject/Measurement.lean#L291)

For the same calibrated tuple bs, consider

```text
recal(B.op(f,bs))
```

and

```text
A.op(f, i ↦ recal(bs(i))).
```

Their T-images are equal.

For the first expression, closure of the calibrated range permits recal_spec:

```text
T(recal(B.op(f,bs)))
=
B.op(f,bs).
```

For the second, operation preservation and the tuple right-inverse equations give

```text
T(A.op(f, i ↦ recal(bs(i))))
=
B.op(f,bs).
```

Injectivity of T therefore yields

```text
recal(B.op(f,bs))
=
A.op(f, i ↦ recal(bs(i))).
```

Thus reverse operation preservation is derived from the supplied calibration fields.

<a name="s11" id="s11"></a>

## 11. The reverse map preserves and reflects relations

[`Measure.ExactCalibration.recal_rel_iff`](../RequestProject/Measurement.lean#L299)

Take a designated relation r and a calibrated tuple bs.

Apply the relation equivalence in FullSubstitution to the source tuple

```text
i ↦ recal(bs(i)).
```

It gives

```text
A.rel(r, i ↦ recal(bs(i)))
↔
B.rel(r, i ↦ T(recal(bs(i)))).
```

The tuple right-inverse equations replace the final tuple by bs.

Therefore

```text
B.rel(r,bs)
↔
A.rel(r, i ↦ recal(bs(i))).
```

This proves both reverse relation preservation and reverse relation reflection.

<a name="s12" id="s12"></a>

## 12. Construction of the calibrated isomorphism

[`Measure.exact_calibration_implies_isomorphic_transposition`](../RequestProject/Measurement.lean#L339) · [`Measure.exists_exact_calibration_iff_isomorphic`](../RequestProject/Measurement.lean#L381)

Restrict the target carrier to the subtype

```text
{b : B.carrier | Bcal(b)}.
```

The previously proved closure property supplies the operations on this restricted carrier. The relations and quantity kind are inherited from B.

Define the forward map by

```text
a ↦ (T(a), proof that Bcal(T(a))).
```

Define the inverse map by

```text
b ↦ recal(b.value).
```

The left-inverse law is

```text
recal(T(a))=a.
```

The right-inverse law follows from recal_spec and subtype equality.

Forward operation preservation comes from hom.

Forward relation preservation and reflection come from fullSubst.

Reverse operation preservation was proved in Section 10.

Reverse relation preservation and reflection were proved in Section 11.

The quantity-kind equality is sameKind.

These fields construct

```text
MeasIso A (B restricted to Bcal).
```

The theorem

```text
Measure.exact_calibration_implies_isomorphic_transposition
```

assembles the resulting conclusions:

```text
same quantity kind;

homomorphic association;

full substitution;

injectivity;

surjectivity onto Bcal;

preservation of operations by recal on Bcal;

preservation and reflection of relations by recal on Bcal;

isomorphic transposition into the restricted calibrated carrier.
```

The isomorphism is constructed from the supplied reverse map.

<a name="s13" id="s13"></a>

## 13. General operation, relation, collision, and coverage obstructions

[`Measure.not_hom_implies_not_valid`](../RequestProject/Measurement.lean#L398) · [`LigoSpecious.fibre_obstructs`](../RequestProject/LIGO_specious_measures.lean#L95) · [`Measure.not_surjective_implies_not_calibration`](../RequestProject/Measurement.lean#L421)

An operation obstruction consists of a symbol f and a tuple xs for which

```text
T(A.op(f,xs))
≠
B.op(f, i ↦ T(xs(i))).
```

If operation preservation held, its specialization to f and xs would give the forbidden equality.

Therefore operation preservation fails.

A ValidMeasurementComparison contains operation preservation, so it also fails.

An ExactCalibration contains the same preservation field, so no such calibration through T exists.

A relation-preservation obstruction consists of a source relation

```text
A.rel(r,xs)
```

whose corresponding image relation is false.

Preservation would send the source proof to that false image proposition, giving a contradiction.

A relation-reflection obstruction consists of an image relation that holds while the source relation fails.

The reverse implication of FullSubstitution would then prove the false source proposition.

A collision obstruction consists of

```text
a1≠a2,

T(a1)=T(a2).
```

Injectivity would turn the second statement into a1=a2.

FullSubstitution implies injectivity.

ExactCalibration contains FullSubstitution.

An isomorphism whose forward map agrees with T is also injective.

Consequently, the same explicit collision excludes all four claims:

```text
Injective(A,B,T);

FullSubstitution(A,B,T);

ExactCalibration(A,B,Bcal,T), for every Bcal;

IsomorphicTransposition(A,B,T).
```

A coverage obstruction consists of b satisfying Bcal(b) for which

```text
T(a)≠b
```

for every a.

An exact calibration would provide recal(b) with T(recal(b))=b, contradicting that obstruction.

<a name="s14" id="s14"></a>

## 14. Quantity-kind and exact unit-conversion examples

[`Measure.different_quantity_kind_implies_not_comparable`](../RequestProject/Measurement.lean#L448) · [`Measure.tons_vs_smiles_not_comparable`](../RequestProject/Examples.lean#L121) · [`Measure.tons_kg_isomorphic_transposition`](../RequestProject/Examples.lean#L233) · [`Measure.two_hundred_tons_vs_fifteen_kg`](../RequestProject/Examples.lean#L247)

The quantity-kind type contains distinct constructors for mass and smile count.

The ton and kilogram structures have kind mass.

The smile-count structure has kind smileCount.

The constructors mass and smileCount are unequal.

Therefore no function from the ton structure to the smile-count structure is a valid measurement comparison or an exact calibration between those defined representations.

In particular, numerals such as 200 and 41 do not remove the quantity-kind obstruction.

For the rational short-ton and kilogram carriers, define

```text
c=907.18474,

T(a)=c a,

recal(b)=b/c.
```

The rational constant c is positive and nonzero.

Addition preservation follows from distributivity:

```text
T(a+a')
=
c(a+a')
=
ca+ca'
=
T(a)+T(a').
```

Multiplication by the positive c preserves and reflects both ≤ and <.

Nonzero multiplication cancellation gives equality reflection.

The inverse equations are

```text
recal(T(a))=(ca)/c=a,

T(recal(b))=c(b/c)=b.
```

Thus T is an exact calibration onto the entire rational kilogram carrier, preserving the designated addition and order structure.

The exact numerical calculation is

```text
T(200)
=
200×907.18474
=
181436.948.
```

The numerical comparison is

```text
181436.948>15.
```

<a name="s15" id="s15"></a>

## 15. Whole tons and the proper integer calibrated range

[`Measure.not_surjective_implies_not_calibration`](../RequestProject/Measurement.lean#L421) · [`Measure.wholeTons_isomorphic_calibrated_range`](../RequestProject/Examples.lean#L365) · [`Measure.tonsToFine_not_full_calibration`](../RequestProject/Examples.lean#L371) · [`Measure.two_hundred_whole_tons`](../RequestProject/Examples.lean#L379)

On the integer whole-ton carrier, define

```text
k=90718474,

T(n)=kn.
```

One target fine unit represents 10 mg.

The calibrated range is

```text
Bcal(b)  ↔  k divides b.
```

The explicit reverse is integer division by k.

For every source n,

```text
k divides kn,
```

so the map lands in the calibrated range.

If Bcal(b), write b=kn using its divisibility witness.

Integer division by the positive nonzero k gives

```text
b/k=n,
```

and hence

```text
T(b/k)=b.
```

The map preserves addition by distributivity.

Its positive multiplier preserves and reflects the designated order relations.

Its nonzero multiplier makes it injective.

These facts construct an exact calibration onto the divisibility range.

The integer 1 is outside that range.

Indeed, if kn=1, then for n≤0 the product is nonpositive, while for n≥1 the product is at least k>1. Neither case permits kn=1.

Therefore there is no exact calibration through this T onto the entire integer target carrier.

The exact numerical certificate is

```text
T(200)
=
90718474×200
=
18143694800.
```

This exceeds

```text
1500000,
```

the encoded comparison value.

<a name="s16" id="s16"></a>

## 16. The integer model-difference map

[`LigoSpecious.ligo_modelDifference_commonMode_fibre`](../RequestProject/LIGO_specious_measures.lean#L170) · [`LigoSpecious.modelDiff_homomorphic`](../RequestProject/LIGO_specious_measures.lean#L162)

Let the source carrier be Int×Int with componentwise addition, and let the target carrier be Int with addition.

Define

```text
modelDiff(x,y)=x-y.
```

It preserves addition:

```text
modelDiff((x,y)+(u,v))
=
x+u-(y+v)

=
(x-y)+(u-v).
```

Its zero fibre is

```text
modelDiff(x,y)=0  ↔  x=y.
```

It is invariant under a common shift:

```text
modelDiff(x+g,y+g)
=
x+g-y-g
=
x-y.
```

The complete fibre description is

```text
modelDiff(x,y)=modelDiff(x',y')
```

if and only if there exists g : Int with

```text
x'=x+g,

y'=y+g.
```

For the forward direction, use the explicit witness

```text
g=x'-x.
```

Then x'=x+g.

The assumed equal-difference equation gives

```text
y'=y+x'-x=y+g.
```

For the reverse direction, substitute the two common-shift equations and cancel g.

<a name="s17" id="s17"></a>

## 17. Explicit difference collisions and their consequences

[`LigoSpecious.modelDiff_fibre_witness`](../RequestProject/LIGO_specious_measures.lean#L202) · [`LigoSpecious.ligo_modelDifference_no_exact_calibration`](../RequestProject/LIGO_specious_measures.lean#L216)

The fixed evaluations are

```text
modelDiff(84,84)=0,

modelDiff(98,98)=0,

modelDiff(64,64)=0.
```

For every R : Int,

```text
R+(84-R)=84,
```

and

```text
modelDiff(84-R,84-R)=0.
```

The states

```text
(84,84),

(98,98)
```

are distinct and have equal modelDiff values.

Apply the general collision obstruction.

The map modelDiff is not injective.

It does not satisfy FullSubstitution.

For every proposed calibrated range Bcal, no ExactCalibration through modelDiff exists on the full source pair carrier.

It is not an IsomorphicTransposition of that source pair carrier.

All these conclusions use the same explicit pair.

<a name="s18" id="s18"></a>

## 18. Completion by the sum coordinate

[`LigoSpecious.diffSum_recal_spec`](../RequestProject/LIGO_specious_measures.lean#L270) · [`LigoSpecious.ligo_modelDifference_anchor_isomorphism`](../RequestProject/LIGO_specious_measures.lean#L288)

Define

```text
diffSum(x,y)=(x-y,x+y).
```

Here the target coordinate order is

```text
(d,s)=(difference,sum).
```

The map preserves addition coordinatewise.

It is injective.

If

```text
x-y=x'-y',

x+y=x'+y',
```

adding the equations gives

```text
2x=2x',
```

and subtracting them gives

```text
2y=2y'.
```

Integer cancellation yields x=x' and y=y'.

The target range is

```text
parityRange(d,s)
↔
(d+s) mod 2=0.
```

Every source image lies in this range because

```text
(x-y)+(x+y)=2x.
```

Define the explicit inverse by

```text
diffSumRecal(d,s)
=
((s+d)/2,(s-d)/2),
```

using integer division.

Assume the parity condition.

Then s+d is even.

Also,

```text
s-d=(s+d)-2d,
```

so s-d is even.

Consequently, if

```text
k=(s+d)/2,

l=(s-d)/2,
```

the integer division identities give

```text
2k=s+d,

2l=s-d.
```

Adding and subtracting these equations yields

```text
k+l=s,

k-l=d.
```

Therefore

```text
diffSum(diffSumRecal(d,s))=(d,s).
```

These equations hold for negative and nonnegative integers under the stated parity premise.

The source packages the map, its inverse, operation preservation, equality reflection, range membership, and inverse equation into diffSumCalibration.

The general calibration construction then gives an isomorphism with the parity-range subtype.

In particular, for every d,s : Int with matching parity, the explicit pair diffSumRecal(d,s) has difference d and sum s.

<a name="s19" id="s19"></a>

## 19. Failure to reflect the error-width relation

[`LigoSpecious.ligo_modelDifference_width_not_reflected`](../RequestProject/LIGO_specious_measures.lean#L339) · [`LigoSpecious.ligo_modelDifference_q_widths_not_reflected`](../RequestProject/LIGO_specious_measures.lean#L352)

For a width w : Int, the source relation requires both errors to lie in the interval [-w,w]:

```text
-w≤e1≤w,

-w≤e2≤w.
```

The target relation requires the difference to lie in [-w,w].

Assume

```text
w≥0,

g>w.
```

Take the source pair

```text
(g,g).
```

It fails the source relation, since g≤w is false.

Its model difference is

```text
g-g=0.
```

Because w≥0,

```text
-w≤0≤w,
```

so its image satisfies the target relation.

Thus the image relation does not reflect the source relation. FullSubstitution fails for these structures.

The supplied numerical instances are

```text
w=14, g=15,
```

and

```text
w=20, g=21.
```

Both common-error pairs have zero difference and exceed their respective source widths.

<a name="s20" id="s20"></a>

## 20. The integer-scaled effective-spin definition

[`LigoSpecious.chiP`](../RequestProject/LIGO_specious_measures.lean#L414) · [`LigoSpecious.nrInjection`](../RequestProject/LIGO_specious_measures.lean#L433)

A SpinState has fields

```text
q,a1,a2 : Nat,

th1,th2,ph1,ph2 : Int.
```

In this encoding, q and the spin amplitudes use hundredths, while the tilt and azimuth coordinates use tenths of a degree.

Let

```text
sinMicro : Int → Nat
```

be a supplied function.

Define

```text
K1(n)=100(3n+400),

K2(n)=n(4n+300).
```

Define maxN by

```text
maxN(x,y)=y when x≤y,

maxN(x,y)=x otherwise.
```

The numerator is

```text
chiPNum(s)
=
maxN(
  K1(s.q) s.a1 sinMicro(s.th1),
  K2(s.q) s.a2 sinMicro(s.th2)
).
```

The denominator is

```text
chiPDen(s)=K1(s.q)×100000000.
```

The encoded chiP observation is the numerator-denominator pair.

The injection record is

```text
nrInjection
=
(81,34,67,188,1494,309,387).
```

The numerical theorem takes the explicit hypotheses

```text
322265≤sinMicro(188)≤322266,

509041≤sinMicro(1494)≤509042.
```

Write

```text
u=sinMicro(188),

v=sinMicro(1494).
```

<a name="s21" id="s21"></a>

## 21. Exact coefficient and numerator calculations

[`LigoSpecious.chiPNum_nrInjection`](../RequestProject/LIGO_specious_measures.lean#L440) · [`LigoSpecious.ligo_chiP_real_values`](../RequestProject/LIGO_specious_measures.lean#L458)

At q=81,

```text
K1(81)
=
100(3×81+400)
=
64300,
```

and

```text
K2(81)
=
81(4×81+300)
=
50544.
```

The denominator is

```text
D=64300×100000000
 =6430000000000.
```

The numerator is

```text
N=maxN(64300×34×u,50544×67×v).
```

The primary term is at most

```text
64300×34×322266
=
704537929200.
```

The secondary term is at least

```text
50544×67×509041
=
1723840876368,
```

and at most

```text
50544×67×509042
=
1723844262816.
```

Therefore the secondary term dominates throughout the supplied windows.

Its minimum value exceeds the maximum primary value by

```text
1723840876368-704537929200
=
1019302947168.
```

The maxN definition therefore gives the exact identity

```text
N=50544×67×v.
```

<a name="s22" id="s22"></a>

## 22. The exact scaled chiP enclosure

[`LigoSpecious.ligo_chiP_real_values`](../RequestProject/LIGO_specious_measures.lean#L458) · [`LigoSpecious.ligo_chiP_real_values_closed`](../RequestProject/LIGO_specious_measures.lean#L509)

The lower endpoint comparison is

```text
268093×D
=
1723837990000000000,
```

and

```text
1000000×1723840876368
=
1723840876368000000.
```

Their difference is

```text
2886368000000>0.
```

Thus

```text
268093D≤1000000N.
```

The upper endpoint comparison is

```text
1000000×1723844262816
=
1723844262816000000,
```

and

```text
268094×D
=
1723844420000000000.
```

Their difference is

```text
157184000000>0.
```

Thus

```text
1000000N≤268094D.
```

Together,

```text
268093D≤1000000N≤268094D.
```

Since D>0, division gives

```text
0.268093≤N/D≤0.268094.
```

Also,

```text
268094<400000,
```

so

```text
N/D<0.4.
```

For the primary contribution,

```text
34×322265=10957010,

34×322266=10957044.
```

Hence

```text
10957000≤34u≤10958000.
```

With the stated scaling, this places the primary contribution between

```text
0.10957
```

and

```text
0.10958.
```

For the defined function sinAtTilts, the relevant values are

```text
sinAtTilts(188)=322266,

sinAtTilts(1494)=509041.
```

Its closed encoded chiP value is

```text
(1723840876368,6430000000000).
```

<a name="s23" id="s23"></a>

## 23. Azimuth invariance and the explicit azimuth collision

[`LigoSpecious.ligo_chiP_azimuth_fibre`](../RequestProject/LIGO_specious_measures.lean#L528) · [`LigoSpecious.ligo_chiP_no_exact_calibration`](../RequestProject/LIGO_specious_measures.lean#L554)

Neither chiPNum nor chiPDen uses ph1 or ph2.

Changing either azimuth field therefore leaves both components of the encoded chiP pair unchanged.

This statement holds for every supplied sinMicro function.

Replace the injection's first azimuth

```text
ph1=309
```

by

```text
ph1=1000,
```

keeping the other fields fixed.

The records are distinct because their first azimuths differ.

Their encoded azimuth differences are

```text
309-387=-78,
```

and

```text
1000-387=613.
```

Their chiP observations are equal.

This collision proves non-injectivity of the chiP map on the full encoded spin-state carrier.

It also excludes FullSubstitution, ExactCalibration through that map onto every proposed range, and IsomorphicTransposition through that map.

<a name="s24" id="s24"></a>

## 24. The primary-spin fibre through amplitude 83

[`LigoSpecious.ligo_chiP_primarySpin_fibre`](../RequestProject/LIGO_specious_measures.lean#L584)

Retain the two sine-window hypotheses and keep every injection field except a1 fixed.

Let a : Nat satisfy

```text
a≤83.
```

Then

```text
a u≤83×322266.
```

The changed primary numerator is therefore at most

```text
64300×83×322266
=
1719901415400.
```

The unchanged secondary numerator is at least

```text
1723840876368.
```

The gap is

```text
1723840876368-1719901415400
=
3939460968>0.
```

Thus the changed primary term remains below the secondary term.

The new maximum is the same secondary numerator as before.

The denominator is unchanged because q is unchanged.

Therefore every natural amplitude a≤83 gives exactly the original encoded chiP pair under the stated hypotheses.

<a name="s25" id="s25"></a>

## 25. The primary-spin threshold from amplitude 84

[`LigoSpecious.ligo_chiP_primarySpin_threshold`](../RequestProject/LIGO_specious_measures.lean#L603) · [`LigoSpecious.ligo_chiP_primarySpin_credible_intervals`](../RequestProject/LIGO_specious_measures.lean#L631)

Now let a : Nat satisfy

```text
84≤a.
```

The sine lower bound gives

```text
a u≥84×322265.
```

The changed primary numerator is at least

```text
64300×84×322265
=
1740617718000.
```

The secondary numerator is at most

```text
1723844262816.
```

The gap is

```text
1740617718000-1723844262816
=
16773455184>0.
```

Thus the changed primary term strictly exceeds the secondary term.

The new maximum is the primary term and is strictly greater than the original numerator.

Equality of the two encoded pairs would imply equality of their first coordinates, contradicting this strict inequality.

Therefore every natural amplitude a≥84 changes the encoded chiP pair.

The stated hundredth-grid intervals ending at 65 and 78 lie within the a≤83 fibre. The endpoint 85 satisfies a≥84 and lies beyond that fibre.

<a name="s26" id="s26"></a>

## 26. Two-bin posterior combination

[`LigoSpecious.ligo_modelAverage_fibre`](../RequestProject/LIGO_specious_measures.lean#L704) · [`LigoSpecious.ligo_modelAverage_not_injective`](../RequestProject/LIGO_specious_measures.lean#L753)

A Post2 record has four integer entries:

```text
P=(eob1,eob2,imr1,imr2).
```

Define

```text
overall(P)
=
(eob1+imr1,eob2+imr2).
```

For any integer delta, redistribute the entries by

```text
(delta,-delta,-delta,delta).
```

The first output coordinate becomes

```text
(eob1+delta)+(imr1-delta)
=
eob1+imr1.
```

The second becomes

```text
(eob2-delta)+(imr2+delta)
=
eob2+imr2.
```

Thus overall is invariant under this redistribution.

The records

```text
P1=(100,0,80,20),

P2=(90,10,90,10)
```

are distinct, since their eob1 coordinates differ.

Their images are

```text
overall(P1)=(180,20),

overall(P2)=(180,20).
```

This explicit collision excludes injectivity, FullSubstitution, ExactCalibration through overall onto every proposed range, and IsomorphicTransposition through overall.

<a name="s27" id="s27"></a>

## 27. The monotone-function bound segment

[`LigoSpecious.ligo_modelAverage_bound_segment`](../RequestProject/LIGO_specious_measures.lean#L726)

Let

```text
FE,FP : Int → Int.
```

Assume both functions are nondecreasing:

```text
x≤y implies FE(x)≤FE(y),

x≤y implies FP(x)≤FP(y).
```

Retain the global bounds

```text
FE(x)≤100 for every x,

0≤FP(x) for every x.
```

Let

```text
xE<xO<xP,
```

and assume

```text
FE(xE)=90,

FP(xP)=90,

FE(xO)+FP(xO)=180.
```

Monotonicity gives

```text
90=FE(xE)≤FE(xO),
```

and

```text
FP(xO)≤FP(xP)=90.
```

The global FE bound gives

```text
FE(xO)≤100.
```

Using the sum equation,

```text
FP(xO)=180-FE(xO)≥80.
```

Therefore

```text
90≤FE(xO)≤100,

80≤FP(xO)≤90.
```

Form the record

```text
(
  FE(xO),
  100-FE(xO),
  FP(xO),
  100-FP(xO)
).
```

Its first overall coordinate is 180 by hypothesis.

Its second overall coordinate is

```text
200-(FE(xO)+FP(xO))
=
200-180
=
20.
```

Hence its overall image is exactly

```text
(180,20).
```

The eleven integer records on the displayed segment are

```text
(90,10,90,10),
(91,9,89,11),
(92,8,88,12),
(93,7,87,13),
(94,6,86,14),
(95,5,85,15),
(96,4,84,16),
(97,3,83,17),
(98,2,82,18),
(99,1,81,19),
(100,0,80,20).
```

Every one maps to (180,20).

<a name="s28" id="s28"></a>

## 28. The four-to-two mode projection

[`LigoSpecious.ligo_modeProjection_fibre`](../RequestProject/LIGO_specious_measures.lean#L832) · [`LigoSpecious.ligo_modeProjection_linear_not_injective`](../RequestProject/LIGO_specious_measures.lean#L881)

A ModeAmps record contains four integers

```text
(h22,h2m2,h21,h2m1).
```

Define

```text
proj22(h22,h2m2,h21,h2m1)
=
(h22,h2m2).
```

Componentwise addition is preserved because projecting a componentwise sum gives the sum of the projected components.

The source and target structures have the same mode-amplitude kind.

Their designated relation interpretations in this additive signature make the relation-preservation field immediate.

Thus proj22 is a ValidMeasurementComparison for these defined structures.

Its fibres are explicit.

For every a,b,c,d,c',d',

```text
proj22(a,b,c,d)=proj22(a,b,c',d').
```

Its zero-image condition is

```text
proj22(h)=(0,0)
↔
h.h22=0 and h.h2m2=0.
```

The records

```text
(5,7,0,0),

(5,7,3,-3)
```

have the same image (5,7) and differ in h21.

Therefore proj22 is not injective.

The same witness excludes FullSubstitution, ExactCalibration through proj22 onto every proposed range, and IsomorphicTransposition through proj22.

The development records both operation preservation and non-injectivity as a conjunction.

<a name="s29" id="s29"></a>

## 29. The integer Gaussian exponent

[`LigoSpecious.gaussExponent_resNeg`](../RequestProject/LIGO_specious_measures.lean#L928) · [`LigoSpecious.ligo_likelihood_sign_fibre`](../RequestProject/LIGO_specious_measures.lean#L943)

For a finite list of integer residuals, define recursively

```text
gaussExponent([])=0,

gaussExponent(x::xs)
=
x²+gaussExponent(xs).
```

Thus gaussExponent is the sum of the squared entries.

Define resNeg by negating every entry.

For every x : Int,

```text
(-x)(-x)=xx.
```

We prove

```text
gaussExponent(resNeg(r))
=
gaussExponent(r)
```

by induction on r.

For the empty list, both sides are zero.

For x::xs, the left side is

```text
(-x)²+gaussExponent(resNeg(xs)).
```

The square identity and induction hypothesis replace this by

```text
x²+gaussExponent(xs),
```

which is the right side.

For every type beta and every function

```text
g : Int → beta,
```

congruence gives

```text
g(gaussExponent(resNeg(r)))
=
g(gaussExponent(r)).
```

This conclusion requires only equality of the exponent arguments.

<a name="s30" id="s30"></a>

## 30. Gaussian sign witnesses and equal-exponent residuals

[`LigoSpecious.likelihood_fibre_witness`](../RequestProject/LIGO_specious_measures.lean#L961) · [`LigoSpecious.ligo_likelihood_no_exact_calibration`](../RequestProject/LIGO_specious_measures.lean#L998)

If a residual list has nonzero first entry x, it differs from its negation.

Suppose, to the contrary,

```text
resNeg(x::xs)=x::xs.
```

Equality of the first entries gives

```text
-x=x.
```

Integer arithmetic implies x=0, contradicting the hypothesis.

A fixed witness for every composite g composed with gaussExponent is

```text
[1],

[-1].
```

Their exponents both equal 1, so their g-images agree.

Their first entries differ, so the lists are distinct.

The general collision theorem therefore excludes injectivity, FullSubstitution, ExactCalibration onto every proposed range, and IsomorphicTransposition through this composite.

A second fixed equal-exponent pair is

```text
[1,0,0,3],

[2,1,1,2].
```

Their exponents are

```text
1²+0²+0²+3²=10,
```

and

```text
2²+1²+1²+2²=10.
```

Their first entries are 1 and 2, so the lists are unequal.

<a name="s31" id="s31"></a>

## 31. Failure of addition preservation for the exponent

[`LigoSpecious.ligo_likelihood_not_additive`](../RequestProject/LIGO_specious_measures.lean#L1026) · [`LigoSpecious.ligo_residual_weight_not_comparable`](../RequestProject/LIGO_specious_measures.lean#L1040)

The residual operation zipAdd adds corresponding entries recursively, with the source's specified empty-list termination.

For the witness used by the theorem,

```text
zipAdd([1],[1])=[2].
```

Therefore

```text
gaussExponent(zipAdd([1],[1]))
=
gaussExponent([2])
=
4.
```

But

```text
gaussExponent([1])+gaussExponent([1])
=
1+1
=
2.
```

Since 4≠2, the exponent does not preserve the designated addition operation.

The residual and exponent-value structures also have distinct quantity-kind labels:

```text
strain,

evidenceWeight.
```

The quantity-kind obstruction consequently excludes valid measurement comparison and exact calibration between those defined structures for every proposed map requiring those labels to agree.

<a name="s32" id="s32"></a>

## 32. The six-to-four spin projection

[`LigoSpecious.ligo_imrPhenom_spinCompression_fibre`](../RequestProject/LIGO_specious_measures.lean#L1148) · [`LigoSpecious.imrSpin_surjective`](../RequestProject/LIGO_specious_measures.lean#L1136)

A Spin6 record contains

```text
(s1x,s1y,s1z,s2x,s2y,s2z).
```

A Spin4 record contains

```text
(z1,z2,px,py).
```

Define

```text
imrSpin(s)
=
(
  s1z,
  s2z,
  s1x+s2x,
  s1y+s2y
).
```

The map preserves componentwise addition.

For example, the third output coordinate after adding two source states is

```text
(s1x+t1x)+(s2x+t2x).
```

Associativity and commutativity rearrange this to

```text
(s1x+s2x)+(t1x+t2x),
```

which is the third coordinate obtained by adding the two output records.

The other coordinates follow directly or by the same calculation.

The map is surjective onto the defined four-integer carrier.

For a desired target

```text
(z1,z2,px,py),
```

choose the source

```text
(px,py,z1,0,0,z2).
```

Its image is exactly the desired target.

Equal retained components give equal images:

```text
equal s1z;

equal s2z;

equal s1x+s2x;

equal s1y+s2y.
```

For every u,v : Int,

```text
imrSpin(u,v,0,-u,-v,0)
=
(0,0,0,0).
```

A fixed collision is

```text
(1,0,0,0,0,0),

(0,0,0,1,0,0).
```

Both images are

```text
(0,0,1,0).
```

The source records are distinct in s1x.

Therefore the map is not injective and does not admit FullSubstitution, ExactCalibration through it onto any proposed range, or IsomorphicTransposition through it.

<a name="s33" id="s33"></a>

## 33. The generic interval obstruction for addition

[`LigoSpecious.tableI_median_not_additive`](../RequestProject/LIGO_published_ledger.lean#L80)

Let A be a measured representation with the table signature.

Let

```text
T : A.carrier → Nat,
```

and let xs be a source tuple for the binary addition operation.

Write

```text
a=T(xs(0)),

b=T(xs(1)),

c=T(A.op(add,xs)).
```

Suppose these values lie in intervals

```text
aLo≤a≤aHi,

bLo≤b≤bHi,

cLo≤c≤cHi.
```

If

```text
aHi+bHi<cLo,
```

then

```text
a+b≤aHi+bHi<cLo≤c.
```

Thus c≠a+b.

If instead

```text
cHi<aLo+bLo,
```

then

```text
c≤cHi<aLo+bLo≤a+b.
```

Again c≠a+b.

Operation preservation would require c=a+b, so either strict interval separation proves failure of operation preservation.

The corresponding ValidMeasurementComparison and ExactCalibration claims fail because their records contain the contradicted operation-preservation field.

<a name="s34" id="s34"></a>

## 34. The supplied addition certificate

[`LigoSpecious.ligo_tableI_imrphenom_median_not_additive`](../RequestProject/LIGO_published_ledger.lean#L101)

The concrete interval hypotheses are

```text
3845≤T(xs(0))≤3855,

3215≤T(xs(1))≤3225,

7085≤T(A.op(add,xs))≤7095.
```

The separate readings satisfy

```text
T(xs(0))+T(xs(1))
≤
3855+3225
=
7080.
```

The reading of the source sum satisfies

```text
7085≤T(A.op(add,xs)).
```

Since

```text
7080<7085,
```

the required operation-preservation equality is impossible.

The possible sum interval is

```text
[7060,7080],
```

whereas the designated total interval is

```text
[7085,7095].
```

The intervals are disjoint, with a strict endpoint separation of 5.

Therefore the theorem concludes

```text
not PreservesOperation(A,natStr,T),

not ValidMeasurementComparison(A,natStr,T),
```

and, for every proposed Bcal,

```text
not Nonempty(ExactCalibration(A,natStr,Bcal,T)).
```

These are implications from the displayed interval hypotheses.

<a name="s35" id="s35"></a>

## 35. The generic redshift-relation obstruction

[`LigoSpecious.tableI_median_not_redshift_relation`](../RequestProject/LIGO_published_ledger.lean#L126)

The target table relation is

```text
10000d=(10000+z)s.
```

Let xs be a source triple and assume the source relation

```text
A.rel(redshift,xs).
```

Write

```text
d=T(xs(0)),

z=T(xs(1)),

s=T(xs(2)).
```

Assume natural-number interval bounds

```text
dLo≤d≤dHi,

zLo≤z≤zHi,

sLo≤s≤sHi.
```

If T preserves the relation, the source relation implies

```text
10000d=(10000+z)s.
```

But the interval bounds give

```text
10000d≤10000dHi,
```

and

```text
(10000+zLo)sLo≤(10000+z)s.
```

Consequently, the strict endpoint inequality

```text
10000dHi<(10000+zLo)sLo
```

makes the proposed relation impossible.

The generic theorem also treats the opposite separation:

```text
(10000+zHi)sHi<10000dLo.
```

That inequality likewise makes equality of the two sides impossible.

In either case, relation preservation fails.

A ValidMeasurementComparison contains relation preservation, so it fails.

Every proposed ExactCalibration through the map contains relation preservation as well, so it is excluded for every proposed calibrated range.

<a name="s36" id="s36"></a>

## 36. EOBNR total-mass redshift certificate

[`LigoSpecious.ligo_tableI_eobnr_totalMass_not_redshift`](../RequestProject/LIGO_published_ledger.lean#L151)

Retain the source-relation hypothesis and assume

```text
d in [7155,7165],

z in [935,945],

s in [6555,6565].
```

The maximum detector-side product is

```text
10000×7165
=
71650000.
```

The minimum redshifted source-side product is

```text
(10000+935)×6555

=
10935×6555

=
71678925.
```

The strict gap is

```text
71678925-71650000
=
28925>0.
```

Therefore

```text
10000d<(10000+z)s
```

throughout the displayed intervals.

This contradicts the relation that preservation would require.

The theorem excludes PreservesRelation, ValidMeasurementComparison, and ExactCalibration through the map under the stated premises.

<a name="s37" id="s37"></a>

## 37. IMRPhenom total-mass redshift certificate

[`LigoSpecious.ligo_tableI_imrphenom_totalMass_not_redshift`](../RequestProject/LIGO_published_ledger.lean#L167)

Retain the source-relation hypothesis and assume

```text
d in [7085,7095],

z in [925,935],

s in [6495,6505].
```

Then

```text
10000×7095
=
70950000,
```

while

```text
(10000+925)×6495

=
10925×6495

=
70957875.
```

The gap is

```text
7875>0.
```

The maximum possible detector-side product is smaller than the minimum possible redshifted source-side product.

Therefore the same three structural exclusions follow under these premises.

<a name="s38" id="s38"></a>

## 38. IMRPhenom secondary-mass redshift certificate

[`LigoSpecious.ligo_tableI_imrphenom_secondaryMass_not_redshift`](../RequestProject/LIGO_published_ledger.lean#L183)

Retain the source-relation hypothesis and assume

```text
d in [3215,3225],

z in [925,935],

s in [2955,2965].
```

Then

```text
10000×3225
=
32250000,
```

while

```text
(10000+925)×2955

=
10925×2955

=
32283375.
```

The gap is

```text
33375>0.
```

Again the required target relation is impossible throughout the displayed intervals.

Relation preservation, valid measurement comparison, and exact calibration through the map are excluded under the stated premises.

<a name="s39" id="s39"></a>

## 39. IMRPhenom final-mass redshift certificate

[`LigoSpecious.ligo_tableI_imrphenom_finalMass_not_redshift`](../RequestProject/LIGO_published_ledger.lean#L200)

Retain the source-relation hypothesis and assume

```text
d in [6755,6765],

z in [925,935],

s in [6195,6205].
```

Then

```text
10000×6765
=
67650000,
```

while

```text
(10000+925)×6195

=
10925×6195

=
67680375.
```

The gap is

```text
30375>0.
```

This supplies the fourth strict endpoint separation and the corresponding three structural exclusions.

<a name="s40" id="s40"></a>

## 40. The defined basis-point threshold verdict

[`LigoSpecious.ligo_ks_phi12_verdict_split`](../RequestProject/LIGO_published_ledger.lean#L229)

Define, for p : Nat,

```text
ksVerdict(p)=true when p<500,
```

and false otherwise.

The closed endpoint evaluations are

```text
ksVerdict(77)=true,

ksVerdict(750)=false.
```

If

```text
77≤p≤499,
```

then p<500, so ksVerdict(p)=true.

If

```text
500≤p≤750,
```

then p<500 is false, so ksVerdict(p)=false.

If

```text
3000≤p≤6000,
```

then p≥500, and the verdict is also false.

These are exact statements about the defined threshold function.

<a name="s41" id="s41"></a>

## 41. The stated domain and calibrated region

[`LigoSpecious.calibrated_subset`](../RequestProject/LIGO_published_ledger.lean#L297)

A ParamPoint has natural coordinates

```text
(q,a1,a2).
```

These domain coordinates use thousandths.

The stated domain is

```text
10≤q≤1000,

a1≤990,

a2≤990.
```

The calibrated region is

```text
125≤q≤1000,

a1≤990,

a2≤990,
```

together with

```text
q=1000
```

or

```text
a1≤500 and a2≤500.
```

Every calibrated point lies in the stated domain.

The only different lower bound is 125 instead of 10, and

```text
10≤125≤q.
```

The other stated-domain bounds are already fields of calibrated-region membership.

<a name="s42" id="s42"></a>

## 42. The calibrated-region inclusion

[`LigoSpecious.calEmbed_homomorphic`](../RequestProject/LIGO_published_ledger.lean#L313) · [`LigoSpecious.calEmbed_injective`](../RequestProject/LIGO_published_ledger.lean#L317)

Let CalPoint be the subtype of ParamPoint satisfying calibratedRegion.

Let StatedPoint be the subtype satisfying statedDomain.

Define calEmbed by retaining the underlying ParamPoint and supplying its stated-domain membership proof from the subset theorem.

This inclusion is injective.

Equality of two StatedPoint images gives equality of their underlying ParamPoint values. Equality of those values gives equality of the original CalPoint subtype elements.

The source and target structures have the same quantity kind and use the bare signature.

There are no operation symbols to check. The corresponding preservation obligation is eliminated using the empty operation-symbol type.

Equality preservation holds for every function.

The relation-preservation obligation is immediate for the defined bare relation interpretation.

Thus calEmbed is a ValidMeasurementComparison.

The source also proves its injectivity explicitly.

<a name="s43" id="s43"></a>

## 43. The uncovered calibration point

[`LigoSpecious.ligo_calibration_scope_not_exact`](../RequestProject/LIGO_published_ledger.lean#L334)

Define the stated-domain point

```text
u=(840,540,0).
```

It belongs to statedDomain because

```text
10≤840≤1000,

540≤990,

0≤990.
```

It does not belong to calibratedRegion.

Its q coordinate is not 1000.

Its first spin coordinate satisfies

```text
540>500.
```

Therefore neither branch of the calibrated-region disjunction can hold.

Suppose a proposed target range Bcal contains u and an ExactCalibration through calEmbed exists onto that range.

Its surjectivity property supplies a CalPoint a with

```text
calEmbed(a)=u.
```

Equality of underlying values forces a to have coordinates (840,540,0).

But a's subtype membership then proves that (840,540,0) belongs to calibratedRegion, contradicting the preceding exclusion.

Hence no exact calibration through calEmbed exists onto any range containing this point.

<a name="s44" id="s44"></a>

## 44. General spin exclusion from the calibrated region

[`LigoSpecious.not_calibrated_of_spin`](../RequestProject/LIGO_published_ledger.lean#L351)

Let q,a1,a2 : Nat satisfy

```text
q<1000,
```

and

```text
500<a1 or 500<a2.
```

Assume calibratedRegion(q,a1,a2).

Its central disjunction has two cases.

First case:

```text
q=1000.
```

This contradicts q<1000.

Second case:

```text
a1≤500 and a2≤500.
```

If 500<a1, the first inequality is contradicted.

If 500<a2, the second inequality is contradicted.

Every case is impossible.

Therefore

```text
not calibratedRegion(q,a1,a2)
```

under the stated hypotheses.

<a name="s45" id="s45"></a>

## 45. The injection and credible-spin grid certificates

[`LigoSpecious.ligo_calibration_injection_outside`](../RequestProject/LIGO_published_ledger.lean#L367) · [`LigoSpecious.ligo_calibration_credible_spin_bounds`](../RequestProject/LIGO_published_ledger.lean#L377)

The point

```text
(810,340,670)
```

belongs to statedDomain:

```text
10≤810≤1000,

340≤990,

670≤990.
```

It lies outside calibratedRegion because

```text
810<1000,
```

and

```text
670>500.
```

The point

```text
(810,340,500)
```

lies inside calibratedRegion:

```text
125≤810≤1000,

340≤500,

500≤500,
```

and both amplitudes are at most 990.

For every q : Nat satisfying

```text
640≤q≤980,
```

we have q<1000.

Each of the primary amplitudes

```text
540,740,650
```

exceeds 500.

Therefore each point

```text
(q,540,0),

(q,740,0),

(q,650,0)
```

lies outside calibratedRegion.

Each of the secondary amplitudes

```text
700,780,750
```

also exceeds 500.

Therefore each point

```text
(q,0,700),

(q,0,780),

(q,0,750)
```

lies outside calibratedRegion.

The proof applies to every natural q in the stated interval.

<a name="s46" id="s46"></a>

## 46. The exact marginal-tail theorem

[`LigoSpecious.ligo_calibration_posterior_mass_outside`](../RequestProject/LIGO_published_ledger.lean#L392)

Let

```text
F : Int → Int
```

be nondecreasing:

```text
for every x,y,
x≤y implies F(x)≤F(y).
```

Let b : Int satisfy

```text
500<b,
```

and assume

```text
F(b)=90.
```

From 500<b, obtain 500≤b.

Monotonicity gives

```text
F(500)≤F(b).
```

Substitute F(b)=90:

```text
F(500)≤90.
```

Subtract from 100:

```text
100-F(500)≥10.
```

Thus the exact conclusion is

```text
10≤100-F(500).
```

This is the proposition proved by

```text
LigoSpecious.ligo_calibration_posterior_mass_outside.
```

When F is a cumulative distribution expressed in percentage units, 100-F(500) is the corresponding marginal mass above 500, in those same units.

The theorem retains the monotonicity, threshold, and F(b)=90 hypotheses exactly as displayed.

<a name="s47" id="s47"></a>

## 47. Assembly of the Part 2 conclusions

[`Measure.exact_calibration_implies_isomorphic_transposition`](../RequestProject/Measurement.lean#L339) · [`LigoSpecious.fibre_obstructs`](../RequestProject/LIGO_specious_measures.lean#L95) · [`LigoSpecious.ligo_calibration_scope_not_exact`](../RequestProject/LIGO_published_ledger.lean#L334)

The measurement construction proves that the supplied ExactCalibration data determine a two-sided structure-preserving isomorphism with the restricted calibrated carrier.

The general obstruction theorems show how explicit failures of operation preservation, relation preservation, relation reflection, injectivity, or range coverage exclude the corresponding calibration claims.

The concrete applications provide the required witnesses or arithmetic separations:

```text
Integer model difference:
    distinct common-level pairs with equal differences.

Sum-and-difference completion:
    an explicit inverse on the parity range.

Error-width relation:
    common errors beyond the width with zero difference.

Integer-scaled chiP:
    exact conditional numerator bounds;
    azimuth collisions;
    a primary-amplitude fibre through 83;
    a strict threshold from 84.

Two-bin posterior combination:
    explicit redistribution fibres and the bounded
    monotone-function segment.

Four-to-two mode projection:
    equal retained modes with unequal discarded modes.

Gaussian exponent:
    sign-related residuals with equal squared sums;
    a concrete failure of addition preservation.

Six-to-four spin projection:
    an explicit surjection with nonzero kernel directions
    and distinct states sharing the same image.

Printed addition intervals:
    strict separation of the sum of separate readings
    from the designated reading of the source sum.

Printed redshift intervals:
    four strict endpoint separations, each retaining its
    source-relation and interval hypotheses.

Threshold verdict:
    the exact true and false intervals of the defined rule.

Calibration-domain inclusion:
    injectivity and valid comparison for the bare signature,
    together with an explicit uncovered target point.

Marginal tail:
    the inequality 10≤100-F(500), derived from the stated
    monotonicity and threshold premises.
```

The mathematical proofs above follow the definitions and quantified hypotheses of the saved Lean declarations.

[Return to contents](#contents) · [Verification and reproducibility](../VERIFICATION.md)
