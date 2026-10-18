# Voisin's degree-ten reduction: notes on the formalization

Mathematical companion to the Cassels-Swinnerton-Dyer formalization. Prepared October 18, 2026.

[PDF edition](voisin-formalization-notes.pdf) · [Repository overview](../README.md) · [Manuscript coverage](../paper/COVERAGE.md)

## Purpose, version, and scope

Claire Voisin's *Rank 2 vector bundles and degrees of points of del Pezzo surfaces* supplies a central ingredient of this project: the elimination of degree ten from Coray's degree-1,4,10 alternative for smooth cubic surfaces in characteristic zero. The rank-two vector-bundle construction and residual-intersection strategy are Voisin's. The formalization implements the part needed for the Cassels-Swinnerton-Dyer argument.

This note concerns **arXiv:2509.17996v2, dated February 20, 2026**. Page numbers refer to that 23-page PDF, not the journal pagination. The observations below were checked against the archived PDF and TeX source. They are project notes, not an author-issued erratum; no assertion is made about corrections in other versions.

Three distinctions matter. The degree-ten calculation contains two identifiable notation slips. Several geometric steps need explicit constructions and hypotheses in Lean, even where the paper already gives the mathematical strategy. A few observations about statements outside the required reduction are recorded separately, without claiming that they have been formalized. These distinctions preserve the difference between correcting a displayed expression, expanding a proof, and verifying a broader theorem.

The completed Lean result constructs an **effective degree-four zero-cycle from a degree-ten closed point** on a smooth cubic surface in characteristic zero. This is enough for the project. It does not certify every Chow-group statement, the stable-irrationality arguments, or the degree-two and degree-one del Pezzo results in Voisin's paper.

## 1. The degree-ten calculation

Write $H=\mathcal O_S(1)$ and $h=H^2\in\operatorname{CH}_0(S)$, so $\deg h=3$. Here an effective class means a class admitting an effective representative; subtraction of classes need not be subtraction of nested subschemes.

The proof of Proposition 4.3(a), p. 18, starts from an effective class $z$ of degree ten. Its intended sequence is:

- $a=z+2h$, of degree $16$, is effective by addition.
- $b=9h-a=7h-z$, of degree $11$, is effective by Lemma 3.6 with $3H$.
- $c=b-h=6h-z$, of degree $8$, is effective by Proposition 3.2 with $(l,d,s)=(2,11,3)$.
- $w=4h-c=z-2h$, of degree $4$, is effective by Lemma 3.6 with $2H$.

The section dimensions are $h^0(2H)=10$ and $h^0(3H)=19$. Thus the first residual step uses $16\leq19-2$, the middle step uses $10<11$ and $19-11=8\geq2\cdot3$, and the final step uses $8=10-2$.

In the paper's notation, $z'=a$ and $z''=b$. The subtraction from $h^0(3H)$ must therefore use $\deg z''=11$, rather than $\deg z'=16$. The subsequent degree-eight expression must refer to $z''-h$, rather than $z''$. These two replacements make the displayed numbers agree with the surrounding construction. They leave the degree-ten reduction intact and yield

$$
z=w+2h,\qquad \deg w=4.
$$

The paper itself records this class relation in equation (50). The correction is therefore consistent with its later use, rather than a proposed change of conclusion.

**Formalization.** [VoisinCycleArithmetic.lean](../PfaffianDescent/VoisinCycleArithmetic.lean) separates effective cycles, their degrees, and equalities modulo curve-family relations. Its arithmetic results take the appropriate geometric constructions as inputs. The completed geometric route supplies the effective degree-four conclusion through [VoisinDegreeElevenActualNativeEffectiveEightFactory.lean](../PfaffianDescent/VoisinDegreeElevenActualNativeEffectiveEightFactory.lean). The latter conclusion should not be advertised as a separate formal proof of equation (50) for every initial effective class: it retains the existence and degree needed for the point theorem.

## 2. The Serre construction and finite zero loci

### What the paper establishes and what must be retained

Lemma 3.1 uses a closed-point hypothesis in the Serre construction. A general effective cycle can have several residue fields and multiplicities, so it cannot simply be substituted for that closed point. Proposition 3.2 addresses this by passing to a generic universal subscheme and then specializing. Starting with that generic object makes the field hypothesis explicit from the outset.

The other essential distinction is between a nonzero section and a section with finite zero locus. For the needed degree-eleven construction, the bundle has nine global sections. Vanishing at three points imposes at most six linear conditions, which gives candidate sections. This dimension count alone does not exclude a curve in the zero locus of the chosen section. Lemma 3.3, pp. 12-14, supplies the geometric argument; Example 3.5 explicitly illustrates why nongeneric data can behave differently.

The paper already chooses a maximal vanishing curve and uses the symmetry of the unordered points. A fully explicit treatment must retain the whole divisorial zero locus and justify the choices made over the parameter field. The formalization makes these dependencies explicit while preserving the geometric purpose of the construction.

### How the formalization proceeds

The Lean development proves that the generic degree-eleven configuration is one closed point with a field as its coordinate algebra. It constructs the corresponding Serre bundle, its nine-dimensional section space, the evaluation maps at the marked points, and a parameter giving the required finite residual. The construction takes place on the original cubic after the stated field changes, with the evaluation maps tied to that bundle throughout.

The resulting degree-eight object is an actual finite subscheme and then an effective cycle. The required regularity and parameter-existence assertions are proved before the residual degree is extracted. This implements the specific geometric input $(l,d,s)=(2,11,3)$; it is not a claim to formalize every numerical instance of Lemma 3.3.

**Lean entry points.** [The generic configuration is one closed point](../AllCharacteristics/VoisinGenericCubicPoint.lean), [construction of the generic-eleven Serre data and good parameter](../PfaffianDescent/CubicElevenPointGroundSerreGoodFactory.lean), [passage to the inner generic-three configuration](../PfaffianDescent/CubicElevenPointGroundSerreGoodInnerResidualCycle.lean), and [extraction of the actual residual degree-eight cycle](../PfaffianDescent/SerreActualCubicGroundFamilyNativeSelectedResidualCycle.lean).

## 3. Proper intersections and the scope of a genericity argument

Lemma 3.6, pp. 14-15, gives residual effectivity on a smooth projective surface with a very ample line bundle. Having two independent sections through the prescribed subscheme is not sufficient by itself: the corresponding divisors must have no common component.

Its proof invokes equation (28), whose earlier justification uses very general points and the countability of the Picard group of a cubic surface. The lemma is stated for general smooth projective surfaces, where that countability is not available in the same form. Thus that invocation needs an additional argument in the stated generality. This observation concerns the justification, not a counterexample to the residual-effectivity statement.

A way to supply the general argument in characteristic zero is to use incidence with a smooth integral member of the very ample system. If $d\leq h^0(H)-2$, choose $d$ points on such a member that impose independent conditions on the remaining sections. The incidence space over the independent-condition locus is a projective bundle, and the existence of a smooth integral member is a nonempty open condition there. Consequently a general tuple lies on a smooth integral member $C_1$. A second, nonproportional member $C_2$ through the tuple intersects $C_1$ properly. Their residual intersection gives the generic effective class, which can then be specialized. This is a mathematical explanation of how to extend the proof; a general-surface formalization of this lemma is not claimed here.

For the cubic cases used in this project, Lean instead constructs the particular auxiliary equations and proves the necessary regularity and finiteness properties. The first residual has total intersection length $27$ and prescribed length $16$, leaving degree $11$; the final quadric intersection has total length $12$ and prescribed length $8$, leaving degree $4$. The finite-scheme and cycle calculations retain multiplicities.

**Lean entry points.** [Generic cubic residual construction](../PfaffianDescent/VoisinDegreeTenSelectedAvoidanceGridGenericComplementCycle.lean), [specialization of its effective degree-eleven cycle](../PfaffianDescent/VoisinDegreeTenSelectedAvoidanceGridSpecializedComplementCycle.lean), and [assembly of the degree-eleven/eight/four branches](../PfaffianDescent/VoisinDegreeTenSelectedAvoidanceGridFactoryBridge.lean). These are constructions for the cubic reduction, not an appeal to the general-surface statement as an assumption.

## 4. Specialization to the prescribed data

Proposition 3.2 and Lemma 3.6 explicitly invoke specialization. The formalization follows that strategy. A dense open set of good configurations need not contain a prescribed configuration, and a rational map from a higher-dimensional parameter space need not be defined at every point. Consequently the generic construction and its passage back to the ground field are separate proof steps.

Lean constructs the unordered configuration spaces and proves the regularity needed at the specialization point. A finite étale subscheme supplies that point of the parameter space. The target for specialization is the full proper unordered-tuple space, which permits collisions; requiring the output to stay in the distinct-point open would be too strong. The cycle construction records multiplicities and preserves total degree during this passage.

In the middle step there are two parameter fields: the generic degree-eleven field and, over it, the generic degree-three field. The construction produces a degree-eight cycle over the second field. Two proved specialization steps return an effective cycle of degree eight on the original surface. Characteristic zero ensures the separability used to represent closed points by finite étale data.

The completed route only needs preservation of effectivity and degree here. It therefore does not claim, on the strength of these specialization modules alone, a full formal construction of Chow specialization preserving every class identity in the paper.

**Lean entry points.** [Specialization from finite étale configurations](../AllCharacteristics/FiniteEtaleConfigurationGenericSpecialization.lean), [specialization of arbitrary effective cycles with multiplicities](../PfaffianDescent/VoisinEffectiveCycleGenericSpecialization.lean), and [the two-stage specialization](../PfaffianDescent/VoisinDegreeTenSelectedAvoidanceGridTwoStageCycleSpecialization.lean).

## 5. Selected observations outside the formalized reduction

These points help delimit what the repository verifies. They are not additional Lean results or a comprehensive list of editorial changes.

**Corollary 1.3, p. 2.** The dimension hypothesis $n\geq3$ from Theorem 1.1 should be retained. For a smooth plane cubic over $\mathbb C$, effective divisors equivalent to the hyperplane class form a projective plane inside the three-dimensional symmetric cube. They are not dense there, and they are line sections. This identifies why the hypothesis matters. Cubic surfaces, the setting used here, already satisfy it.

**Corollary 1.14(b), p. 19.** In the sign-conversion argument, if $\deg x_4=4$ and $\deg z'=e\leq4$, then

$$
\deg(4h-x_4-z')=8-e.
$$

This is four when $e=4$, but larger when $e<4$. The smaller degrees therefore require separate treatment if the new effective remainder is to have degree at most four. For $e=0,1,2,3,4$, suitable classes are respectively $0$, $h-z'$, $h-z'$, $2h-z'$, and $4h-x_4-z'$. Their degrees are $0,2,1,3,4$. The first two nonzero small-degree constructions use residual line intersections; the degree-three case can be obtained on a smooth plane section followed by specialization; the degree-four case uses the genus-four curve in the paper. The associated multiples of $h$ and $x_4$ are absorbed into the other coefficients. This explains how the degree bookkeeping can be completed, without claiming a formal verification of the whole corollary or its subsequent field-of-definition arguments.

**Sections 5 and 6.** The degree-two and degree-one del Pezzo analogues require their own geometric estimates, in addition to the changed Riemann-Roch numbers. They are outside the completed cubic reduction. This note draws no conclusion about their validity from their absence in the Lean project.

## 6. What the completed endpoint says

The theorem `PfaffianDescent.voisinDegreeTenSelectedAvoidance_actualNative_effectiveDegreeFourFactory` in [VoisinDegreeElevenActualNativeEffectiveEightFactory.lean](../PfaffianDescent/VoisinDegreeElevenActualNativeEffectiveEightFactory.lean) proves the interface `VoisinDegreeTenEffectiveDegreeFourFor`. Its hypotheses are a characteristic-zero field, a nonzero homogeneous cubic defining a smooth surface, and a closed point of residue degree ten. Its conclusion is an effective zero-cycle of degree four on that surface. No external Voisin geometric conclusion is an input to this endpoint.

The [interface definition](../AllCharacteristics/VoisinDegreeTenReduction.lean) and [main-proof assembly](../AllCharacteristics/TwoProofs.lean) show precisely how this result is consumed. Combined with the internally proved Coray reduction, it supplies the characteristic-zero input to the project's main argument. The subsequent degree-four-to-rational-point construction belongs to this project and should not be attributed to Voisin's Theorem 1.5.

The repository's [verification instructions](../verification/README.md) and [coverage table](../paper/COVERAGE.md) explain the broader checks. The successful main Comparator run concerns the declared Cassels-Swinnerton-Dyer challenge, not a challenge asserting all statements of Voisin's paper. Mathematical comparison of the paper, this explanation, and the Lean theorem types remains part of reviewing the formalization.

## References

- C. Voisin, *Rank 2 vector bundles and degrees of points of del Pezzo surfaces*, [arXiv:2509.17996v2](https://arxiv.org/abs/2509.17996v2), February 20, 2026. [Reviewed PDF](https://arxiv.org/pdf/2509.17996v2) and [TeX source](https://arxiv.org/src/2509.17996v2). Journal reference: J. Reine Angew. Math. 836 (2026), 303-327. The version-specific observations above concern the arXiv text.
- J.-L. Colliot-Thélène, *Zéro-cycles sur les surfaces de del Pezzo (Variations sur un thème de Daniel Coray)*, L'Enseignement Mathématique 66 (2020), 447-487, [arXiv:2005.06876](https://arxiv.org/abs/2005.06876). Relevant background includes Lemma 2.10 and Proposition 2.11 on effectivity and specialization, also cited in the mathematical discussion underlying this project.
- [Companion notes on Coray's reduction](../coray-paper/README.md).

The Markdown and PDF editions contain the same explanatory text. Source links in the PDF point to this project's GitHub repository; the Markdown links resolve within the checkout.
