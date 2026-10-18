# Coray's degree reduction: notes on the formalization

Mathematical companion to the Cassels-Swinnerton-Dyer formalization. Prepared October 18, 2026.

[PDF edition](coray-formalization-notes.pdf) · [Repository overview](../README.md) · [Manuscript coverage](../paper/COVERAGE.md)

## Purpose and scope

Coray's *Algebraic points on cubic hypersurfaces* (1976) provides the degree-reduction argument underlying an important part of this project. Theorem 7.1 states that a smooth cubic surface over a perfect field with a point over an extension of degree prime to three has a point over an extension of degree 1, 4, or 10. The formalization retains this conclusion and much of the descent strategy: choose a point of least degree prime to three, construct auxiliary curves, and use divisors and degree bounds to obtain a smaller point outside the exceptional degrees.

This note explains several places where a modern, fully explicit proof benefits from additional distinctions or arguments. They have different statuses: an incidence count does not by itself justify a point-degree inference; normalization requires care at the boundary of a genus estimate; and an infinitude statement needs an infinite-field hypothesis. None of these observations is a counterexample to Theorem 7.1. They are recorded to explain the mathematical choices in the formalization, without making a claim of priority for the observations.

The completed internal Coray endpoint in this repository concerns **smooth cubic surfaces in characteristic zero**, which is the reduction required by the project's lifting argument. It is not a formal verification of every assertion in Coray's paper, or a separate formalization of Theorem 7.1 over every perfect field. Printed page numbers below refer to Coray's original article, pp. 267-296.

## 1. Incidence counts and degrees of closed points

### The distinction in the printed argument

In case (B)(ii), pp. 291-292, the proof considers conjugate geometric components and the conjugates of a prescribed closed point. Let $r$ be the number of components, $d$ the degree of the original point, and $\nu$ the number of its geometric conjugates on one component. If each point lies on one or two components, double counting gives $r\nu=d$ or $r\nu=2d$.

These identities count incidences. To identify $\nu$ with the degree of a **single closed point** over the component's field of definition requires the stabilizer of that component to act transitively on the incident points. In the one-component-through-each-point situation, uniqueness gives the required implication. In the two-component situation, transitivity on all points and on all components separately does not, by itself, supply it. The transition on p. 292 therefore needs an additional argument or a formulation using the whole cycle.

For an elementary illustration of the distinction, let a cyclic group of order four act regularly on four points and through its quotient of order two on two components, with every point incident to both components. Both actions are transitive. A component stabilizer nevertheless has two orbits of size two on the four points. This is an example about the group-theoretic inference, not a geometric counterexample to Coray's theorem.

### How the formalization proceeds

The formalization constructs the component over its field of definition $M$ and the **entire finite incidence scheme** over the original point. Its fundamental cycle retains every closed-point contribution and its multiplicity. No assertion that the whole incidence is one closed point is needed.

Writing $r=[M:k]$, $d=[\kappa(P):k]$, and letting $\nu$ and $s$ denote the ranks of that incidence scheme over $M$ and $\kappa(P)$, respectively, the formal argument proves the identity

$$
r\nu=ds.
$$

Here ranks include scheme-theoretic multiplicities; they are not silently replaced by cardinalities. For each closed point $Q$ in the incidence support, the residue-field tower also gives

$$
d\mid r[\kappa(Q):M].
$$

These identities, together with the geometric bounds, provide the degree control needed for the descent. The subsequent construction uses divisors and sections on the normalization and produces an effective cycle; a suitable closed point is then extracted and mapped back to the original cubic surface. This supplies explicit cycle and residue-degree arguments without requiring the single-orbit inference.

**Lean entry points.** [Entire incidence cycle](../PfaffianDescent/CorayEntireModelIncidenceCycle.lean), [exact rank count](../PfaffianDescent/CorayModelIncidenceExactRankCount.lean), [individual support-point degrees](../PfaffianDescent/CorayModelEntireIncidenceSupportPointDegree.lean), and [construction of a smaller point on the original surface](../PfaffianDescent/CoraySameWitnessOriginalSharpOwnWordPoint.lean).

## 2. Normalization and the boundary of the genus estimate

### What needs to be checked

Riemann-Roch is applied on a regular curve, obtained here by normalization. A closed point on a singular curve cannot automatically be regarded as a point of the same degree on its normalization. Regularity at the prescribed point, or another appropriate degree argument, must first be established.

Let

$$
G_\ell=1+\frac{3\ell(\ell-1)}2.
$$

In the geometrically integral setting, if all $d$ conjugates of the prescribed point were singular, their contributions would give $g\leq G_\ell-d$ for the normalization genus $g$. This is a contradiction when $d>G_\ell$. Footnote 28 occurs in that strict case, and this part of its reasoning is valid. At $d=G_\ell$, however, the same estimate gives only $g\leq0$; the strict-case argument cannot simply be carried over.

Coray's case (A)(iii) supplies additional singularities. Their role must be included when establishing regularity of the original point and making the degree-preserving passage to the normalization. This is a boundary-case clarification, rather than an assertion that footnote 28 is incorrect in its stated case.

### How the formalization proceeds

The boundary construction produces singular support of total degree three, disjoint from the original point. The proof establishes the contribution of these distinct singular points to the normalization quotient. In the geometrically integral description, if the original point were singular as well, the strengthened estimate would be $g\leq G_\ell-d-3<0$.

The Lean implementation also handles an integral curve whose normalization may have a larger field of global constants. It keeps that constants-field dimension in the cohomological estimates instead of assuming geometric integrality. The boundary module derives the needed bounds and proves regularity of the original point. Only then does the normalization-lift theorem construct a point above it with the same ground-field degree.

The resulting divisors, nonzero sections, effective cycles, and degree comparisons are constructed on the specified normalization. In particular, the additional singular cycle is used to obtain the defect estimate; it is not simply lifted as though every singular point had a degree-preserving preimage.

**Lean entry points.** [Additive singularity contributions](../PfaffianDescent/CorayNormalizationDistinctSingularityContribution.lean), [boundary estimates with the full field of constants](../PfaffianDescent/CorayIntegralBoundaryConstants.lean), [degree-preserving lift at a regular point](../PfaffianDescent/CorayOriginalRegularClosedPointNormalizationLift.lean), and [assembly of case (A)(iii)](../PfaffianDescent/CorayIntegralAiiiProducerClosure.lean).

## 3. Components and multiplicities

The component-intersection calculation on p. 292 also calls for a distinction between a reduced union of distinct components and the original complete-intersection scheme. The usual formula relating arithmetic genus, component genera, and pairwise intersection numbers applies to the appropriate reduced union. A repeated component cannot be discarded while retaining all of the original degree data without justification.

The formalization keeps the whole homogeneous complete-intersection ideal. Hilbert-function arguments show that a minimal component with the full intersection degree forces equality with the whole ideal and hence integrality. Consequently, in the nonintegral case, a selected minimal component has strictly smaller degree. This includes a scheme with only one minimal component but nonreduced multiplicity. The nonintegral branch can therefore proceed without replacing the original intersection by its reduced support and assuming its degree is unchanged.

This is an explicit treatment of a scheme-theoretic distinction in the component argument. It does not assert that every auxiliary curve considered in the paper is nonreduced.

**Lean entry points.** [Whole-intersection degree comparison](../PfaffianDescent/CorayOriginalWholeIntersectionMaximalComponentDegree.lean), [smaller-point construction from strict component degree](../PfaffianDescent/CorayStrictOwnComponentOriginalBPoint.lean), and [closure of the nonintegral case](../PfaffianDescent/CorayOriginalLeastPointNonintegralBClosure.lean).

## 4. The field hypothesis in Corollary 6.2

On p. 286, Corollary 6.2 asserts infinitude of rational points on a genus-zero curve of odd degree, and an analogous infinitude for rational pairs in even degree. Read over arbitrary fields, the infinitude assertion needs the qualification that the ground field is infinite. For example, the degree-one curve $\mathbf P^1_{\mathbf F_2}$ has exactly three $\mathbf F_2$-rational points. A positive-dimensional linear system need not have infinitely many rational members over a finite field.

The appropriate qualification concerns infinitude, not the existence statements used in the descent. At the start of the proof of Theorem 7.1, on p. 289, Coray explicitly reduces to an infinite field using an earlier result. Thus this qualification does not invalidate that theorem.

The repository's completed internal Coray theorem assumes characteristic zero, so its ground field is infinite. It does not use the unqualified infinitude assertion over finite fields. This is a scope clarification rather than a replacement of the central degree-reduction argument.

## 5. Relationship to the completed proof

The constructions above feed into the original least-degree descent. The [internal closure](../PfaffianDescent/CorayOriginalDegreeOneCycleInternalClosure.lean) selects a point of least degree prime to three from a degree-one zero-cycle, chooses the interpolation window, and obtains a point of degree 1, 4, or 10. Its hypotheses are the original smooth nonzero homogeneous cubic, a characteristic-zero ground field, and the degree-one cycle; the Coray conclusion is not supplied as an external assumption.

The public endpoint is `AllCharacteristics.internalCorayDegreeOneFourOrTenFor_uniform001`, in [InternalCorayPaperConclusions.lean](../AllCharacteristics/InternalCorayPaperConclusions.lean). It supplies the Coray input used by the subsequent main-theorem proof. The [Coray audit](../AllCharacteristics/ManuscriptVerification/Coray.lean) records the exported type and allowed-axiom and dependency checks. The wider scope is described in the [coverage table](../paper/COVERAGE.md).

The main Cassels-Swinnerton-Dyer Comparator challenge also passed on October 17, 2026: statement matching, the permitted-axiom check, and Lean default kernel replay completed with exit code 0. The [run record](../verification/evidence/comparator-main-20261017.json) identifies the exact configuration. This was a native macOS run with Nanoda disabled and no Linux sandbox. It verifies the main challenge; it is not a separate Comparator certification of every assertion in Coray's paper or of this explanatory note.

For related mathematical context, Colliot-Thélène's later treatment explicitly uses generisation, specialisation, Bertini theorems, and large fields to avoid special cases in Coray's argument. That provides another approach to the degree-reduction theorem; it does not serve here as an attribution of the particular observations above. The source links in this note describe the component, incidence, and normalization constructions in the present Lean development.

## References and checking the sources

- D. F. Coray, *Algebraic points on cubic hypersurfaces*, Acta Arithmetica **30** (1976), 267-296. [DOI and publication record](https://doi.org/10.4064/aa-30-3-267-296). Relevant printed pages: 286, 289-292.
- J.-L. Colliot-Thélène, *Zéro-cycles sur les surfaces de del Pezzo (Variations sur un thème de Daniel Coray)*, L'Enseignement Mathématique **66** (2020), 447-487. [arXiv:2005.06876](https://arxiv.org/abs/2005.06876).
- [Verification instructions](../verification/README.md) explain the pinned Lean/Mathlib versions, source-integrity checks, declaration audits, and the separate Comparator procedure. Human mathematical review remains necessary when comparing a printed assertion with its Lean statement.

The Markdown and PDF editions contain the same explanatory text. Source links in the PDF point to this project's GitHub repository; the Markdown links resolve within the checkout.
