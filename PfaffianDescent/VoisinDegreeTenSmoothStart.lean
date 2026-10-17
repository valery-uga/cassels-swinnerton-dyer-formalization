import PfaffianDescent.VoisinDegreeTenFiniteDatumStart
import PfaffianDescent.GenericRegularSection
import PfaffianDescent.VoisinRegularSequenceCriteria

/-!
# Smooth-cubic start of Voisin's degree-ten residual

On a smooth cubic the surface equation is automatically prime.  The remaining
geometric input is therefore a selected prime intermediate cubic through one
of the actual degree-ten completions, together with transversality of the
three-cubic complete intersection.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [Infinite K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The selected intermediate cubic required after completing a degree-ten
finite datum by two disjoint line sections. -/
def DegreeTenSelectedPrimeIntermediate
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀) : Prop :=
  let D := degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
    D₁₀ C.first C.second C.disjoint_first C.disjoint_second
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
    Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
    ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
    p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
    q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
    q ≠ 0 ∧ IsRelPrime p q ∧
    (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime

/-- A strong uniform transversality condition: every regular third cubic
meets every relatively-prime first cubic transversely.  This is useful for
compatibility with the older uniform residual API, but is stronger than the
source argument, which selects one third cubic through one chosen
rank-sixteen completion.  The source-facing existential datum is
`DegreeTenTransverseCubicIntersectionData`. -/
def CubicTripleIntersectionTransverse
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) : Prop :=
  ∀ (q r : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
    q ≠ 0 → IsRelPrime p q →
    (∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
    Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))

/-- The explicit Jacobian form of the transverse-three-cubic condition.
On every normalized chart, the determinant of the derivatives of `p`, `q`,
`r`, and the chart-normalizing equation must be a unit.  This is the direct
output that a chartwise Bertini transversality calculation can establish. -/
def CubicTripleIntersectionChartJacobianUnit
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) : Prop :=
  ∀ (q r : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
    q ≠ 0 → IsRelPrime p q →
    (∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
    ∀ j : Fin 4,
      IsUnit (tripleCompleteIntersectionChartJacobian p q r hp hq hr j)

/- A pointwise Jacobian certificate is often the natural output of a
   transversality calculation: at every maximal chart point, the selected
   three-equation Jacobian is outside that maximal ideal.  The next theorem
   converts this local formulation to the global unit formulation above. -/
def CubicTripleIntersectionChartJacobianNonvanishing
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) : Prop :=
  ∀ (q r : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
    q ≠ 0 → IsRelPrime p q →
    (∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
    ∀ j : Fin 4,
      ∀ (Q : Ideal (ChartRing
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j))
        [Q.IsMaximal],
        tripleCompleteIntersectionChartJacobian p q r hp hq hr j ∉ Q

theorem CubicTripleIntersectionChartJacobianNonvanishing.toUnit
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hjac : CubicTripleIntersectionChartJacobianNonvanishing p hp) :
    CubicTripleIntersectionChartJacobianUnit p hp := by
  intro q r hq hr hq0 hrel hregular j
  rw [← Ideal.span_singleton_eq_top]
  by_contra htop
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span {tripleCompleteIntersectionChartJacobian p q r hp hq hr j}) htop
  letI : Q.IsMaximal := hQ
  have hmem : tripleCompleteIntersectionChartJacobian p q r hp hq hr j ∈ Q :=
    hle (Ideal.subset_span (by simp))
  exact (hjac q r hq hr hq0 hrel hregular j Q) hmem

/- A unit cannot lie in a proper maximal ideal.  Together with the preceding
   theorem this identifies the chartwise unit and maximal-spectrum
   nonvanishing formulations of the Jacobian condition. -/
theorem CubicTripleIntersectionChartJacobianUnit.toNonvanishing
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hjac : CubicTripleIntersectionChartJacobianUnit p hp) :
    CubicTripleIntersectionChartJacobianNonvanishing p hp := by
  intro q r hq hr hq0 hrel hregular j Q hQ
  letI : Q.IsMaximal := hQ
  intro hmem
  obtain ⟨c, hc⟩ := isUnit_iff_dvd_one.mp
    (hjac q r hq hr hq0 hrel hregular j)
  have hmul :
      tripleCompleteIntersectionChartJacobian p q r hp hq hr j * c ∈ Q :=
    Ideal.mul_mem_right c Q hmem
  have hone : (1 : ChartRing
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr) j) ∈ Q :=
    hc ▸ hmul
  have htop : Q = ⊤ := (Ideal.eq_top_iff_one Q).mpr hone
  exact (Ideal.IsMaximal.ne_top (I := Q) hQ) htop

/-- The chartwise Jacobian condition gives the finite étale transversality
used by the first residual construction. -/
theorem CubicTripleIntersectionChartJacobianUnit.toTransverse
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hjac : CubicTripleIntersectionChartJacobianUnit p hp) :
    CubicTripleIntersectionTransverse p hp := by
  intro q r hq hr hq0 hrel hregular
  exact etale_tripleCompleteIntersection_toBase_of_chartJacobian_isUnit
    p q r hp hq hr (hjac q r hq hr hq0 hrel hregular)

/-- Pointwise nonvanishing of the chart Jacobians directly supplies the
transversality condition used by the first cubic residual step. -/
theorem CubicTripleIntersectionChartJacobianNonvanishing.toTransverse
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hjac : CubicTripleIntersectionChartJacobianNonvanishing p hp) :
    CubicTripleIntersectionTransverse p hp := by
  intro q r hq hr hq0 hrel hregular
  exact etale_tripleCompleteIntersection_toBase_of_chartJacobian_not_mem_maximal
    p q r hp hq hr (hjac q r hq hr hq0 hrel hregular)

/-- The reduced form of the transverse-three-cubic condition.  After the
regular-sequence calculation has made the complete intersection finite,
reducedness is enough for its structure map to be étale in characteristic
zero.  This is the form supplied by a Bertini argument. -/
def CubicTripleIntersectionReduced
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) : Prop :=
  ∀ (q r : MvPolynomial (Fin 4) K)
    (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
    q ≠ 0 → IsRelPrime p q →
    (∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
    AlgebraicGeometry.IsReduced
      (scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))

/-- A reduced regular three-cubic intersection is finite étale in
characteristic zero. -/
theorem CubicTripleIntersectionReduced.toTransverse
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hreduced : CubicTripleIntersectionReduced p hp) :
    CubicTripleIntersectionTransverse p hp := by
  intro q r hq hr hq0 hrel hregular
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  have hp0 : p ≠ 0 :=
    isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hq (by decide) hrel.symm
  letI : IsFinite (toBase I) :=
    triple_cubic_intersection_finite p q r hp hq hr hp0 hq0 hrel hregular
  letI : AlgebraicGeometry.IsReduced (scheme I) :=
    hreduced q r hq hr hq0 hrel hregular
  exact finiteScheme_etale_of_isReduced (toBase I)

/-- The part of Voisin's first cubic choice that follows formally from a
smooth cubic and a degree-ten finite datum.  It records the two avoiding
line sections, normalized coordinates on their rank-sixteen completion, and
an auxiliary cubic through that completion which is relatively prime to the
surface equation.  Primality of the intermediate curve is deliberately not a
field: that is the remaining Bertini input. -/
structure DegreeTenRegularCubicSectionData
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) where
  completion : DegreeTenRankSixteenCompletion p hp D₁₀
  coordinates :
    let D := completion.datum
    letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
    letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
      ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
      p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
      q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
      q ≠ 0 ∧ IsRelPrime p q

/-- The first cubic through a degree-ten completion together with the
normalized chart of the actual completed finite subscheme.  The chart is
retained because it turns vanishing of the first and third cubics into a
closed immersion into their complete intersection, rather than only a
coordinate-level incidence statement. -/
structure DegreeTenRegularCubicSectionEmbeddingData
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) where
  completion : DegreeTenRankSixteenCompletion p hp D₁₀
  q : MvPolynomial (Fin 4) K
  hq : q.IsHomogeneous 3
  hq0 : q ≠ 0
  hrel : IsRelPrime p q
  chart :
    let D := completion.datum
    letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
    letI : IsAffine D.val.subscheme :=
      isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    letI := finiteSchemeCoefficientAlgebra
      (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (z : CoordinateRing (equationIdeal p hp))
      (hz : z ∈ grading (equationIdeal p hp) 1)
      (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (he : ∀ s ∈ (equationIdeal p hp).toIdeal,
        (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) s = 0)
      (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
        (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) he) z = 1),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
      q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
      linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
        D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι

/-- An embedded first cubic whose cubic--cubic intersection is prime supplies
the selected-prime intermediate datum used by the first residual.  The
normalized chart already contains a homogeneous linear representative, so no
separate affine-coordinate hypothesis is needed. -/
theorem DegreeTenSelectedPrimeIntermediate.ofEmbeddingData
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hprime : (Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    DegreeTenSelectedPrimeIntermediate p hp D₁₀ S.completion := by
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hqvan, _⟩ :=
    by simpa only [D] using S.chart
  have hzmem := hz
  change z ∈ AllCharacteristics.quotientGrading
    (MvPolynomial.homogeneousSubmodule (Fin 4) K)
    (equationIdeal p hp).toIdeal 1 at hzmem
  obtain ⟨ell, hell, hellz⟩ := hzmem
  have hellone : ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 := by
    rw [← hellz] at hzOne
    exact hzOne
  have hpx : p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 :=
    he p (Ideal.subset_span (Set.mem_singleton p))
  refine ⟨x, ell, S.q, hxsurj, hell, hellone, hpx,
    S.hq, hqvan, S.hq0, S.hrel, hprime⟩

/-- A prime selected cubic section in the cubic surface coordinate ring gives
the integral intermediate curve needed by the degree-ten residual.  This is
the direct algebraic output expected from the Bertini irreducibility step. -/
theorem DegreeTenSelectedPrimeIntermediate.ofEmbeddingData_of_quotientPrime
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hqprime : Prime (Ideal.Quotient.mk
      (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) S.q)) :
    DegreeTenSelectedPrimeIntermediate p hp D₁₀ S.completion := by
  exact DegreeTenSelectedPrimeIntermediate.ofEmbeddingData p hp D₁₀ S
    (ideal_span_pair_isPrime_of_quotient_mk_prime p S.q hpprime hqprime)

/-- The associated-component assertion needed after a first cubic has been
selected.  Unlike the uniform finite-rank packaging, this records only the
one normalized chart and the one cubic--cubic curve used by Voisin's actual
residual construction.  Lemma 3.3 is precisely the geometric source of the
last field. -/
def DegreeTenRegularCubicSectionSelectedAvoidance
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀) : Prop :=
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∃ (z : CoordinateRing (equationIdeal p hp))
    (hz : z ∈ grading (equationIdeal p hp) 1)
    (x : Fin 4 → Γ(D.val.subscheme, ⊤))
    (he : ∀ s ∈ (equationIdeal p hp).toIdeal,
      (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) s = 0)
    (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) he) z = 1),
    Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
    S.q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
    linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
      D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ∧
    ∀ P ∈ associatedPrimes
      (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K)))
      (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))),
      ∃ r ∈ homogeneousVanishingPolynomialSubmodule
        (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3,
        Ideal.Quotient.mk (Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))) r ∉ P

/-- The finite-rank version of the selected-cubic base-locus condition.
It is restricted to the first cubic and normalized chart that occur in the
actual construction, so it is exactly the linear-algebraic form of the
associated-component condition in `DegreeTenRegularCubicSectionSelectedAvoidance`. -/
def DegreeTenRegularCubicSectionSelectedFinrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀) : Prop :=
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∃ (z : CoordinateRing (equationIdeal p hp))
    (hz : z ∈ grading (equationIdeal p hp) 1)
    (x : Fin 4 → Γ(D.val.subscheme, ⊤))
    (he : ∀ s ∈ (equationIdeal p hp).toIdeal,
      (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) s = 0)
    (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) he) z = 1),
    Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
    S.q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
    linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
      D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ∧
    let I := Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))
    let W := homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3
    let qmap : MvPolynomial (Fin 4) K →ₗ[K]
        MvPolynomial (Fin 4) K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
    let V : Submodule K (MvPolynomial (Fin 4) K ⧸ I) := W.map qmap
    ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
        (MvPolynomial (Fin 4) K ⧸ I),
      Module.finrank K ((P.restrictScalars K).comap V.subtype) <
        Module.finrank K V

/-- Associated-component avoidance for the selected cubic implies the exact
finite-rank condition consumed by the regular-third-cubic selector. -/
theorem DegreeTenRegularCubicSectionSelectedAvoidance.finrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (havoid : DegreeTenRegularCubicSectionSelectedAvoidance p hp D₁₀ S) :
    DegreeTenRegularCubicSectionSelectedFinrankDrop p hp D₁₀ S := by
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint, havoid⟩ :=
    by simpa only [D] using havoid
  refine ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint, ?_⟩
  exact (avoids_associatedPrimes_mod_ideal_iff_finrank_drop
    (Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K)))
    (homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3)).mp havoid

/-- The selected finite-rank condition is equivalent to the natural
associated-component condition; it does not add a separate hypothesis to
Voisin's Lemma 3.3. -/
theorem DegreeTenRegularCubicSectionSelectedAvoidance.ofFinrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hdrop : DegreeTenRegularCubicSectionSelectedFinrankDrop p hp D₁₀ S) :
    DegreeTenRegularCubicSectionSelectedAvoidance p hp D₁₀ S := by
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint, hdrop⟩ :=
    by simpa only [D] using hdrop
  refine ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint, ?_⟩
  exact (avoids_associatedPrimes_mod_ideal_iff_finrank_drop
    (Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K)))
    (homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3)).mpr hdrop

/-- Equivalent selected-cubic formulations of the remaining base-locus input
in Voisin's first residual construction. -/
theorem degreeTenRegularCubicSection_selectedAvoidance_iff_finrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀) :
    DegreeTenRegularCubicSectionSelectedAvoidance p hp D₁₀ S ↔
      DegreeTenRegularCubicSectionSelectedFinrankDrop p hp D₁₀ S := by
  constructor
  · exact DegreeTenRegularCubicSectionSelectedAvoidance.finrankDrop p hp D₁₀ S
  · exact DegreeTenRegularCubicSectionSelectedAvoidance.ofFinrankDrop p hp D₁₀ S

/-- If the one cubic--cubic intersection selected by the construction is
integral, then the rank-sixteen section-space estimate already proves the
selected associated-component condition.  Indeed the quotient has only its
zero associated prime, and the cubic kernel contains a third cubic outside
the span of the two chosen equations.  This gives a Bertini-style route to
the first residual that does not retain a separate base-locus premise in the
prime-intermediate branch. -/
theorem DegreeTenRegularCubicSectionSelectedAvoidance.ofPrimeIntermediate
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hprime : (Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    DegreeTenRegularCubicSectionSelectedAvoidance p hp D₁₀ S := by
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint⟩ :=
    by simpa only [D] using S.chart
  have hpx : p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 :=
    he p (Ideal.subset_span (Set.mem_singleton p))
  have hsections : 3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx :=
    cubic_degree_sixteen_vanishing_sections_finrank p hp hne x hpx
      ((finiteSchemeCoefficient_finrank
        (D.val.subschemeι ≫ hypersurfaceToBase p hp)).trans
        (AllCharacteristics.finiteSubschemeDatum_finiteSchemeRank
          (hypersurfaceToBase p hp) D))
  obtain ⟨r, hrW, hrnot⟩ :=
    exists_cubic_vanishing_section_not_mem_span_pair p S.q hp x hpx S.hq hqvan hsections
  refine ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint, ?_⟩
  intro P hP
  haveI : IsDomain (MvPolynomial (Fin 4) K ⧸
      Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hprime
  have hPbot : P = ⊥ := associatedPrimes_eq_bot_of_domain P hP
  refine ⟨r, hrW, ?_⟩
  intro hrP
  have : Ideal.Quotient.mk (Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))) r = 0 := by
    rw [hPbot] at hrP
    simpa using hrP
  exact hrnot (Ideal.Quotient.eq_zero_iff_mem.mp this)

/-- The prime-intermediate branch also provides the selected finite-rank
form used by the residual theorem. -/
theorem DegreeTenRegularCubicSectionSelectedFinrankDrop.ofPrimeIntermediate
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hprime : (Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))).IsPrime) :
    DegreeTenRegularCubicSectionSelectedFinrankDrop p hp D₁₀ S :=
  (DegreeTenRegularCubicSectionSelectedAvoidance.ofPrimeIntermediate
    p hp hne D₁₀ S hprime).finrankDrop p hp D₁₀ S


/-- The older uniform finite-rank condition on a completion restricts to the
selected first cubic and its retained normalized chart. -/
theorem DegreeTenRegularCubicSectionSelectedFinrankDrop.ofCompletionFinrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hdrop : DegreeTenCompletionThirdCubicFinrankDrop p hp D₁₀ S.completion) :
    DegreeTenRegularCubicSectionSelectedFinrankDrop p hp D₁₀ S := by
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint⟩ :=
    by simpa only [D] using S.chart
  refine ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint, ?_⟩
  exact hdrop x hxsurj S.q


/-- The uniform associated-component condition for a degree-ten completion
implies the condition for any one selected regular cubic and its normalized
chart.  This is the precise weakening used by the residual construction: once
the first cubic has been fixed, Lemma 3.3 need only control the one
cubic--cubic curve that occurs there. -/
theorem DegreeTenRegularCubicSectionSelectedAvoidance.ofCompletionAvoidance
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (havoid : DegreeTenCompletionThirdCubicAvoidsAssociatedPrimes
      p hp D₁₀ S.completion) :
    DegreeTenRegularCubicSectionSelectedAvoidance p hp D₁₀ S := by
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint⟩ :=
    by simpa only [D] using S.chart
  refine ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint, ?_⟩
  exact havoid x hxsurj S.q

/-- A smooth nonzero cubic supplies the complete first-section datum after a
degree-ten finite datum is enlarged by two avoiding line sections.  This
discharges all of the first selection except geometric integrality of the
selected cubic--cubic curve. -/
theorem nonempty_degreeTenRegularCubicSectionData_of_smooth_cubic
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) :
    Nonempty (DegreeTenRegularCubicSectionData p hp D₁₀) := by
  obtain ⟨C⟩ := nonempty_degreeTenRankSixteenCompletion_of_smooth_cubic_of_field
    p hp hne D₁₀
  have hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
    principalIdeal_prime_of_irreducible_cubic p
      (irreducible_of_smooth_homogeneous_cubic_of_field p hp hne)
  let D := C.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  refine ⟨{ completion := C, coordinates := ?_ }⟩
  exact cubicFiniteSubscheme_degree_sixteen_regular_cubic_section_of_prime_surface
    p hp hne C.datum.val.subschemeι
    (AllCharacteristics.finiteSubschemeDatum_finiteSchemeRank
      (hypersurfaceToBase p hp) C.datum)
    hprime

/-- Smoothness supplies the first regular cubic together with a normalized
chart that remembers the completed degree-sixteen subscheme itself.  This is
the scheme-level form of the first section selection used by the residual
construction. -/
theorem nonempty_degreeTenRegularCubicSectionEmbeddingData_of_smooth_cubic
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) :
    Nonempty (DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀) := by
  obtain ⟨C⟩ := nonempty_degreeTenRankSixteenCompletion_of_smooth_cubic_of_field
    p hp hne D₁₀
  have hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
    principalIdeal_prime_of_irreducible_cubic p
      (irreducible_of_smooth_homogeneous_cubic_of_field p hp hne)
  let D := C.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hpx, hpoint⟩ :=
    cubicFiniteSubscheme_normalized_chart p hp D.val.subschemeι
  have hsections : 3 ≤ cubicVanishingSectionsModuloEquationFinrank p hp x hpx :=
    cubic_degree_sixteen_vanishing_sections_finrank p hp hne x hpx
      ((finiteSchemeCoefficient_finrank
        (D.val.subschemeι ≫ hypersurfaceToBase p hp)).trans
        (AllCharacteristics.finiteSubschemeDatum_finiteSchemeRank
          (hypersurfaceToBase p hp) D))
  obtain ⟨q, hq, hqvan, hq0, hrel⟩ :=
    exists_regular_cubic_section_data_of_prime_with_nonzero
      p hp hne x hpx hsections hprime
  refine ⟨{
    completion := C
    q := q
    hq := hq
    hq0 := hq0
    hrel := hrel
    chart := ?_
  }⟩
  exact ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint⟩

/-- A smooth cubic already supplies a normalized affine chart and the first
regular cubic through a chosen degree-ten completion.  Thus the
first-residual selection problem reduces to making the intermediate `(p,q)`
intersection prime; relative primality, normalization, and the incidence
condition on the completed degree-sixteen datum are proved here. -/
theorem exists_degreeTen_completion_regular_cubic_section_of_smooth_cubic
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) :
    ∃ C : DegreeTenRankSixteenCompletion p hp D₁₀,
      let D := degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
        D₁₀ C.first C.second C.disjoint_first C.disjoint_second
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q ≠ 0 ∧ IsRelPrime p q := by
  obtain ⟨C⟩ := nonempty_degreeTenRankSixteenCompletion_of_smooth_cubic_of_field
    p hp hne D₁₀
  let D := degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
    D₁₀ C.first C.second C.disjoint_first C.disjoint_second
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  have hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
    principalIdeal_prime_of_irreducible_cubic p
      (irreducible_of_smooth_homogeneous_cubic_of_field p hp hne)
  refine ⟨C, ?_⟩
  simpa only [D] using
    cubicFiniteSubscheme_degree_sixteen_regular_cubic_section_of_prime_surface
      p hp hne D.val.subschemeι
      (AllCharacteristics.finiteSubschemeDatum_finiteSchemeRank
        (hypersurfaceToBase p hp) D)
      hprime

/-- The smooth-cubic degree-ten construction reaches the first residual by
Voisin's actual base-locus route.  The surface primeness and the two avoiding
line sections are supplied here; the remaining inputs are exactly Lemma 3.3's
associated-prime estimate for this completion and the transverse third-cubic
choice.  No selected-prime intermediate curve is assumed. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_of_smooth_cubic_of_completion_and_finrank_drop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (hdrop : DegreeTenCompletionThirdCubicFinrankDrop p hp D₁₀ C)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  have hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
    principalIdeal_prime_of_irreducible_cubic p
      (irreducible_of_smooth_homogeneous_cubic_of_field p hp hne)
  exact exists_degreeTenResidualDatum_and_toBase_etale_of_completion_and_finrank_drop
    p hp hne D₁₀ C hprime hdrop htransverse

/-- The Bertini-facing version of the smooth-cubic first residual.  The only
third-cubic geometric premise is reducedness of the regular intersection;
the finite algebra calculation supplies étaleness internally. -/
theorem
    exists_degreeTenResidualDatum_and_toBase_etale_of_smooth_cubic_of_completion_and_finrank_drop_and_reduced
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (hdrop : DegreeTenCompletionThirdCubicFinrankDrop p hp D₁₀ C)
    (hreduced : CubicTripleIntersectionReduced p hp) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact
    exists_degreeTenResidualDatum_and_toBase_etale_of_smooth_cubic_of_completion_and_finrank_drop
      p hp hne D₁₀ C hdrop
      (CubicTripleIntersectionReduced.toTransverse p hp hreduced)

/-- The smooth-cubic first residual can be stated directly with Voisin's
geometric associated-component avoidance condition.  The conversion to the
finite-rank formulation is internal, so this interface leaves Lemma 3.3 in
its natural form. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_of_smooth_cubic_of_completion_and_avoidsAssociatedPrimes
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (havoid : DegreeTenCompletionThirdCubicAvoidsAssociatedPrimes p hp D₁₀ C)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact
    exists_degreeTenResidualDatum_and_toBase_etale_of_smooth_cubic_of_completion_and_finrank_drop
      p hp hne D₁₀ C havoid.finrankDrop htransverse

/-- Once Voisin's selected intermediate and transversality assertions hold
for one line-section completion of a degree-ten datum, a smooth cubic has an
actual rank-eleven residual datum.  Surface primeness is proved internally
from smoothness. -/
theorem exists_degreeTenResidualDatum_of_smooth_cubic_and_selected_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (hselected : ∃ C : DegreeTenRankSixteenCompletion p hp D₁₀,
      DegreeTenSelectedPrimeIntermediate p hp D₁₀ C)
    (htransverse : CubicTripleIntersectionTransverse p hp) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 := by
  obtain ⟨C, hselected⟩ := hselected
  exact exists_degreeTenAndTwoDegreeThreeResidualDatum_of_selected_prime_intermediate
    p hp hne D₁₀ C.first C.second C.disjoint_first C.disjoint_second hselected htransverse

/-- The same smooth-cubic selected-prime construction retains the étaleness
of the rank-eleven residual, which is the property required by the rank-two
residual step. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_of_smooth_cubic_and_selected_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (hselected : ∃ C : DegreeTenRankSixteenCompletion p hp D₁₀,
      DegreeTenSelectedPrimeIntermediate p hp D₁₀ C)
    (htransverse : CubicTripleIntersectionTransverse p hp) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  obtain ⟨C, hselected⟩ := hselected
  exact exists_finiteSubschemeDatum_degree_sixteen_residual_and_toBase_etale_of_selected_prime_intermediate
    p hp hne C.datum hselected htransverse

/-- A concrete embedded first cubic through the degree-sixteen completion,
whose intersection with the original cubic is integral, directly produces
the finite-etale degree-eleven residual.  This is the selected-prime residual
construction with its intermediate package reconstructed from the retained
coordinate-ring chart. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_of_smooth_cubic_and_embeddingData_prime
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hprime : (Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : CubicTripleIntersectionTransverse p hp) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact exists_degreeTenResidualDatum_and_toBase_etale_of_smooth_cubic_and_selected_prime_intermediate
    p hp hne D₁₀
    ⟨S.completion, DegreeTenSelectedPrimeIntermediate.ofEmbeddingData p hp D₁₀ S hprime⟩
    htransverse


/-- The finite-dimensional base-locus estimate selects the third cubic once
an initial regular cubic through the degree-sixteen completion is fixed.  The
result packages exactly one transverse triple, so later residual arguments do
not need a uniform Bertini assertion over unrelated cubic choices. -/
theorem nonempty_degreeTenTransverseCubicIntersectionData_of_regularCubicSectionData_of_finrank_drop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionData p hp D₁₀)
    (hdrop : DegreeTenCompletionThirdCubicFinrankDrop p hp D₁₀ S.completion)
    (htransverse : CubicTripleIntersectionTransverse p hp) :
    Nonempty (DegreeTenTransverseCubicIntersectionData p hp D₁₀) := by
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficient_finite (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, q, hxsurj, hell, hxell, hpx, hq, hqvan, hq0, hrel⟩ :=
    by simpa only [D] using S.coordinates
  obtain ⟨r, hr, hrvan, hregular⟩ :=
    exists_regular_third_cubic_section_data_of_finrank_drop p q x
      (by simpa only [D] using hdrop x hxsurj q)
  refine ⟨{
    completion := S.completion
    q := q
    r := r
    hq := hq
    hr := hr
    hrel := hrel
    coordinates := ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩
    regular := hregular
    transverse := htransverse q r hq hr hq0 hrel hregular }⟩

/-- The rank-drop estimate upgrades the chart-retaining first cubic selection
to an actual closed immersion of the completed degree-sixteen datum into one
transverse three-cubic complete intersection.  This is the scheme-level first
residual datum used by the first finite-flat pencil. -/
theorem exists_degreeTenTransverseCubicIntersectionEmbeddingData_of_regularCubicSectionEmbeddingData_of_finrank_drop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hdrop : DegreeTenCompletionThirdCubicFinrankDrop p hp D₁₀ S.completion)
    (htransverse : CubicTripleIntersectionTransverse p hp) :
    ∃ T : DegreeTenTransverseCubicIntersectionEmbeddingData p hp D₁₀,
      T.completion = S.completion := by
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint⟩ :=
    by simpa only [D] using S.chart
  obtain ⟨r, hr, hrvan, hregular⟩ :=
    exists_regular_third_cubic_section_data_of_finrank_drop p S.q x
      (by simpa only [D] using hdrop x hxsurj S.q)
  refine ⟨DegreeTenTransverseCubicIntersectionEmbeddingData.ofNormalizedChart
    p S.q r hp S.hq hr D₁₀ S.completion S.hrel hregular ?_ ?_, rfl⟩
  · exact ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hrvan, hpoint⟩
  · exact htransverse S.q r S.hq hr S.hq0 S.hrel hregular

/-- Voisin's selected associated-component condition produces the embedded
three-cubic intersection directly.  This uses neither a rank-drop statement
for unrelated first cubics nor a uniform transversality assertion: the latter
is required only for the regular third cubic selected from this one system. -/
theorem exists_degreeTenTransverseCubicIntersectionEmbeddingData_of_regularCubicSectionEmbeddingData_of_selectedAvoidance
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (havoid : DegreeTenRegularCubicSectionSelectedAvoidance p hp D₁₀ S)
    (htransverse : ∀ (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 3),
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase
        (tripleCompleteIntersectionHomogeneousIdeal p S.q r hp S.hq hr))) :
    ∃ T : DegreeTenTransverseCubicIntersectionEmbeddingData p hp D₁₀,
      T.completion = S.completion := by
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint, havoid⟩ :=
    by simpa only [D] using havoid
  obtain ⟨r, hr, hrvan, hregular⟩ :=
    exists_regular_third_cubic_section_data_of_avoids_associatedPrimes
      p S.q x havoid
  refine ⟨DegreeTenTransverseCubicIntersectionEmbeddingData.ofNormalizedChart
    p S.q r hp S.hq hr D₁₀ S.completion S.hrel hregular ?_ ?_, rfl⟩
  · exact ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hrvan, hpoint⟩
  · exact htransverse r hr hregular

/-- The selected-cubic associated-component condition and one selected
transverse complete intersection yield Voisin's finite étale degree-eleven
residual, disjoint from the completed degree-sixteen datum. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_regularCubicSectionEmbeddingData_of_selectedAvoidance
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (havoid : DegreeTenRegularCubicSectionSelectedAvoidance p hp D₁₀ S)
    (htransverse : ∀ (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 3),
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase
        (tripleCompleteIntersectionHomogeneousIdeal p S.q r hp S.hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
          S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  obtain ⟨T, hTcompletion⟩ :=
    exists_degreeTenTransverseCubicIntersectionEmbeddingData_of_regularCubicSectionEmbeddingData_of_selectedAvoidance
      p hp D₁₀ S havoid htransverse
  refine ⟨degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData
    p hp hne D₁₀ T, ?_, ?_, ?_⟩
  · exact degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_cycle_degree
      p hp hne D₁₀ T
  · exact degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_toBase_etale
      p hp hne D₁₀ T
  · rw [← hTcompletion]
    exact degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_disjoint
      p hp hne D₁₀ T

/-- The selected finite-rank base-locus estimate yields the finite étale
rank-eleven residual.  This is the form to which the dimension estimates in
Voisin's Claim 3.4 apply directly. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_regularCubicSectionEmbeddingData_of_selectedFinrankDrop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hdrop : DegreeTenRegularCubicSectionSelectedFinrankDrop p hp D₁₀ S)
    (htransverse : ∀ (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 3),
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase
        (tripleCompleteIntersectionHomogeneousIdeal p S.q r hp S.hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
          S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  exact
    exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_regularCubicSectionEmbeddingData_of_selectedAvoidance
      p hp hne D₁₀ S
      (DegreeTenRegularCubicSectionSelectedAvoidance.ofFinrankDrop p hp D₁₀ S hdrop)
      htransverse

/-- An integral first cubic--cubic intersection and the transverse
three-cubic condition yield the full first residual, including its
disjointness from the completed degree-sixteen datum.  The associated-prime
avoidance required to select the third cubic follows from primeness. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_embeddingData_prime
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hprime : (Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : CubicTripleIntersectionTransverse p hp) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
          S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  exact
    exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_regularCubicSectionEmbeddingData_of_selectedAvoidance
      p hp hne D₁₀ S
    (DegreeTenRegularCubicSectionSelectedAvoidance.ofPrimeIntermediate
        p hp hne D₁₀ S hprime)
      (fun r hr hregular => htransverse S.q r S.hq hr S.hq0 S.hrel hregular)

/-- The same first-residual construction accepts the intrinsic form of the
Bertini irreducibility conclusion: the selected cubic is prime after passing
to the cubic-surface coordinate ring. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_embeddingData_quotientPrime
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hqprime : Prime (Ideal.Quotient.mk
      (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ) S.q))
    (htransverse : CubicTripleIntersectionTransverse p hp) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
          S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  have hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime :=
    principalIdeal_prime_of_irreducible_cubic p
      (irreducible_of_smooth_homogeneous_cubic_of_field p hp hne)
  exact
    exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_embeddingData_prime
      p hp hne D₁₀ S
      (ideal_span_pair_isPrime_of_quotient_mk_prime p S.q hpprime hqprime)
      htransverse


/-- Forgetting the identified completion gives the corresponding nonempty
type of embedded transverse first-residual data. -/
theorem nonempty_degreeTenTransverseCubicIntersectionEmbeddingData_of_regularCubicSectionEmbeddingData_of_finrank_drop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hdrop : DegreeTenCompletionThirdCubicFinrankDrop p hp D₁₀ S.completion)
    (htransverse : CubicTripleIntersectionTransverse p hp) :
    Nonempty (DegreeTenTransverseCubicIntersectionEmbeddingData p hp D₁₀) := by
  obtain ⟨T, _⟩ :=
    exists_degreeTenTransverseCubicIntersectionEmbeddingData_of_regularCubicSectionEmbeddingData_of_finrank_drop
      p hp D₁₀ S hdrop htransverse
  exact ⟨T⟩

/-- The embedded first-residual datum produces the degree-eleven finite
étale residual and proves its support disjoint from the degree-sixteen
completion.  The only hypotheses left are Voisin's rank-drop and transverse
choice assertions for the selected first cubic. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_regularCubicSectionEmbeddingData_and_finrank_drop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hdrop : DegreeTenCompletionThirdCubicFinrankDrop p hp D₁₀ S.completion)
    (htransverse : CubicTripleIntersectionTransverse p hp) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
          S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  obtain ⟨T, hTcompletion⟩ :=
    exists_degreeTenTransverseCubicIntersectionEmbeddingData_of_regularCubicSectionEmbeddingData_of_finrank_drop
      p hp D₁₀ S hdrop htransverse
  refine ⟨degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData
    p hp hne D₁₀ T, ?_, ?_, ?_⟩
  · exact degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_cycle_degree
      p hp hne D₁₀ T
  · exact degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_toBase_etale
      p hp hne D₁₀ T
  · rw [← hTcompletion]
    exact degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_disjoint
      p hp hne D₁₀ T

/-- Starting with a smooth cubic and a degree-ten datum, Voisin's rank-drop
and transverse-choice inputs yield a completed degree-sixteen datum together
with a disjoint finite étale degree-eleven residual. -/
theorem exists_degreeTenCompletion_and_residualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_finrank_drop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (hdrop : ∀ S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀,
      DegreeTenCompletionThirdCubicFinrankDrop p hp D₁₀ S.completion)
    (htransverse : CubicTripleIntersectionTransverse p hp) :
    ∃ C : DegreeTenRankSixteenCompletion p hp D₁₀,
      ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
          (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
        Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
        Disjoint
          (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) C.datum))
          (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  obtain ⟨S⟩ :=
    nonempty_degreeTenRegularCubicSectionEmbeddingData_of_smooth_cubic p hp hne D₁₀
  obtain ⟨R, hRdegree, hRetale, hdisjoint⟩ :=
    exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_regularCubicSectionEmbeddingData_and_finrank_drop
      p hp hne D₁₀ S (hdrop S) htransverse
  exact ⟨S.completion, R, hRdegree, hRetale, hdisjoint⟩

/-- The selected first cubic and the associated-prime rank-drop estimate
already give the finite étale degree-eleven residual.  Smoothness is needed
only upstream, to construct the regular first cubic; this theorem isolates
the exact remaining Lemma 3.3 and transversality inputs for that selection. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_of_regularCubicSectionData_and_finrank_drop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionData p hp D₁₀)
    (hdrop : DegreeTenCompletionThirdCubicFinrankDrop p hp D₁₀ S.completion)
    (htransverse : CubicTripleIntersectionTransverse p hp) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  obtain ⟨T⟩ :=
    nonempty_degreeTenTransverseCubicIntersectionData_of_regularCubicSectionData_of_finrank_drop
      p hp D₁₀ S hdrop htransverse
  exact exists_degreeTenResidualDatum_and_toBase_etale_of_transverseCubicIntersectionData
    p hp hne D₁₀ T

 /-- The normalized affine-chart data through which a chosen third cubic
vanishes on the completed degree-sixteen datum. -/
def DegreeTenRegularCubicSectionSelectedThirdCubicChart
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (r : MvPolynomial (Fin 4) K) : Prop :=
    let D := S.completion.datum
    letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
    letI : IsAffine D.val.subscheme :=
      isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    letI := finiteSchemeCoefficientAlgebra
      (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (z : CoordinateRing (equationIdeal p hp))
      (hz : z ∈ grading (equationIdeal p hp) 1)
      (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (he : ∀ s ∈ (equationIdeal p hp).toIdeal,
        (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) s = 0)
      (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
        (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) he) z = 1),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
      S.q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
      r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
      linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
        D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι

/-- A chosen third cubic for the fixed first section, retaining the same
normalized chart of the completed degree-sixteen datum. -/
structure DegreeTenRegularCubicSectionSelectedThirdCubicData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀) where
  r : MvPolynomial (Fin 4) K
  hr : r.IsHomogeneous 3
  regular : ∀ y : MvPolynomial (Fin 4) K,
    r * y ∈ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K)) →
      y ∈ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))
  chart : DegreeTenRegularCubicSectionSelectedThirdCubicChart p hp D₁₀ S r
  transverse : Etale
    (toBase (tripleCompleteIntersectionHomogeneousIdeal p S.q r hp S.hq hr))

/-- An integral first cubic--cubic curve makes any third cubic outside its
ideal a regular third equation.  Together with a normalized chart and the
finite-etale intersection assertion, this supplies the concrete selected
third cubic used by the first residual construction. -/
noncomputable def DegreeTenRegularCubicSectionSelectedThirdCubicData.ofPrimeIntermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hprime : (Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 3)
    (hrnot : r ∉ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K)))
    (chart : DegreeTenRegularCubicSectionSelectedThirdCubicChart p hp D₁₀ S r)
    (htransverse : Etale
      (toBase (tripleCompleteIntersectionHomogeneousIdeal p S.q r hp S.hq hr))) :
    DegreeTenRegularCubicSectionSelectedThirdCubicData p hp D₁₀ S := by
  exact
    { r := r
      hr := hr
      regular := regular_mod_prime_ideal_of_not_mem
        (Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))) hprime hrnot
      chart := chart
      transverse := htransverse }

/-- The explicit chart Jacobian criterion produces the transverse selected
third cubic required by the first residual.  This is the direct interface
from a chartwise Bertini calculation: the determinant of the four equations
`p`, `q`, `r`, and the chart normalization is a unit on every projective
chart. -/
noncomputable def
    DegreeTenRegularCubicSectionSelectedThirdCubicData.ofPrimeIntermediate_of_chartJacobian_isUnit
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hprime : (Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 3)
    (hrnot : r ∉ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K)))
    (chart : DegreeTenRegularCubicSectionSelectedThirdCubicChart p hp D₁₀ S r)
    (hjac : ∀ j : Fin 4,
      IsUnit (tripleCompleteIntersectionChartJacobian p S.q r hp S.hq hr j)) :
    DegreeTenRegularCubicSectionSelectedThirdCubicData p hp D₁₀ S := by
  exact DegreeTenRegularCubicSectionSelectedThirdCubicData.ofPrimeIntermediate
    p hp D₁₀ S hprime r hr hrnot chart
    (etale_tripleCompleteIntersection_toBase_of_chartJacobian_isUnit
      p S.q r hp S.hq hr hjac)

/-- A selected regular third cubic whose complete intersection is reduced
gives the transverse datum required by the first residual.  This is the
scheme-theoretic conclusion supplied by a Bertini argument. -/
noncomputable def DegreeTenRegularCubicSectionSelectedThirdCubicData.ofReduced
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 3)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K)))
    (chart : DegreeTenRegularCubicSectionSelectedThirdCubicChart p hp D₁₀ S r)
    (hreduced : AlgebraicGeometry.IsReduced
      (scheme (tripleCompleteIntersectionHomogeneousIdeal p S.q r hp S.hq hr))) :
    DegreeTenRegularCubicSectionSelectedThirdCubicData p hp D₁₀ S := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p S.q r hp S.hq hr
  have hp0 : p ≠ 0 :=
    isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree S.hq (by decide) S.hrel.symm
  letI : IsFinite (toBase I) :=
    triple_cubic_intersection_finite p S.q r hp S.hq hr hp0 S.hq0 S.hrel hregular
  letI : AlgebraicGeometry.IsReduced (scheme I) := hreduced
  exact
    { r := r
      hr := hr
      regular := hregular
      chart := chart
      transverse := finiteScheme_etale_of_isReduced (toBase I) }

noncomputable def DegreeTenRegularCubicSectionSelectedThirdCubicData.toEmbeddingData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (T : DegreeTenRegularCubicSectionSelectedThirdCubicData p hp D₁₀ S) :
    DegreeTenTransverseCubicIntersectionEmbeddingData p hp D₁₀ :=
  DegreeTenTransverseCubicIntersectionEmbeddingData.ofNormalizedChart
    p S.q T.r hp S.hq T.hr D₁₀ S.completion S.hrel T.regular T.chart T.transverse

theorem DegreeTenRegularCubicSectionSelectedThirdCubicData.toEmbeddingData_completion
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (T : DegreeTenRegularCubicSectionSelectedThirdCubicData p hp D₁₀ S) :
    (T.toEmbeddingData p hp D₁₀ S).completion = S.completion := rfl
theorem exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_selectedThirdCubicData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (T : DegreeTenRegularCubicSectionSelectedThirdCubicData p hp D₁₀ S) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
          S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  let U := T.toEmbeddingData p hp D₁₀ S
  refine ⟨degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData
    p hp hne D₁₀ U, ?_, ?_, ?_⟩
  · exact degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_cycle_degree
      p hp hne D₁₀ U
  · exact degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_toBase_etale
      p hp hne D₁₀ U
  · change Disjoint
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) U.completion.datum))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
        (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData p hp hne D₁₀ U)))
    exact degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_disjoint
      p hp hne D₁₀ U

/- A pointwise Jacobian certificate for the selected third cubic is enough
   for the residual construction.  This is the form used when Bertini is
   proved only on the one normalized chart retained by the first cubic,
   rather than uniformly for every possible third cubic. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_embeddingData_prime_of_selectedThirdCubicChart_of_chartJacobian_isUnit
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hprime : (Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (r : MvPolynomial (Fin 4) K) (hr : r.IsHomogeneous 3)
    (hrnot : r ∉ Ideal.span ({p, S.q} : Set (MvPolynomial (Fin 4) K)))
    (chart : DegreeTenRegularCubicSectionSelectedThirdCubicChart p hp D₁₀ S r)
    (hjac : ∀ j : Fin 4,
      IsUnit (tripleCompleteIntersectionChartJacobian p S.q r hp S.hq hr j)) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
          S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  let T := DegreeTenRegularCubicSectionSelectedThirdCubicData.ofPrimeIntermediate_of_chartJacobian_isUnit
    p hp D₁₀ S hprime r hr hrnot chart hjac
  exact exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_selectedThirdCubicData
    p hp hne D₁₀ S T

end PfaffianDescent
