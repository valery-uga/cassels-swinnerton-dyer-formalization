import PfaffianDescent.VoisinSingularChartBadLocusCriterion
import PfaffianDescent.VoisinDegreeTenRestrictionKernelEtale

/-!
# A polynomial certificate for the first Voisin residual

Four coordinate-power ideal memberships in one specialized singular fibre
certify that the restriction-kernel bad locus is proper.  The checked
restriction-kernel selector then constructs the degree-eleven residual.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The exact finite polynomial certificate needed on a normalized chart of
the completed degree-ten datum.  Unlike an abstract properness premise, this
can be checked by four ideal-membership calculations for one third cubic. -/
def DegreeTenRestrictionKernelCoordinateCertificate
    {K : Type u} [Field K] [Infinite K]
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
    ∃ (i : cubicRestrictionKernelParameterIndex (K := K) x)
      (g : cubicRestrictionKernelParameterChartRing (K := K) x i →+* K),
      let I := tripleCompleteIntersectionUniversalSingularChartFiberIdeal
        p S.q hp S.hq (cubicRestrictionKernelFrame (K := K) x) i g
      ∀ j : Fin 4,
        ∃ n : ℕ, (MvPolynomial.X j : MvPolynomial (Fin 4) K) ^ n ∈ I.toIdeal

/-- The proper-chart hypothesis supplies the explicit coordinate-power
certificate by selecting one empty singular fiber over the ground field. -/
theorem DegreeTenRegularCubicSectionRestrictionKernelProperChart.toCoordinateCertificate
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hproper : DegreeTenRegularCubicSectionRestrictionKernelProperChart
      p hp D₁₀ S) :
    DegreeTenRestrictionKernelCoordinateCertificate p hp D₁₀ S := by
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI : FiniteDimensional K Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint, hsing⟩ := hproper
  obtain ⟨i, g, _hbase, hpow⟩ :=
    exists_groundFieldRestrictionKernel_parameterChart_coordinatePowers_of_singularLocus_ne_univ
      p S.q hp S.hq x hsing
  exact ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint, i, g, hpow⟩

/-- The polynomial certificate proves properness of the actual singular
parameter locus on the same normalized chart. -/
theorem DegreeTenRestrictionKernelCoordinateCertificate.toProperChart
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hcert : DegreeTenRestrictionKernelCoordinateCertificate p hp D₁₀ S) :
    DegreeTenRegularCubicSectionRestrictionKernelProperChart p hp D₁₀ S := by
  let D := S.completion.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI : FiniteDimensional K Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint, i, g, hmem⟩ := hcert
  exact ⟨z, hz, x, he, hzOne, hxsurj, hqvan, hpoint,
    tripleCompleteIntersectionRestrictionKernelSingularParameterLocus_ne_univ_of_coordinate_powers_mem
      p S.q hp S.hq x i g hmem⟩

/-- A finite polynomial certificate produces Voisin's disjoint finite étale
rank-eleven residual from the degree-ten datum. -/
theorem exists_degreeTenResidualDatum_of_coordinateCertificate
    {K : Type u} [Field K] [Infinite K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData p hp D₁₀)
    (hcert : DegreeTenRestrictionKernelCoordinateCertificate p hp D₁₀ S) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
          S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  exact exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_restrictionKernelProperChart
    p hp hp0 D₁₀ S (hcert.toProperChart p hp D₁₀ S)

end PfaffianDescent
