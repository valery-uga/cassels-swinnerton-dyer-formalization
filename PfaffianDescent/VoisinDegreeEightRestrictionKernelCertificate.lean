import PfaffianDescent.VoisinQuadraticSingularChartBadLocusCriterion
import PfaffianDescent.VoisinDegreeEightRestrictionKernelEtale

/-!
# A polynomial certificate for Voisin's degree-eight residual

One specialized mixed cubic--quadric--quadric singular fibre with four
coordinate-power ideal memberships certifies the properness needed to choose
the second quadric and construct the degree-four residual.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An explicit algebraic certificate for the final quadratic choice.  The
normalization data describes the actual rank-eight finite subscheme; the four
ideal memberships certify emptiness of one specialized singular fibre. -/
def DegreeEightRestrictionKernelCoordinateCertificate
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI : IsAffine D₈.val.subscheme :=
    isAffine_of_isAffineHom (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∃ (z : CoordinateRing (equationIdeal p hp))
    (hz : z ∈ grading (equationIdeal p hp) 1)
    (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
    (he : ∀ s ∈ (equationIdeal p hp).toIdeal,
      (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) s = 0)
    (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) he) z = 1),
    Function.Surjective
        (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) ∧
      linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
        D₈.val.subscheme.isoSpec.inv ≫ D₈.val.subschemeι ∧
      ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 2),
        q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 ∧
        q ≠ 0 ∧
        ∃ (i : Fin (finrank K
          (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2))))
          (g : ChartRing
            (⊥ : HomogeneousIdeal (homogeneousSubmodule
              (Fin (finrank K
                (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)))) K)) i →+* K),
          let I := cubicTwoQuadricUniversalSingularChartFiberIdeal
            p q hp hq (quadraticRestrictionKernelFrame (K := K) x) i g
          ∀ j : Fin 4,
            ∃ n : ℕ, (MvPolynomial.X j : MvPolynomial (Fin 4) K) ^ n ∈ I.toIdeal

/-- A coordinate certificate gives the exact proper-member input for the
checked degree-eight residual construction. -/
theorem DegreeEightRestrictionKernelCoordinateCertificate.toProperMember
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcert : DegreeEightRestrictionKernelCoordinateCertificate p hp D₈) :
    DegreeEightQuadraticRestrictionKernelProperMemberExists p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI : IsAffine D₈.val.subscheme :=
    isAffine_of_isAffineHom (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI : FiniteDimensional K Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨z, hz, x, he, hzOne, hxsurj, hpoint,
    q, hq, hqvan, hq0, i, g, hmem⟩ := hcert
  exact ⟨z, hz, x, he, hzOne, hxsurj, hpoint,
    q, hq, hqvan, hq0,
    cubicTwoQuadricRestrictionKernelSingularParameterLocus_ne_univ_of_coordinate_powers_mem
      p q hp hq x i g hmem⟩

/-- The final finite polynomial certificate implies the disjoint étale
degree-four residual on a smooth cubic. -/
theorem exists_degreeFourResidualDatum_of_coordinateCertificate
    {K : Type u} [Field K] [Infinite K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcert : DegreeEightRestrictionKernelCoordinateCertificate p hp D₈) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 4,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 4 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₈))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  exact
    exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_restrictionKernelProperMember
      p hp hp0 D₈ (hcert.toProperMember p hp D₈)

end PfaffianDescent
