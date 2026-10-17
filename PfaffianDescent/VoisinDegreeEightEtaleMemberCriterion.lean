import PfaffianDescent.VoisinEtaleJacobianConverse
import PfaffianDescent.VoisinDegreeEightRestrictionKernelEtale

/-!
# A canonical quadratic-pencil criterion for the degree-eight residual

The full quadratic restriction kernel has a chosen basis. Étaleness of the
intersection with one basis member gives the proper universal singular-member
locus. For a two-dimensional kernel, this reduces the final geometric input
to transversality of its two displayed basis quadrics.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicTwoQuadricRestrictionKernelSingularParameterLocus_ne_univ_of_etale_basis_member
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (x : Fin 4 → A)
    (i : Fin (finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2))))
    (hEtale : Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
      p q (quadraticRestrictionKernelFrame (K := K) x i).1
      hp hq (quadraticRestrictionKernelFrame (K := K) x i).2))) :
    cubicTwoQuadricRestrictionKernelSingularParameterLocus p q hp hq x ≠
      Set.univ := by
  let v := quadraticRestrictionKernelFrame (K := K) x
  let c : Fin (finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2))) → K :=
    fun j => if j = i then 1 else 0
  have hci : c i = 1 := by simp [c]
  have hrepr : (v i).1 = ∑ j, C (c j) * (v j).1 := by
    classical
    simp [c]
  exact cubicTwoQuadricUniversalSingularParameterLocus_ne_univ_of_etale_member
    p q (v i).1 hp hq (v i).2 v c i hci hrepr hEtale

/-- For a normalized rank-eight datum, étaleness of the complete intersection
cut out by two members of its canonical quadratic-kernel basis supplies the
proper-member condition. -/
theorem DegreeEightQuadraticRestrictionKernelProperMemberExists.of_canonicalBasisEtale
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) :
    letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
    letI : IsAffine D₈.val.subscheme :=
      isAffine_of_isAffineHom (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    letI := finiteSchemeCoefficientAlgebra
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    letI : FiniteDimensional K Γ(D₈.val.subscheme, ⊤) :=
      finiteSchemeCoefficient_finite
        (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∀ (z : CoordinateRing (equationIdeal p hp))
      (hz : z ∈ grading (equationIdeal p hp) 1)
      (x : Fin 4 → Γ(D₈.val.subscheme, ⊤))
      (he : ∀ s ∈ (equationIdeal p hp).toIdeal,
        (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) s = 0)
      (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
        (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) he) z = 1),
      Function.Surjective
          (eval₂Hom (algebraMap K Γ(D₈.val.subscheme, ⊤)) x) →
      linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
          D₈.val.subscheme.isoSpec.inv ≫ D₈.val.subschemeι →
      ∀ (i₀ i₁ : Fin (finrank K
        (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)))),
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p
        (quadraticRestrictionKernelFrame (K := K) x i₀).1
        (quadraticRestrictionKernelFrame (K := K) x i₁).1
        hp (quadraticRestrictionKernelFrame (K := K) x i₀).2
        (quadraticRestrictionKernelFrame (K := K) x i₁).2)) →
      DegreeEightQuadraticRestrictionKernelProperMemberExists p hp D₈ := by
  letI : IsFinite (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := D₈.property.1
  letI : IsAffine D₈.val.subscheme :=
    isAffine_of_isAffineHom (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI : FiniteDimensional K Γ(D₈.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro z hz x he hzOne hxsurj hpoint i₀ i₁ hEtale
  let q := (quadraticRestrictionKernelFrame (K := K) x i₀).1
  have hq : q.IsHomogeneous 2 :=
    (quadraticRestrictionKernelFrame (K := K) x i₀).2
  have hqvan : q.eval₂ (algebraMap K Γ(D₈.val.subscheme, ⊤)) x = 0 :=
    quadraticRestrictionKernelFrame_vanishes (K := K) x i₀
  have hq0 : q ≠ 0 := by
    intro hzero
    apply (quadraticRestrictionKernelFrame_linearIndependent (K := K) x).ne_zero i₀
    apply Subtype.ext
    exact hzero
  refine ⟨z, hz, x, he, hzOne, hxsurj, hpoint, q, hq, hqvan, hq0, ?_⟩
  exact cubicTwoQuadricRestrictionKernelSingularParameterLocus_ne_univ_of_etale_basis_member
    p q hp hq x i₁ hEtale

end PfaffianDescent
