import PfaffianDescent.CubicAffineQuotientSupportLocalSurface
import PfaffianDescent.ActualArtinianQuotientSupport

/-!
Instantiate the generic
finite-support localization theorem with the support CONSTRUCTED from the
whole original quotient, and geometry derived from the original cubic.
-/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

theorem cubic_actualFiniteSupport_localSurface001
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (a : Spec (.of A) ⟶ hypersurface p hp) [IsOpenImmersion a]
    (ha : a ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (J : Ideal A) [Module.Finite K (A ⧸ J)] [IsArtinianRing (A ⧸ J)]
    (m : MaximalSpectrum A) (hm : m ∈ actualArtinianQuotientSupport001 J) :
    IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
      ringKrullDim (Localization.AtPrime m.asIdeal) = 2 := by
  classical
  letI : Fintype (MaximalSpectrum (A ⧸ J)) := Fintype.ofFinite _
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hm
  exact cubicAffineQuotient_support_localSurface001 p hp hp0 a ha J z.toPrimeSpectrum

end PfaffianDescent
end
