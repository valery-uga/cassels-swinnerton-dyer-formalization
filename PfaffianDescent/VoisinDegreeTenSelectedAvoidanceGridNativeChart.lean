import PfaffianDescent.FiniteSubschemeCompleteIntersection
import PfaffianDescent.NormalizedChartAlgebraTransport
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_exists_nativeFiniteChart
    {F : Type u} [Field F] [Infinite F]
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)] :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
    letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
    ∃ T : NormalizedAmbientChart F Γ(Z, ⊤) (Fin 4)
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
        (Z.isoSpec.inv ≫ i ≫ hypersurfaceToAmbient p hp),
      Function.Surjective (eval₂Hom (algebraMap F Γ(Z, ⊤)) T.x) ∧
      p.eval₂ (algebraMap F Γ(Z, ⊤)) T.x = 0 := by
  letI : CommRing Γ(Z, ⊤) := inferInstance
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra (i ≫ hypersurfaceToBase p hp)
  obtain ⟨ell, hell, x, he, hellOne, hxsurj, hpx, hpoint⟩ :=
    cubicFiniteSubscheme_normalized_ambient_chart p hp i
  exact ⟨⟨ell, hell, x, he, hellOne, hpoint⟩, hxsurj, hpx⟩
end PfaffianDescent
