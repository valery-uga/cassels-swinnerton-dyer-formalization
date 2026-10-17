import PfaffianDescent.CubicGroundKernelJetPointBase

/-! The actual jet residue point factors through the SAME original
degree-eleven support immersion, not just a point with matching coordinates. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicGroundKernelJetPoint_factors_original_support
    {F L E : Type u} [Field F] [Field L] [Field E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    (φ : Away (grading I) (ell : CoordinateRing I) →+* CubicSurfaceFirstJet E)
    (β : L →+* E)
    (hres : cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ = β.comp g) :
    cubicGroundKernelJetPoint I ell φ = Spec.map (CommRingCat.ofHom β) ≫
      cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g := by
  simp only [cubicGroundKernelJetPoint, hres,
    cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion,
    cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism, Category.assoc]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end PfaffianDescent
