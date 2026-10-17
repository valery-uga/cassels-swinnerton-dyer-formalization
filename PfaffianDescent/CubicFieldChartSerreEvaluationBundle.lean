import PfaffianDescent.CubicElevenPointGroundSerreEvaluation

/-! A compact predicate for actual evaluation witnesses of a fixed bundle.
The constructor only packages literal witnesses. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def CubicFieldChartSerreBundleEvaluation
    {F L E : Type u} [Field F] [Field L] [Field E] [Algebra F L] [Algebra F E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)]
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I)
      (z := (ell : CoordinateRing I))) = algebraMap F L)
    (M : (Proj (grading I)).Modules)
    (π : M ⟶ closedImmersionIdealTwist
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)
      (positiveSheafOfModules (grading I) 3)) : Prop :=
    ∃ (φ : Fin 3 → (Away (grading I) (ell : CoordinateRing I) →+* CubicSurfaceFirstJet E))
      (α : Fin 3 → (L →ₐ[F] E))
      (hres : ∀ k, cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap (φ k) =
        (α k).toRingHom.comp g),
      Function.Surjective (cubicGroundKernelJetSectionEvaluation I ell g hbase φ α hres M) ∧
      Function.Bijective (cubicGroundKernelSerrePointDerivative I ell g φ
        (fun k => (α k).toRingHom) hres M π)

theorem cubicFieldChartSerreBundleEvaluation_of_witnesses
    {F L E : Type u} [Field F] [Field L] [Field E] [Algebra F L] [Algebra F E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)]
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I)
      (z := (ell : CoordinateRing I))) = algebraMap F L)
    (M : (Proj (grading I)).Modules)
    (π : M ⟶ closedImmersionIdealTwist
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)
      (positiveSheafOfModules (grading I) 3))
    (φ : Fin 3 → (Away (grading I) (ell : CoordinateRing I) →+* CubicSurfaceFirstJet E))
    (α : Fin 3 → (L →ₐ[F] E))
    (hres : ∀ k, cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap (φ k) =
      (α k).toRingHom.comp g)
    (honto : Function.Surjective (cubicGroundKernelJetSectionEvaluation I ell g hbase φ α hres M))
    (hbij : Function.Bijective (cubicGroundKernelSerrePointDerivative I ell g φ
      (fun k => (α k).toRingHom) hres M π)) :
    CubicFieldChartSerreBundleEvaluation (E := E) I ell g hbase M π :=
  ⟨φ, α, hres, honto, hbij⟩

end PfaffianDescent
