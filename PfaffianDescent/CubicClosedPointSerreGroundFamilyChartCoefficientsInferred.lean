import PfaffianDescent.CubicClosedPointSerreGroundFamilyChartCoefficients
import PfaffianDescent.SerreActualCubicGroundFamilyProjections
import PfaffianDescent.SerreActualGroundFamilyBaseMap

/-! # Opaque native specialization of the checked ground-family coefficient theorem -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The actual new family has the generic canonical parameter projection.
Keeping this identity opaque confines conversion of the native parameter-map
wrapper to this small declaration. -/
theorem serreActualCubicGroundFamilyToNew_parameters_canonical
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1) :
    letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
    let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
    let M := (Scheme.Modules.pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
    serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG ≫
      pullback.snd x (schemeModuleGlobalSectionsProjectiveParametersToBase x M) =
    pullback.snd x
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F))) ≫
      serreActualGroundKernelCanonicalParameters x M
        ((serreIncidenceCubicCoefficientGlobalSections_finrank (F := F) p hp e C).trans h9)
        (serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9) G H hHG := by
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  exact serreActualCubicGroundFamilyToNew_parameters p hp e C h9 G H hHG

/-- Opaque native specialization with its result type inferred from the
checked generic coefficient theorem. Inference retains the actual cubic
charts, old/new family maps, transported basis, and surface coefficient map,
while avoiding a second independent elaboration of their large result type.
The remaining arguments are the actual chart indices, chart maps, and their
ambient factorizations, in the same order as the generic theorem. -/
@[irreducible]
def pointSplittingCubicSerreGroundChosenSection_cubicGroundParameter_coefficients_inferred
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    {I J : Type u} (A : SchemeModuleFiniteFreeAffineCover e.E I)
    (B : SchemeModuleFiniteFreeAffineCover
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) J)
    (G : Matrix (Fin 9) (Fin 3) F) (H : Matrix (Fin 3) (Fin 9) F)
    (hHG : H * G = 1) {T : Scheme.{u}}
    (t : T ⟶ serreActualCubicGroundFamilyAmbient (F := F) p hp) :=
  letI := serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C
  let x := hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  let M := (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E
  let hnew : finrank F (SchemeModuleGlobalSectionsOver x M) = 9 :=
    (serreIncidenceCubicCoefficientGlobalSections_finrank (F := F) p hp e C).trans h9
  pointSplittingSerreGroundFamily_chart_coefficients
    (hypersurfaceToBase p hp) e.E x M h9 hnew A B
    (serreIncidenceCubicCoefficientGlobalBasis (F := F) p hp e C h9)
    G H hHG t (pullback.snd x
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F))))
    (serreActualCubicGroundFamilyToOriginal p hp e h9 G H hHG)
    (serreActualCubicGroundFamilyToNew p hp e C h9 G H hHG)
    (serreActualCubicGroundFamilyToOriginal_parameters p hp e h9 G H hHG)
    (serreActualCubicGroundFamilyToNew_parameters_canonical p hp e C h9 G H hHG)
    (affineFunctionHom (t ≫ pullback.fst x
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F))) ≫ x))
    (serreActualGroundFamily_kernel_baseMap x G H hHG t)

end PfaffianDescent
