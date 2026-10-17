import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundChosenSectionEquality

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Equality of actual sections on the same twice-coefficient cubic, for ANY
actual coefficient-cubic global section, not merely its fibre evaluations. -/
theorem pointSplittingCubicSerreGroundChosenSection_native_section_eq_combination
    {K F E : Type u} [Field K] [Field F] [Field E]
    (a : K →+* F) (β : F →+* E)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) = 9)
    (σ : SchemeModuleGlobalSectionsOver
      (hypersurfaceToBase (p.map a) (hp.map a))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap a p hp)).obj e.E)) :
    letI : Algebra K F := a.toAlgebra
    letI : Algebra F E := β.toAlgebra
    letI : Algebra K E := (β.comp a).toAlgebra
    letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    serreActualPulledGlobalSection
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (hypersurfaceToBase ((p.map (algebraMap K F)).map (algebraMap F E))
        ((hp.map (algebraMap K F)).map (algebraMap F E)))
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap F E)
        (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      ((Scheme.Modules.pullback
        (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E) σ ≫
      (pointSplittingCubicSerreGroundChosenSection_compositeModuleIso (F := F) (E := E) p hp e.E).hom =
    pointSplittingCubicSerreGroundChosenSection_originalCombinationMap (F := F) (E := E) p hp e h9
      (pointSplittingCubicSerreGroundKernel_originalSectionsTensorEquiv
        (F := F) (E := E) p hp e C (1 ⊗ₜ[F] σ)) := by
  letI : Algebra K F := a.toAlgebra
  letI : Algebra F E := β.toAlgebra
  letI : Algebra K E := (β.comp a).toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  exact pointSplittingCubicSerreGroundChosenSection_section_eq_combination
    (F := F) (E := E) p hp e C h9 σ

end PfaffianDescent
