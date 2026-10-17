import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSectionsCoefficient

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Actual coefficient-cubic sections identified with scalar-extended original
sections using the native geometric field comparison. -/
def pointSplittingCubicSerreGroundKernel_coefficientFrame
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)] :
    (F ⊗[K] SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) ≃ₗ[F]
      SchemeModuleGlobalSectionsOver
        (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
        ((Scheme.Modules.pullback
          (ProjectiveNegativeTwist.cubicPointTraceFieldBaseChangeCubicCoefficientMap
            (algebraMap K F) p hp)).obj e.E) := by
  letI : CompactSpace (hypersurface p hp) :=
    QuasiCompact.compactSpace_of_compactSpace (hypersurfaceToBase p hp)
  exact (serreIncidenceGlobalSectionsFieldFrame (L := F) (hypersurfaceToBase p hp) e C).trans
    (serreIncidenceCubicCoefficientGlobalSectionsIso (F := F) p hp e.E)

/-- On the actual original Gamma basis the coefficient frame is the literal
pulled global section. -/
theorem pointSplittingCubicSerreGroundKernel_coefficientFrame_one_tmul_basis
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E))) :
    pointSplittingCubicSerreGroundKernel_coefficientFrame (F := F) p hp e C
      (1 ⊗ₜ[K] Module.finBasis K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) i) =
    serreActualPulledGlobalSection (hypersurfaceToBase p hp)
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (ProjectiveNegativeTwist.cubicPointTraceFieldBaseChangeCubicCoefficientMap
        (algebraMap K F) p hp) e.E
      (Module.finBasis K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) i) := by
  letI : CompactSpace (hypersurface p hp) :=
    QuasiCompact.compactSpace_of_compactSpace (hypersurfaceToBase p hp)
  change serreIncidenceCubicCoefficientGlobalSectionsIso (F := F) p hp e.E
    (serreIncidenceGlobalSectionsFieldFrame (L := F) (hypersurfaceToBase p hp) e C _) = _
  rw [serreIncidenceGlobalSectionsFieldFrame_apply,
    schemeModuleGlobalSectionsFieldBaseChangeLinearMap_one_tmul_finBasis]
  exact pointSplittingCubicSerreGroundKernel_coefficientIso_pulled p hp e.E _

end PfaffianDescent
