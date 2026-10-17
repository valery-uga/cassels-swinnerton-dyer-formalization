import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSectionsFrame
import PfaffianDescent.VoisinFiniteFreeAffineCoverFromLocal

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Native field Gamma frame on every pure section tensor, derived from an
actual finite affine rank-two trivializing cover. -/
theorem pointSplittingCubicSerreGroundChosenSection_fieldFrame_tmul
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (c : F) (s : SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) :
    letI : CompactSpace (hypersurface p hp) :=
      QuasiCompact.compactSpace_of_compactSpace (hypersurfaceToBase p hp)
    serreIncidenceGlobalSectionsFieldFrame (L := F) (hypersurfaceToBase p hp) e C (c ⊗ₜ[K] s) =
    c • serreActualPulledGlobalSection (hypersurfaceToBase p hp)
      (schemeFieldBaseChangeToField (L := F) (hypersurfaceToBase p hp))
      (schemeFieldBaseChangeToOriginal (L := F) (hypersurfaceToBase p hp)) e.E s := by
  classical
  letI : CompactSpace (hypersurface p hp) :=
    QuasiCompact.compactSpace_of_compactSpace (hypersurfaceToBase p hp)
  obtain ⟨D, ⟨hfinite⟩⟩ := exists_finiteFreeAffineCover_of_localTrivializations
    (show (hypersurface p hp).Modules from e.E) (ULift.{u} (Fin 2)) (fun x => by
      have hx : x ∈ (⨆ i, C.U i) := by rw [C.covers]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨C.U i, hi, C.affine i, ⟨C.trivialization i⟩⟩)
  letI : Fintype D.ι := hfinite
  letI : DecidableEq D.ι := Classical.decEq _
  rw [serreIncidenceGlobalSectionsFieldFrame_apply]
  have hmap := D.globalSectionsFieldBaseChangeLinearEquiv_toLinearMap_eq_canonical
    (L := F) (hypersurfaceToBase p hp) (show _ from e.E)
  rw [← hmap]
  exact D.globalSectionsFieldBaseChangeLinearEquiv_tmul_eq_smul_pullback
    (L := F) (hypersurfaceToBase p hp) (show _ from e.E) c s

/-- The actual coefficient-cubic section frame sends every pure tensor to the
literal coefficient-map pullback, with the exact field scalar. -/
theorem pointSplittingCubicSerreGroundChosenSection_coefficientFrame_tmul
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    (c : F) (s : SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E) :
    pointSplittingCubicSerreGroundKernel_coefficientFrame (F := F) p hp e C (c ⊗ₜ[K] s) =
    c • serreActualPulledGlobalSection (hypersurfaceToBase p hp)
      (hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
      (ProjectiveNegativeTwist.cubicPointTraceFieldBaseChangeCubicCoefficientMap
        (algebraMap K F) p hp) e.E s := by
  letI : CompactSpace (hypersurface p hp) :=
    QuasiCompact.compactSpace_of_compactSpace (hypersurfaceToBase p hp)
  change serreIncidenceCubicCoefficientGlobalSectionsIso (F := F) p hp e.E
    (serreIncidenceGlobalSectionsFieldFrame (L := F) (hypersurfaceToBase p hp) e C (c ⊗ₜ[K] s)) = _
  rw [pointSplittingCubicSerreGroundChosenSection_fieldFrame_tmul,
    map_smul, pointSplittingCubicSerreGroundKernel_coefficientIso_pulled]

end PfaffianDescent
