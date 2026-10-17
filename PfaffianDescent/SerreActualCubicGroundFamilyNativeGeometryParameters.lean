import PfaffianDescent.SerreActualCubicGroundFamilyNativeOriginalSelectedSectionEvidenceProvider
import PfaffianDescent.CubicConfigurationRankChosenEvidenceGeometry

/-! Literal coefficient cubic, pulled Serre module, parameter map and zero
family, with their internally derived finite-dimensional and closedness facts.
These aliases retain the original morphisms and introduce no hypotheses. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Literal coefficient cubic map; instantiated with the actual native field. -/
def serreActualNativeGeometryCubicToBase
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :=
  hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))

instance serreActualNativeGeometryCubicToBase_isSeparated
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    IsSeparated (serreActualNativeGeometryCubicToBase (F := F) p hp) := by
  change IsSeparated (hypersurfaceToBase
    (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
  infer_instance

/-- Literal coefficient pullback of the original Serre bundle. -/
def serreActualNativeGeometryPulledModule
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N) :=
  (Scheme.Modules.pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp)).obj e.E

theorem serreActualNativeGeometryPulledModule_finiteDimensional
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)] :
    FiniteDimensional F (SchemeModuleGlobalSectionsOver
      (serreActualNativeGeometryCubicToBase (F := F) p hp)
      (serreActualNativeGeometryPulledModule (F := F) p hp e)) := by
  simpa only [serreActualNativeGeometryCubicToBase, serreActualNativeGeometryPulledModule]
    using serreIncidenceCubicCoefficientGlobalSections_finiteDimensional (F := F) p hp e C

def serreActualNativeGeometryParametersToBase
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)] :=
  letI := serreActualNativeGeometryPulledModule_finiteDimensional (F := F) p hp e C
  schemeModuleGlobalSectionsProjectiveParametersToBase
    (serreActualNativeGeometryCubicToBase (F := F) p hp)
    (serreActualNativeGeometryPulledModule (F := F) p hp e)

def serreActualNativeGeometryZeroToAmbient
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    {IB : Type u} [Fintype IB] [DecidableEq IB]
    (B : SchemeModuleFiniteFreeAffineCover
      (serreActualNativeGeometryPulledModule (F := F) p hp e) IB) :=
  letI := serreActualNativeGeometryPulledModule_finiteDimensional (F := F) p hp e C
  B.projectiveSectionLocalZeroGluedToAmbient
    (serreActualNativeGeometryCubicToBase (F := F) p hp)
    (serreActualNativeGeometryPulledModule (F := F) p hp e)

theorem serreActualNativeGeometryZeroToAmbient_isClosedImmersion
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    {IB : Type u} [Fintype IB] [DecidableEq IB]
    (B : SchemeModuleFiniteFreeAffineCover
      (serreActualNativeGeometryPulledModule (F := F) p hp e) IB) :
    IsClosedImmersion (serreActualNativeGeometryZeroToAmbient (F := F) p hp e C B) := by
  letI := serreActualNativeGeometryPulledModule_finiteDimensional (F := F) p hp e C
  exact B.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient
    (serreActualNativeGeometryCubicToBase (F := F) p hp)
    (serreActualNativeGeometryPulledModule (F := F) p hp e)


end PfaffianDescent
