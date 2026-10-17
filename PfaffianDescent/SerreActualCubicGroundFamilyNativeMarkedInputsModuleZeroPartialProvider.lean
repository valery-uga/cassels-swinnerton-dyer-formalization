import PfaffianDescent.SerreActualCubicGroundFamilyNativeGeometryParameters
import PfaffianDescent.SerreActualCanonicalMarkedResidualInputsOfFiniteChosenGeometry

/-! Small coefficient-family prefix of the accepted
whole-record bridge. i/j/tE/Finite/geometry remain unapplied; final native
producer must construct them from the original selected incidence data. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Actual native B-zero projection is proper, with no properness premise. -/
theorem serreActualNativeMarkedInputsZeroToParameters_isProper
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    {IB : Type u} [Fintype IB] [DecidableEq IB]
    (B : SchemeModuleFiniteFreeAffineCover
      (serreActualNativeGeometryPulledModule (F := F) p hp e) IB) :
    IsProper (serreActualNativeGeometryZeroToAmbient (F := F) p hp e C B ≫
      pullback.snd (serreActualNativeGeometryCubicToBase (F := F) p hp)
        (serreActualNativeGeometryParametersToBase (F := F) p hp e C)) := by
  letI : IsProper (serreActualNativeGeometryCubicToBase (F := F) p hp) := by
    change IsProper (hypersurfaceToBase
      (p.map (algebraMap K F)) (hp.map (algebraMap K F)))
    infer_instance
  letI := serreActualNativeGeometryPulledModule_finiteDimensional (F := F) p hp e C
  exact serreSectionUniversalZeroToParameters_isProper
    (serreActualNativeGeometryCubicToBase (F := F) p hp)
    (serreActualNativeGeometryPulledModule (F := F) p hp e) B

/-- Fix only literal x/pp/B-zero. The result is inferred, not reconstructed
through a large explicit output contract. The whole geometry record stays
abstract behind the checked generic bridge. -/
@[irreducible]
def serreActualCubicGroundFamily_nativeMarkedInputsModuleZeroPartialProvider
    {K F E L3 : Type u} [Field K] [Field F] [Field E] [Field L3]
    [Algebra K F] [Algebra F E]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    {N : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)]
    {IB : Type u} [Fintype IB] [DecidableEq IB]
    (B : SchemeModuleFiniteFreeAffineCover
      (serreActualNativeGeometryPulledModule (F := F) p hp e) IB)
    {I : Scheme.{u}} :=
  letI := serreActualNativeGeometryZeroToAmbient_isClosedImmersion
    (F := F) p hp e C B
  letI := serreActualNativeMarkedInputsZeroToParameters_isProper (F := F) p hp e C B
  serreActualCanonicalMarkedResidualInputsOfFiniteChosenGeometry
    (F := F) (E := E) (L := L3) (I := I)
    (serreActualNativeGeometryCubicToBase (F := F) p hp)
    (serreActualNativeGeometryParametersToBase (F := F) p hp e C)
    (serreActualNativeGeometryZeroToAmbient (F := F) p hp e C B)

end PfaffianDescent
