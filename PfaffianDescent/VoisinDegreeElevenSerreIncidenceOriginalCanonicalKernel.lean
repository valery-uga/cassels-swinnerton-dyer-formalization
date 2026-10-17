import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalGraphKernel
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeMatrix
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCanonicalIdeal

/-! # Original smooth cubic data identify the actual canonical graph zero kernel -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective
open SerreExtensionData
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerre_exists_native_canonical_graph_kernel
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1}
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
    (e : SerreExtensionData (hypersurface p hp)
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)))
    (hne :
      letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
      letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp) _ e.toSequenceData hExt)
        (show 1 + 1 = 2 by omega) ≠ 0)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E))]
    (C : SerreExtensionRankTwoAffineCover e) :
    let base := hypersurfaceToBase p hp
    let M : (hypersurface p hp).Modules := e.E
    let D := serreIncidenceRankTwoAffineCover e C
    ∃ (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
      (b : finiteDimensionalProjectiveChartRing K
        (SchemeModuleGlobalSectionsOver base M) j →+* K)
      (hb : b.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K
        (SchemeModuleGlobalSectionsOver base M)) j) = RingHom.id K),
      (D.projectiveSectionLocalZeroGluedToAmbient base M).ker.comap
        (serreIncidenceGroundSectionGraph base M j b hb) = i.ker := by
  apply serreIncidenceCanonicalSection_exists_ground_graph_kernel
    (hypersurfaceToBase p hp) e (i default) (serreIncidenceRankTwoAffineCover e C) i
  intro k
  exact (cubicClosedPointSerreFiniteZeroResidual_canonical_chart_ideal_eq
    K p hp hp0 i e hne ⟨C.U k, C.affine k⟩ (C.trivialization k)).trans
      (cubicClosedPointSerreFiniteZeroResidual_pullback_snd_kernel i (C.U k).ι)

end PfaffianDescent.ProjectiveNegativeTwist
