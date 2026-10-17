import PfaffianDescent.VoisinDegreeElevenSerreIncidenceOriginalCanonicalKernel
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceClosedGraphSurface

/-! # Original canonical Serre section parameter and literal universal-zero fibre -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective
open SerreExtensionData
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerre_exists_native_canonical_parameter_surface_fibre
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
    let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
    let z := zero ≫ pullback.snd base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    ∃ (t : Spec (.of K) ⟶ schemeModuleGlobalSectionsProjectiveParameters base M),
      t ≫ schemeModuleGlobalSectionsProjectiveParametersToBase base M = 𝟙 _ ∧
      ∃ (v : Spec (.of L) ≅ pullback z t),
        v.hom ≫ pullback.snd z t = i ≫ base ∧
        v.hom ≫ pullback.fst z t ≫ zero ≫
          pullback.fst base (schemeModuleGlobalSectionsProjectiveParametersToBase base M) = i := by
  let base := hypersurfaceToBase p hp
  let M : (hypersurface p hp).Modules := e.E
  let D := serreIncidenceRankTwoAffineCover e C
  let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsClosedImmersion zero :=
    D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  obtain ⟨j,b,hb,hk⟩ := cubicClosedPointSerre_exists_native_canonical_graph_kernel
    K p hp hp0 i e hne C
  let t := serreIncidenceGroundSectionParameter base M j b
  have ht : t ≫ schemeModuleGlobalSectionsProjectiveParametersToBase base M = 𝟙 _ :=
    serreIncidenceGroundSectionParameter_toBase base M j b hb
  let g := serreIncidenceGroundSectionGraph base M j b hb
  let v := serreIncidenceClosedGraphZeroIso base
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M) t ht g
    (serreIncidenceGroundSectionGraph_fst base M j b hb)
    (serreIncidenceGroundSectionGraph_snd base M j b hb) zero i hk
  refine ⟨t,ht,v,?_,?_⟩
  · exact serreIncidenceClosedGraphZeroIso_hom_snd base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M) t ht g
      (serreIncidenceGroundSectionGraph_fst base M j b hb)
      (serreIncidenceGroundSectionGraph_snd base M j b hb) zero i hk
  · exact serreIncidenceClosedGraphZeroIso_hom_surface base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M) t ht g
      (serreIncidenceGroundSectionGraph_fst base M j b hb)
      (serreIncidenceGroundSectionGraph_snd base M j b hb) zero i hk

end PfaffianDescent.ProjectiveNegativeTwist
