import PfaffianDescent.VoisinDegreeElevenSerreIncidenceOriginalCanonicalFibre
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Etale.Field

/-! # Original canonical Serre section parameter and literal universal-zero fibre -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective
open SerreExtensionData
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_exists_native_canonical_finite_etale_parameter
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
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
    (C : SerreExtensionRankTwoAffineCover e)
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
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
          IsFinite (pullback.snd z t) ∧ Etale (pullback.snd z t) := by
  let base := hypersurfaceToBase p hp
  let M : (hypersurface p hp).Modules := e.E
  let D := serreIncidenceRankTwoAffineCover e C
  let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
  let z := zero ≫ pullback.snd base
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
  obtain ⟨t, ht, v, hv⟩ := cubicClosedPointSerre_exists_native_canonical_parameter_fibre
    K p hp hp0 i e hne C
  letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : Module.FinitePresentation K L := Module.finitePresentation_of_finite K L
  letI : Algebra.Etale K L := {
    formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
    finitePresentation := Algebra.FinitePresentation.of_finitePresentation K L
  }
  letI : Etale (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have he : pullback.snd z t = v.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    rw [← cancel_epi v.hom]
    simp only [Iso.hom_inv_id_assoc]
    exact hv.trans hi
  refine ⟨t, ht, v, hv, ?_, ?_⟩ <;> rw [he] <;> infer_instance

end PfaffianDescent.ProjectiveNegativeTwist
