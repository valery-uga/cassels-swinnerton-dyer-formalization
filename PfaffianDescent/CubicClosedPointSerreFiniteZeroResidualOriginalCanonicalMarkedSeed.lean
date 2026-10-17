import PfaffianDescent.VoisinDegreeElevenSerreIncidenceOriginalCanonicalSurfaceFibre
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCanonicalIncidenceMarkedSeed
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

theorem cubicClosedPointSerreFiniteZeroResidual_original_exists_canonical_marked_seed
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
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    {E : Type u} [Field E] [Algebra K E] [FiniteDimensional K E]
    {B : Scheme.{u}} (b : B ⟶ Spec (.of K)) [LocallyOfFiniteType b] [IsSeparated b]
    (marked : Fin 3 → (B ⟶ hypersurface p hp))
    (hm : ∀ n, marked n ≫ hypersurfaceToBase p hp = b)
    (c : Spec (.of E) ⟶ B)
    (hc : c ≫ b = Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (δ : Fin 3 → (Spec (.of E) ⟶ Spec (.of L)))
    (hδd : ∀ n, δ n ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (hδi : ∀ n, δ n ≫ i = c ≫ marked n) :
    let base := hypersurfaceToBase p hp
    let M : (hypersurface p hp).Modules := e.E
    let C' := serreIncidenceRankTwoAffineCover e C
    let zero := C'.projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsClosedImmersion zero := C'.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    let P := schemeModuleGlobalSectionsProjectiveParameters base M
    let π := schemeModuleGlobalSectionsProjectiveParametersToBase base M
    ∃ (t : Spec (.of K) ⟶ P), t ≫ π = 𝟙 _ ∧
      ∃ s : Spec (.of E) ⟶ serreThreePointSectionIncidence b base π marked hm zero,
        s ≫ serreThreePointSectionIncidenceToParameters b base π marked hm zero =
          Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t ∧
        s ≫ serreThreePointSectionIncidenceToConfiguration b base π marked hm zero = c ∧
        s (IsLocalRing.closedPoint E) ∈
          cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen b base π marked hm zero ∧
        IsFinite (pullback.snd (serreThreePointSectionIncidenceZeroFamily b base π marked hm zero) s) ∧
        Etale (pullback.snd (serreThreePointSectionIncidenceZeroFamily b base π marked hm zero) s) := by
  let base := hypersurfaceToBase p hp
  let M : (hypersurface p hp).Modules := e.E
  let C' := serreIncidenceRankTwoAffineCover e C
  let zero := C'.projectiveSectionLocalZeroGluedToAmbient base M
  let π := schemeModuleGlobalSectionsProjectiveParametersToBase base M
  letI : IsClosedImmersion zero := C'.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  obtain ⟨t, ht, v, hv, hvs⟩ := cubicClosedPointSerre_exists_native_canonical_parameter_surface_fibre
    K p hp hp0 i e hne C
  letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : Module.FinitePresentation K L := Module.finitePresentation_of_finite K L
  letI : Algebra.Etale K L := {
    formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
    finitePresentation := Algebra.FinitePresentation.of_finitePresentation K L
  }
  letI : Etale (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  obtain ⟨s, hsP, hsC, hW, hfinite, hetale⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_canonicalSupport_exists_marked_seed
      b base π marked hm zero t ht (Spec.map (CommRingCat.ofHom (algebraMap K L))) i
      v (hv.trans hi) hvs c hc δ hδd hδi
  exact ⟨t, ht, s, hsP, hsC, hW, hfinite, hetale⟩

end PfaffianDescent.ProjectiveNegativeTwist
