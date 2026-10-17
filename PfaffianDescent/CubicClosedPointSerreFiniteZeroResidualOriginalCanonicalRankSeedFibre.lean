import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOriginalCanonicalMarkedSeed
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoverYonedaNonzero
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSeedFibreProperties
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGoodOpen
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
theorem cubicClosedPointSerreFiniteZeroResidual_original_rank_support_exists_finite_good_canonical_seed
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
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E))]
    (C : SerreExtensionRankTwoAffineCover e)
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    {E : Type u} [Field E] [Algebra K E]
    {B : Scheme.{u}} (b : B ⟶ Spec (.of K))
    (marked : Fin 3 → (B ⟶ hypersurface p hp))
    (hm : ∀ n, marked n ≫ hypersurfaceToBase p hp = b)
    (c : Spec (.of E) ⟶ B)
    (α : Fin 3 → (L →ₐ[K] E))
    (hsupport : ∀ n, Spec.map (CommRingCat.ofHom (α n).toRingHom) ≫ i = c ≫ marked n) :
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
          cubicClosedPointSerreFiniteZeroResidual_goodOpen
          (serreThreePointSectionIncidenceZeroFamily b base π marked hm zero) ∧
        IsFinite (pullback.snd (serreThreePointSectionIncidenceZeroFamily b base π marked hm zero) s) ∧
        Etale (pullback.snd (serreThreePointSectionIncidenceZeroFamily b base π marked hm zero) s) := by
  let base := hypersurfaceToBase p hp
  let M : (hypersurface p hp).Modules := e.E
  let C' := serreIncidenceRankTwoAffineCover e C
  let zero := C'.projectiveSectionLocalZeroGluedToAmbient base M
  let π := schemeModuleGlobalSectionsProjectiveParametersToBase base M
  letI : IsClosedImmersion zero := C'.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  have hne := cubicClosedPointSerreFiniteZeroResidual_yoneda_nonzero_of_rankTwoCover K p hp hp0 i e C
  obtain ⟨t, ht, v, hv, hvs⟩ := cubicClosedPointSerre_exists_native_canonical_parameter_surface_fibre
    K p hp hp0 i e hne C
  let d := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let r := Spec.map (CommRingCat.ofHom (algebraMap K E))
  let δ : Fin 3 → (Spec (.of E) ⟶ Spec (.of L)) :=
    fun n => Spec.map (CommRingCat.ofHom (α n).toRingHom)
  have hδd : ∀ n, δ n ≫ d = r := by
    intro n
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact (α n).commutes x
  have hc : c ≫ b = r := by
    calc
      c ≫ b = c ≫ marked 0 ≫ base := congrArg (fun q => c ≫ q) (hm 0).symm
      _ = (δ 0 ≫ i) ≫ base := by rw [← Category.assoc, ← hsupport 0]
      _ = δ 0 ≫ d := by rw [Category.assoc, hi]
      _ = r := hδd 0
  have ht' : t ≫ π = 𝟙 _ := ht
  let a : Spec (.of E) ⟶ pullback b π :=
    pullback.lift c (r ≫ t) (by simp only [Category.assoc, ht', Category.comp_id]; exact hc)
  have ha : a ≫ pullback.snd b π = r ≫ t := pullback.lift_snd _ _ _
  have hpoints : ∀ n, δ n ≫ i = a ≫ pullback.fst b π ≫ marked n := by
    intro n
    rw [← Category.assoc, pullback.lift_fst]
    exact hsupport n
  obtain ⟨s, hsP, hsB⟩ := serreIncidenceCanonicalSupport_exists_seed b base π marked hm zero
    t d i v (hv.trans hi) hvs a r ha δ hδd hpoints
  have hsC : s ≫ serreThreePointSectionIncidenceToConfiguration b base π marked hm zero = c := by
    simpa only [a, pullback.lift_fst] using hsB
  letI : IsFinite d :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : Module.FinitePresentation K L := Module.finitePresentation_of_finite K L
  letI : Algebra.Etale K L := {
    formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
    finitePresentation := Algebra.FinitePresentation.of_finitePresentation K L
  }
  letI : Etale d :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  let g := serreThreePointSectionIncidenceZeroFamily b base π marked hm zero
  let w := serreIncidenceSeedCanonicalFibreIso b base π marked hm zero s t d v (hv.trans hi) r hsP
  have hw : w.hom ≫ pullback.snd g s = pullback.snd d r :=
    serreIncidenceSeedCanonicalFibreIso_hom_snd b base π marked hm zero s t d v (hv.trans hi) r hsP
  have hprops := cubicClosedPointSerreFiniteZeroResidual_fibre_finite_etale_of_iso
    g s (pullback.snd d r) w hw
  letI : IsFinite (pullback.snd g s) := hprops.1
  letI : IsProper g := inferInstance
  let y := s (IsLocalRing.closedPoint E)
  letI : Finite (g.fiber y) :=
    cubicClosedPointSerreFiniteZeroResidual_seed_residue_fibre_finite g s
  letI : Finite (g ⁻¹' {y} : Set _) := (g.fiberHomeo y).finite_iff.mp inferInstance
  have hgood : y ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen g :=
    cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre g y (Set.toFinite _)
  exact ⟨t, ht, s, hsP, hsC, hgood, hprops.1, hprops.2⟩
end PfaffianDescent.ProjectiveNegativeTwist
