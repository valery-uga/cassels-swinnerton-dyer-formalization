import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOriginalCanonicalRankSeedFibre
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOriginalCanonicalRankClosedSupportPoint
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOriginalCanonicalRankClosedSupportIncidence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
theorem cubicClosedPointSerreFiniteZeroResidual_original_rank_closed_support_exists_good_marked_canonical_seed
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
    (a : B ⟶ (AllCharacteristics.orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
    [IsOpenImmersion a]
    (hb : a ≫ (AllCharacteristics.orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).hom = b)
    (hmarked : ∀ n, marked n = a ≫
      (AllCharacteristics.orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3).left ≫
      (AllCharacteristics.orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 n).left)
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
          serreIncidenceGoodOpen
          (serreThreePointSectionIncidenceZeroFamily b base π marked hm zero)
          (cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen b base π marked hm zero) ∧
        IsFinite (pullback.snd (serreThreePointSectionIncidenceZeroFamily b base π marked hm zero) s) ∧
        Etale (pullback.snd (serreThreePointSectionIncidenceZeroFamily b base π marked hm zero) s) := by
  let base := hypersurfaceToBase p hp
  let M : (hypersurface p hp).Modules := e.E
  let C' := serreIncidenceRankTwoAffineCover e C
  let zero := C'.projectiveSectionLocalZeroGluedToAmbient base M
  let π := schemeModuleGlobalSectionsProjectiveParametersToBase base M
  letI : IsClosedImmersion zero := C'.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
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
  letI : IsFinite d :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hpoints : ∀ n, c ≫ a ≫ (AllCharacteristics.orderedFamilyConfigurationι base 3).left ≫
      (AllCharacteristics.orderedFamilyCoordinate base 3 n).left = δ n ≫ i := by
    intro n
    calc
      _ = c ≫ marked n := congrArg (fun q => c ≫ q) (hmarked n).symm
      _ = _ := (hsupport n).symm
  have hcClosed := cubicClosedPointSerreFiniteZeroResidual_rankConfiguration_support_point_closed
    base d i hi a c r δ hδd hpoints
  have hc : c ≫ b = r := by
    calc
      c ≫ b = c ≫ marked 0 ≫ base := congrArg (fun q => c ≫ q) (hm 0).symm
      _ = (δ 0 ≫ i) ≫ base := by rw [← Category.assoc, ← hsupport 0]
      _ = δ 0 ≫ d := by rw [Category.assoc, hi]
      _ = r := hδd 0
  obtain ⟨t, ht, s, hsP, hsC, hgood, hf, he⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_original_rank_support_exists_finite_good_canonical_seed
      K p hp hp0 i e C hi b marked hm c α hsupport
  have hsP' : s ≫ serreThreePointSectionIncidenceToParameters b base π marked hm zero = c ≫ b ≫ t := by
    exact hsP.trans ((congrArg (fun q => q ≫ t) hc).symm.trans (Category.assoc c b t))
  have hsClosed := cubicClosedPointSerreFiniteZeroResidual_canonical_incidence_seed_closed
    b base π marked hm zero t ht c hcClosed s hsP' hsC
  letI : LocallyOfFiniteType b := by rw [← hb]; infer_instance
  letI : IsSeparated b := by
    rw [← hb]
    change IsSeparated (a ≫ (AllCharacteristics.orderedFamilyConfigurationOpen base 3).ι ≫
      (AllCharacteristics.orderedFamilyPowerOver base 3).hom)
    infer_instance
  let g := serreThreePointSectionIncidenceZeroFamily b base π marked hm zero
  let f := serreThreePointSectionIncidenceToParameters b base π marked hm zero ≫ π
  letI : LocallyOfFiniteType f := by dsimp [f]; infer_instance
  letI : IsLocallyNoetherian (serreThreePointSectionIncidence b base π marked hm zero) :=
    LocallyOfFiniteType.isLocallyNoetherian f
  letI : IsProper g := inferInstance
  letI : IsLocallyNoetherian (pullback (zero ≫ pullback.snd base π)
      (serreThreePointSectionIncidenceToParameters b base π marked hm zero) : Scheme) :=
    LocallyOfFiniteType.isLocallyNoetherian g
  letI : IsFinite (pullback.snd g s) := hf
  letI : Etale (pullback.snd g s) := he
  let y := s (IsLocalRing.closedPoint E)
  letI : Finite (g.fiber y) :=
    cubicClosedPointSerreFiniteZeroResidual_seed_residue_fibre_finite g s
  have hW := cubicClosedPointSerreFiniteZeroResidual_finiteFibre_threeMarkedSeed g
    (serreIncidenceMarkedZeroSection b base π marked hm zero)
    (serreIncidenceMarkedZeroSection_toIncidence b base π marked hm zero) y hsClosed
    (cubicClosedPointSerreFiniteZeroResidual_seed_residue_fibre_fields g s)
  exact ⟨t, ht, s, hsP, hsC, ⟨hgood, hW⟩, hf, he⟩
end PfaffianDescent.ProjectiveNegativeTwist
