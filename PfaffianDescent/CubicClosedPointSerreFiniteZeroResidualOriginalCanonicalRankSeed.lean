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
theorem cubicClosedPointSerreFiniteZeroResidual_original_rank_support_exists_good_canonical_seed
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
    {E : Type u} [Field E] [Algebra K E] [FiniteDimensional K E]
    {B : Scheme.{u}} (b : B ⟶ Spec (.of K)) [LocallyOfFiniteType b] [IsSeparated b]
    (marked : Fin 3 → (B ⟶ hypersurface p hp))
    (hm : ∀ n, marked n ≫ hypersurfaceToBase p hp = b)
    (c : Spec (.of E) ⟶ B)
    (hc : c ≫ b = Spec.map (CommRingCat.ofHom (algebraMap K E)))
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
  have hne := cubicClosedPointSerreFiniteZeroResidual_yoneda_nonzero_of_rankTwoCover K p hp hp0 i e C
  let δ : Fin 3 → (Spec (.of E) ⟶ Spec (.of L)) :=
    fun n => Spec.map (CommRingCat.ofHom (α n).toRingHom)
  have hδd : ∀ n, δ n ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K E)) := by
    intro n
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact (α n).commutes x
  obtain ⟨t, ht, s, hsP, hsC, hW, hf, he⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_original_exists_canonical_marked_seed
      K p hp hp0 i e hne C hi b marked hm c hc δ hδd hsupport
  let g := serreThreePointSectionIncidenceZeroFamily b base π marked hm zero
  letI : IsProper g := inferInstance
  letI : IsFinite (pullback.snd g s) := hf
  let y := s (IsLocalRing.closedPoint E)
  letI : Finite (g.fiber y) :=
    cubicClosedPointSerreFiniteZeroResidual_seed_residue_fibre_finite g s
  letI : Finite (g ⁻¹' {y} : Set _) := (g.fiberHomeo y).finite_iff.mp inferInstance
  have hgood : y ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen g :=
    cubicClosedPointSerreFiniteZeroResidual_mem_goodOpen_of_finite_fibre g y (Set.toFinite _)
  exact ⟨t, ht, s, hsP, hsC, ⟨hgood, hW⟩, hf, he⟩
end PfaffianDescent.ProjectiveNegativeTwist
