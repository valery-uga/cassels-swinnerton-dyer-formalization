import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOriginalChosenResidual
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoverYonedaNonzero
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCanonicalMarkedDatum
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalFibreBaseChangeSurface

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
open PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The actual chosen parameter yields residual eight from its literal canonical
marked field stalk, using only finite-good membership of the seed. -/
theorem cubicClosedPointSerreFiniteZeroResidual_chosen_canonical_marked_residual_eight
    (K : Type u) [Field K] {E L₃ : Type u} [Field E] [Field L₃] [Algebra K E] [Algebra K L₃] [FiniteDimensional K L₃]
    {B : Scheme.{u}}
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (SheafOfModules.{u}
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).ringCatSheaf)]
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
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hL : Module.finrank K L = 11)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp)
      (show (hypersurface p hp).Modules from e.E))]
    (C : SerreExtensionRankTwoAffineCover e)
    (j₃ : Spec (.of L₃) ⟶ hypersurface p hp) [IsClosedImmersion j₃]
    (hj₃ : j₃ ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L₃)))
    (hL₃ : Module.finrank K L₃ = 3)
    (cfg : B ⟶ Spec (.of K))
    (marked : Fin 3 → (B ⟶ hypersurface p hp))
    (hm : ∀ n, marked n ≫ hypersurfaceToBase p hp = cfg) :
    let base := hypersurfaceToBase p hp
    let M : (hypersurface p hp).Modules := e.E
    let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
    let D := serreIncidenceRankTwoAffineCover e C
    let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
    letI : IsProper (zero ≫ pullback.snd base pp) := serreSectionUniversalZeroToParameters_isProper base M D
    let g := serreThreePointSectionIncidenceZeroFamily cfg base pp marked hm zero
    ∀ (t : Spec (.of K) ⟶ schemeModuleGlobalSectionsProjectiveParameters base M),
      t ≫ pp = 𝟙 _ →
      ∀ (s : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg base pp marked hm zero),
      s (IsLocalRing.closedPoint E) ∈
        cubicClosedPointSerreFiniteZeroResidual_goodOpen g →
      s ≫ serreThreePointSectionIncidenceToParameters cfg base pp marked hm zero =
        Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t →
      ∀ n : Fin 3,
      (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base pp marked hm zero ≫ marked n)
        (IsLocalRing.closedPoint E) ∉ Set.range i →
      (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base pp marked hm zero ≫ marked n)
        (IsLocalRing.closedPoint E) = j₃ (IsLocalRing.closedPoint L₃) →
      ∀ (y : (pullback (zero ≫ pullback.snd base pp)
          (Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t) : Scheme)),
      IsField ((pullback (zero ≫ pullback.snd base pp)
        (Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t)).presheaf.stalk y) →
      (pullback.fst (zero ≫ pullback.snd base pp)
        (Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t) ≫ zero ≫
          pullback.fst base pp) y = j₃ (IsLocalRing.closedPoint L₃) →
      ∃ R : AllCharacteristics.FiniteSubschemeDatum base 8,
        Disjoint (Set.range R.val.subschemeι) (Set.range j₃) := by
  let base := hypersurfaceToBase p hp
  let M : (hypersurface p hp).Modules := e.E
  let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
  let D := serreIncidenceRankTwoAffineCover e C
  let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsProper (zero ≫ pullback.snd base pp) := serreSectionUniversalZeroToParameters_isProper base M D
  dsimp only
  intro t ht s hW hsp n hout hsupport y hy hySurface
  have hne := cubicClosedPointSerreFiniteZeroResidual_yoneda_nonzero_of_rankTwoCover
    K p hp hp0 i e C
  obtain ⟨seed,j,b,a,ha,hb,hbt,hlift,hc⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_original_chosen_parameter_exists_seed
      K p hp hp0 i e hne C cfg marked hm t ht s hsp n hout
  have hsp' : s ≫ serreThreePointSectionIncidenceToParameters cfg base pp marked hm zero =
      Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ serreIncidenceGroundSectionParameter base M j b := by
    rw [hbt]
    exact hsp
  let c := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _)
  letI : IsClosedImmersion c :=
    C.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing e seed 0 (𝟙 _)
  have hf := cubicClosedPointSerreFiniteZeroResidual_selected_chart_goodPoint_endpoint_finite
    base e C seed cfg marked hm j b hb a ha hc s hW hsp'
  have H11 := cubicClosedPointSerreFiniteZeroResidual_selected_finite_rank_eleven
    K p hp hp0 i e hne hi hL C seed hf
  letI : IsFinite (c ≫ base) := H11.1
  obtain ⟨ht',v,hv,hvc⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_selected_chart_parameter_surface_fibre base e C seed j b hb a ha hc
  have hmrange := cubicClosedPointSerreFiniteZeroResidual_chosenMarked_mem_surface_range
    cfg base pp marked hm zero s (serreIncidenceGroundSectionParameter base M j b)
    (c ≫ base) c v hv hvc (Spec.map (CommRingCat.ofHom (algebraMap K E))) hsp' n
    (IsLocalRing.closedPoint E)
  have hjrange : j₃ (IsLocalRing.closedPoint L₃) ∈ Set.range c := hsupport ▸ hmrange
  let w := cubicClosedPointSerreFiniteZeroResidual_fieldPoint_support_embedding c j₃ hjrange
  letI : IsClosedImmersion w :=
    cubicClosedPointSerreFiniteZeroResidual_fieldPoint_support_embedding_isClosedImmersion c j₃ hjrange
  have hwc : w ≫ c = j₃ :=
    cubicClosedPointSerreFiniteZeroResidual_fieldPoint_support_embedding_comp c j₃ hjrange
  have hpoint : (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base pp marked hm zero ≫ marked n)
      (IsLocalRing.closedPoint E) = c (w (IsLocalRing.closedPoint L₃)) := by
    rw [hsupport,← hwc,Scheme.Hom.comp_apply]
  letI : IsFinite (j₃ ≫ base) := by
    rw [hj₃]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hthree : finiteSchemeRank (w ≫ c ≫ base) = 3 := by
    rw [finiteSchemeRank_eq_finrank,← Category.assoc,hwc,hj₃,
      Scheme.Hom.finrank_SpecMap_algebraMap]
    exact (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := L₃))
      (IsLocalRing.closedPoint K)).trans hL₃
  subst t
  let z := zero ≫ pullback.snd base pp
  let t₀ := serreIncidenceGroundSectionParameter base M j b
  let r := Spec.map (CommRingCat.ofHom (algebraMap K E))
  let vE := serreIncidenceCanonicalFibreBaseChangeIso z t₀ (c ≫ base) v hv r
  have hSurface := serreIncidenceCanonicalFibreBaseChangeIso_inv_surface
    z t₀ (c ≫ base) v hv r (zero ≫ pullback.fst base pp) c hvc
  have hpoint : c (pullback.fst (c ≫ base) r (vE.inv y)) =
      c (w (IsLocalRing.closedPoint L₃)) := by
    calc
      _ = (pullback.fst z (r ≫ t₀) ≫ zero ≫ pullback.fst base pp) y :=
        congrArg (fun f => f y) hSurface
      _ = j₃ (IsLocalRing.closedPoint L₃) := hySurface
      _ = c (w (IsLocalRing.closedPoint L₃)) := by
        rw [← hwc, Scheme.Hom.comp_apply]
  have h11 : finiteSchemeRank (c ≫ base) = 11 := by
    rw [finiteSchemeRank_eq_finrank]
    exact H11.2 _
  have H := cubicClosedPointSerreFiniteZeroResidual_canonicalMarked_datum_eight
    base c w z t₀ v hv y hy hpoint h11 hthree
  simpa only [hwc] using H

end PfaffianDescent.ProjectiveNegativeTwist
