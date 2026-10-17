import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualOriginalChosenResidual
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualCoverYonedaNonzero
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent.ProjectiveNegativeTwist
open BundleSectionZeroLocus AllCharacteristics.HomogeneousProjective SerreExtensionData
open PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
/-- The chosen canonical fibre has rank eleven using only finite-fibre
open membership and a marked point outside the original support. Relative
marked-point etaleness and the degree-three support are not rank hypotheses. -/
theorem cubicClosedPointSerreFiniteZeroResidual_chosen_fibre_rank_eleven_of_good
    (K : Type u) [Field K] {E : Type u} [Field E] [Algebra K E]
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
      let z := zero ≫ pullback.snd base pp
      let c := pullback.snd z t
      IsFinite c ∧ (∀ x, c.finrank x = 11) := by
  let base := hypersurfaceToBase p hp
  let M : (hypersurface p hp).Modules := e.E
  let pp := schemeModuleGlobalSectionsProjectiveParametersToBase base M
  let D := serreIncidenceRankTwoAffineCover e C
  let zero := D.projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsClosedImmersion zero := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base M
  letI : IsProper (zero ≫ pullback.snd base pp) := serreSectionUniversalZeroToParameters_isProper base M D
  dsimp only
  intro t ht s hW hsp n hout
  have hne := cubicClosedPointSerreFiniteZeroResidual_yoneda_nonzero_of_rankTwoCover K p hp hp0 i e C
  obtain ⟨seed,j,b,a,ha,hb,hbt,hlift,hc⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_original_chosen_parameter_exists_seed
      K p hp hp0 i e hne C cfg marked hm t ht s hsp n hout
  have hsp' : s ≫ serreThreePointSectionIncidenceToParameters cfg base pp marked hm zero =
      Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ serreIncidenceGroundSectionParameter base M j b := by
    rw [hbt]
    exact hsp
  have hf := cubicClosedPointSerreFiniteZeroResidual_selected_chart_goodPoint_endpoint_finite
    base e C seed cfg marked hm j b hb a ha hc s hW hsp'
  have H := cubicClosedPointSerreFiniteZeroResidual_selected_finite_rank_eleven
    K p hp hp0 i e hne hi hL C seed hf
  let c := C.localPencilZeroGluedToAmbient e seed 0 (𝟙 _) ≫ base
  letI : IsFinite c := H.1
  obtain ⟨ht',v,hv,hvc⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_selected_chart_parameter_surface_fibre base e C seed j b hb a ha hc
  subst t
  let z := zero ≫ pullback.snd base pp
  let q := pullback.snd z (serreIncidenceGroundSectionParameter base M j b)
  have hv' : v.hom ≫ q = c := hv
  letI : IsFinite q := by
    rw [← v.inv_hom_id_assoc q, hv']
    infer_instance
  refine ⟨inferInstance, ?_⟩
  intro x
  have heq := congrArg (fun f => f.finrank x) hv'
  rw [Scheme.Hom.finrank_comp_left_of_isIso] at heq
  exact heq.trans (H.2 x)

end PfaffianDescent.ProjectiveNegativeTwist
