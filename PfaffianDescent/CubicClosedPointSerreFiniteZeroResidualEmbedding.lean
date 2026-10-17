import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPullbackRestriction
import PfaffianDescent.SerreExtensionPencilGluing

/-! # Actual reduced closed subschemes inside the selected Serre zero scheme

Actual pullback vanishing is transported to each affine bundle chart.  The
resulting local lifts prove support containment.  Reducedness of the original
closed subscheme then proves scheme-theoretic containment and constructs its
closed immersion into the actual globally glued zero scheme.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PfaffianDescent
open BundleSectionZeroLocus SerreExtensionData
universe u
set_option backward.isDefEq.respectTransparency false

@[reassoc]
theorem cubicClosedPointSerreFiniteZeroResidual_ideal_transport_comp
    {X : Scheme.{u}} (I J : Scheme.IdealSheafData X) (h : I = J) :
    (eqToIso (congrArg (·.subscheme) h)).inv ≫ I.subschemeι = J.subschemeι := by
  cases h
  simp only [eqToIso_refl, Iso.refl_inv, Category.id_comp]

theorem cubicClosedPointSerreFiniteZeroResidual_kernel_le_of_reduced_range
    {X Z T : Scheme.{u}} (j : Z ⟶ X) [IsReduced Z]
    (c : T ⟶ X) (h : Set.range j ⊆ Set.range c) : c.ker ≤ j.ker := by
  have hj : j.ker = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (Set.range j)) := by
    have hm := Scheme.IdealSheafData.map_vanishingIdeal j (⊤ : Closeds Z)
    simpa only [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
      Scheme.IdealSheafData.map_bot, Closeds.coe_top, Set.image_univ] using hm
  rw [hj, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  apply Closeds.closure_le.mpr
  exact h.trans c.range_subset_ker_support

theorem cubicClosedPointSerreFiniteZeroResidual_selected_chart_lift
    {X Z : Scheme.{u}} {M : X.Modules} (e : SerreExtensionData X M)
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (j : Z ⟶ X) [IsClosedImmersion j]
    (hs : (Scheme.Modules.pullback j).map (e.E.unitHomEquiv.symm seed.lift) = 0)
    (i : C.ι) :
    ∃ w : pullback j (C.U i).ι ⟶
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i 0 (𝟙 _)).subscheme,
      w ≫ (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal
        e C seed i 0 (𝟙 _)).subschemeι = pullback.snd j (C.U i).ι := by
  let U := C.U i
  letI : IsAffine (U : Scheme.{u}) := C.affine i
  let jU := pullback.snd j U.ι
  let t := localFreeIsoOfOver U (ULift.{u} (Fin 2)) (C.trivialization i)
  let s := restrictSectionToOpen U seed.lift
  have hsU := cubicClosedPointSerreFiniteZeroResidual_over_section_pullback_zero
    j U e.E seed.lift hs
  let v := cubicClosedPointSerreFiniteZeroResidual_affine_zeroLift
    jU (ULift.{u} (Fin 2)) t s hsU
  have hv := cubicClosedPointSerreFiniteZeroResidual_affine_zeroLift_comp
    jU (ULift.{u} (Fin 2)) t s hsU
  let J := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i 0 (𝟙 _)
  have hJ : J = sectionZeroIdealOfFreeIso (ULift.{u} (Fin 2)) t s :=
    SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_zero_one e C seed i
  let w : pullback j U.ι ⟶ J.subscheme := v ≫ (eqToIso (congrArg (·.subscheme) hJ)).inv
  refine ⟨w, ?_⟩
  change w ≫ J.subschemeι = jU
  dsimp only [w]
  rw [Category.assoc]
  have heq : (eqToIso (congrArg (·.subscheme) hJ)).inv ≫ J.subschemeι =
      sectionZeroSubschemeOfFreeIsoι (ULift.{u} (Fin 2)) t s := by
    exact cubicClosedPointSerreFiniteZeroResidual_ideal_transport_comp J _ hJ
  rw [heq]
  exact hv

theorem cubicClosedPointSerreFiniteZeroResidual_selected_range_contains
    {X Z : Scheme.{u}} {M : X.Modules} (e : SerreExtensionData X M)
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (j : Z ⟶ X) [IsClosedImmersion j]
    (hs : (Scheme.Modules.pullback j).map (e.E.unitHomEquiv.symm seed.lift) = 0) :
    Set.range j ⊆ Set.range
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed 0 (𝟙 _)) := by
  rintro _ ⟨z, rfl⟩
  have hz : j z ∈ ⨆ i, C.U i := by rw [C.covers]; trivial
  rw [Opens.mem_iSup] at hz
  obtain ⟨i, hzi⟩ := hz
  let U := C.U i
  let jU := pullback.snd j U.ι
  let zUtoZ := pullback.fst j U.ι
  let J := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i 0 (𝟙 _)
  obtain ⟨w, hw⟩ :=
    cubicClosedPointSerreFiniteZeroResidual_selected_chart_lift e C seed j hs i
  have hzrange : z ∈ Set.range zUtoZ := by
    change z ∈ (pullback.fst j U.ι).opensRange
    rw [Scheme.Hom.opensRange_pullbackFst]
    rw [Scheme.Opens.opensRange_ι]
    change j z ∈ U
    exact hzi
  obtain ⟨zU, hzU⟩ := hzrange
  refine ⟨SerreExtensionRankTwoAffineCover.localPencilZeroGluedι e C seed i 0 (𝟙 _) (w zU), ?_⟩
  have hcomp := SerreExtensionRankTwoAffineCover.localPencilZeroGluedι_comp_toAmbient
    e C seed i 0 (𝟙 _)
  have hpoint :
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient
        e C seed 0 (𝟙 _))
        ((SerreExtensionRankTwoAffineCover.localPencilZeroGluedι
          e C seed i 0 (𝟙 _)) (w zU)) = U.ι (J.subschemeι (w zU)) :=
    congrArg (fun f => f (w zU)) hcomp
  have hwpoint : J.subschemeι (w zU) = jU zU := congrArg (fun f => f zU) hw
  have hp := congrArg (fun f => f zU) (pullback.condition (f := j) (g := U.ι))
  change j (zUtoZ zU) = U.ι (jU zU) at hp
  exact hpoint.trans ((congrArg U.ι hwpoint).trans (hp.symm.trans (congrArg j hzU)))

def cubicClosedPointSerreFiniteZeroResidual_selected_embedding
    {X Z : Scheme.{u}} {M : X.Modules} (e : SerreExtensionData X M)
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (j : Z ⟶ X) [IsClosedImmersion j] [IsReduced Z]
    (hs : (Scheme.Modules.pullback j).map (e.E.unitHomEquiv.symm seed.lift) = 0) :
    Z ⟶ SerreExtensionRankTwoAffineCover.localPencilZeroGluedScheme e C seed 0 (𝟙 _) := by
  let c := SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed 0 (𝟙 _)
  letI : IsClosedImmersion c :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing
      e C seed 0 (𝟙 _)
  exact IsClosedImmersion.lift c j
    (cubicClosedPointSerreFiniteZeroResidual_kernel_le_of_reduced_range j c
      (cubicClosedPointSerreFiniteZeroResidual_selected_range_contains e C seed j hs))

@[reassoc]
theorem cubicClosedPointSerreFiniteZeroResidual_selected_embedding_comp
    {X Z : Scheme.{u}} {M : X.Modules} (e : SerreExtensionData X M)
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (j : Z ⟶ X) [IsClosedImmersion j] [IsReduced Z]
    (hs : (Scheme.Modules.pullback j).map (e.E.unitHomEquiv.symm seed.lift) = 0) :
    cubicClosedPointSerreFiniteZeroResidual_selected_embedding e C seed j hs ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed 0 (𝟙 _) = j := by
  letI : IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed 0 (𝟙 _)) :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing
      e C seed 0 (𝟙 _)
  unfold cubicClosedPointSerreFiniteZeroResidual_selected_embedding
  exact IsClosedImmersion.lift_fac _ _ _

theorem cubicClosedPointSerreFiniteZeroResidual_selected_embedding_isClosedImmersion
    {X Z : Scheme.{u}} {M : X.Modules} (e : SerreExtensionData X M)
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (j : Z ⟶ X) [IsClosedImmersion j] [IsReduced Z]
    (hs : (Scheme.Modules.pullback j).map (e.E.unitHomEquiv.symm seed.lift) = 0) :
    IsClosedImmersion
      (cubicClosedPointSerreFiniteZeroResidual_selected_embedding e C seed j hs) := by
  let c := SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed 0 (𝟙 _)
  letI : IsClosedImmersion c :=
    SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroGluedToAmbient_of_localPencilZeroGluing
      e C seed 0 (𝟙 _)
  let w := cubicClosedPointSerreFiniteZeroResidual_selected_embedding e C seed j hs
  letI : IsClosedImmersion (w ≫ c) := by
    change IsClosedImmersion
      (cubicClosedPointSerreFiniteZeroResidual_selected_embedding e C seed j hs ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroGluedToAmbient e C seed 0 (𝟙 _))
    rw [cubicClosedPointSerreFiniteZeroResidual_selected_embedding_comp]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion w c

end PfaffianDescent
