import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodRestrictExtension
import PfaffianDescent.LocalExtResidueInjective

/-! # Actual free affine neighborhoods away from the closed support point -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Ambient native stalk isomorphisms on an open make the actual restricted
module map invertible. -/
theorem cubicClosedPointSerreFreeNeighborhood_restrict_isIso_of_stalk
    {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules} (p : M ⟶ N)
    (h : ∀ (x : X), x ∈ U → IsIso ((schemeModuleStalkModuleFunctor X x).map p)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map p) := by
  apply schemeModuleMap_isIso_of_stalk
  intro x
  letI := h (U.ι x) x.2
  have ha : IsIso ((schemeModuleStalkFunctor X (U.ι x)).map p) :=
    Functor.map_isIso (forget₂ (ModuleCat (X.presheaf.stalk (U.ι x))) AddCommGrpCat)
      ((schemeModuleStalkModuleFunctor X (U.ι x)).map p)
  let G := Scheme.Modules.toPresheaf (U : Scheme) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hb : IsIso (G.map ((Scheme.Modules.restrictFunctor U.ι).map p)) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso U.ι x) p).mpr ha
  have hh : IsIso ((forget₂ (ModuleCat ((U : Scheme).presheaf.stalk x)) AddCommGrpCat).map
      ((schemeModuleStalkModuleFunctor (U : Scheme) x).map
        ((Scheme.Modules.restrictFunctor U.ι).map p))) := by
    change IsIso (G.map ((Scheme.Modules.restrictFunctor U.ι).map p))
    exact hb
  letI := hh
  exact isIso_of_reflects_iso _
    (forget₂ (ModuleCat ((U : Scheme).presheaf.stalk x)) AddCommGrpCat)

/-- The actual ideal inclusion is invertible on any open avoiding the
closed field point, after any actual line-bundle twist. -/
theorem cubicClosedPointSerreFreeNeighborhood_ideal_restrict_isIso_away
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, T.over (V j) ≅ SheafOfModules.unit (X.ringCatSheaf.over (V j)))
    (U : X.Opens) (hU : ∀ x ∈ U, x ≠ i default) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (closedImmersionIdealTwistSequence i T).f) := by
  let S := closedImmersionIdealTwistSequence i T
  have hS : S.ShortExact := closedImmersionIdealTwistSequence_shortExact_of_coversTop_iso_unit
    i V hV eV
  apply cubicClosedPointSerreFreeNeighborhood_restrict_isIso_of_stalk
  intro x hx
  let F := schemeModuleStalkModuleFunctor X x
  letI : F.Additive := by dsimp [F]; infer_instance
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  letI : PreservesFiniteLimits F := by dsimp [F]; infer_instance
  letI : PreservesFiniteColimits F := by dsimp [F]; infer_instance
  letI : Subsingleton (S.X₃.presheaf.stalk x) :=
    fieldPointPushforwardTwist_stalk_subsingleton_off_of_coversTop_iso_unit i T V hV eV x (hU x hx)
  letI : Subsingleton (F.obj S.X₃) := by
    change Subsingleton (S.X₃.presheaf.stalk x)
    infer_instance
  have hz : IsZero (F.obj S.X₃) := ModuleCat.isZero_of_subsingleton _
  exact (hS.map_of_exact F).isIso_f_iff.mpr hz

/-- Every actual Serre extension of the twisted ideal has an actual rank-two
free affine neighborhood at every point outside the closed support point.
The local splitting and all quotient coordinates are constructed. -/
theorem cubicClosedPointSerreFreeNeighborhood_exists_away
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, T.over (V j) ≅ SheafOfModules.unit (X.ringCatSheaf.over (V j)))
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T))
    (x : X) (hx : x ≠ i default) :
    ∃ (W : X.Opens), x ∈ W ∧ IsAffineOpen W ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over W)
        (ULift.{u} (Fin 2)) ≅ e.E.over W) := by
  have hcover : (⨆ j, V j) = ⊤ := (Opens.coversTop_iff X V).mp hV
  have hxcover : x ∈ ⨆ j, V j := by rw [hcover]; trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hxcover
  obtain ⟨j, hxj⟩ := hxcover
  let B : X.Opens := ⟨({i default} : Set X)ᶜ, (fieldPoint_image_isClosed i).isOpen_compl⟩
  have hxB : x ∈ B := by exact hx
  obtain ⟨U, hU, hxU, hUB⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V j ⊓ B from ⟨hxj, hxB⟩)
  have hUV : U ≤ V j := hUB.trans inf_le_left
  have hUA : ∀ y ∈ U, y ≠ i default := by
    intro y hy
    exact (hUB hy).2
  let H := SheafOfModules.overMap X.ringCatSheaf (homOfLE hUV)
  let tU : T.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
    ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE hUV)).app T).symm ≪≫
      H.mapIso (eV j) ≪≫ SheafOfModules.overMapUnitIso (homOfLE hUV)
  let G := (Scheme.Modules.overEquiv U).functor
  let qT : T.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    ((Scheme.Modules.overFunctorEquiv U).app T).symm ≪≫ G.mapIso tU ≪≫
      TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf
  letI : PreservesFiniteLimits (schemeModuleTensorRight T) :=
    schemeModuleTensorRight_preservesFiniteLimits_of_coversTop_iso_unit V hV eV
  letI : PreservesFiniteColimits (schemeModuleTensorRight T) :=
    schemeModuleTensorRight_preservesFiniteColimits_of_coversTop_iso_unit V hV eV
  let R := Scheme.Modules.restrictFunctor U.ι
  let S := closedImmersionIdealTwistSequence i T
  letI : IsIso (R.map S.f) :=
    cubicClosedPointSerreFreeNeighborhood_ideal_restrict_isIso_away i T V hV eV U hUA
  let q : (closedImmersionIdealTwist i T).restrict U.ι ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    asIso (R.map S.f) ≪≫ R.mapIso (closedImmersionIdealTwistSequence_middleIso i T) ≪≫ qT
  exact cubicClosedPointSerreFreeNeighborhood_exists_of_local_quotient_unit_iso e U ⟨x, hxU⟩ q

end PfaffianDescent
