import PfaffianDescent.StalkPushforwardNaturality
import PfaffianDescent.LocalExtResidueInjective

/-!
# Exactness of pushforward along a closed immersion

Pushforward of sheaves of modules along a closed immersion is exact.  On a
point of the closed image, the pushforward stalk is naturally isomorphic to
the original stalk.  Away from the image, the pushforward stalk is zero.
These two descriptions reduce preservation of short exact sequences to the
stalkwise exactness theorem for scheme modules.
-/

noncomputable section

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology

universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- At a point in the source of an inducing scheme map, taking the stalk of
module-sheaf pushforward at its image agrees naturally with taking the
original stalk. -/
def schemeModulePushforwardStalkNatIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsInducing f.base) (x : X) :
    Scheme.Modules.pushforward f ⋙ schemeModuleStalkFunctor Y (f x) ≅
      schemeModuleStalkFunctor X x := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · letI : IsIso (M.presheaf.stalkPushforward AddCommGrpCat f.base x) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrpCat hf M.presheaf x
    exact asIso (M.presheaf.stalkPushforward AddCommGrpCat f.base x)
  · intro M N η
    exact (presheafStalkPushforwardNatTrans
      (C := AddCommGrpCat) f.base x).naturality
        ((Scheme.Modules.toPresheaf X).map η)

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Pushforward along a closed immersion preserves short exact sequences of
module sheaves. -/
theorem schemeModulePushforward_map_shortExact_of_closedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (Scheme.Modules.pushforward f)).ShortExact := by
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  have hstalk (y : Y) :
      ((S.map (Scheme.Modules.pushforward f)).map
        (schemeModuleStalkFunctor Y y)).ShortExact := by
    by_cases hy : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hy
      have hxS : (S.map (schemeModuleStalkFunctor X x)).ShortExact := by
        exact
          { exact := schemeModuleStalkFunctor_map_exact_of_shortExact x S hS
            mono_f := schemeModuleStalkFunctor_map_mono S.f x
            epi_g := schemeModuleStalkFunctor_map_epi S.g x }
      let e := ShortComplex.mapNatIso S
        (schemeModulePushforwardStalkNatIso f
          f.isClosedEmbedding.isInducing x)
      apply ShortComplex.shortExact_of_iso e.symm
      exact hxS
    · have hzero (M : X.Modules) :
          IsZero ((schemeModuleStalkFunctor Y y).obj
            ((Scheme.Modules.pushforward f).obj M)) := by
        change IsZero (AddCommGrpCat.of
          (((Scheme.Modules.pushforward f).obj M).presheaf.stalk y))
        let _ : Subsingleton
            (((Scheme.Modules.pushforward f).obj M).presheaf.stalk y) :=
          schemeModulePushforward_stalk_subsingleton_off_range f M y hy
        exact AddCommGrpCat.isZero_of_subsingleton _
      refine
        { exact := ?_
          mono_f := (hzero S.X₁).isTerminal.mono_from _
          epi_g := (hzero S.X₃).isInitial.epi_to _ }
      apply ShortComplex.exact_of_isZero_X₂
      exact hzero S.X₂
  let T := SheafOfModules.toSheaf.{u} Y.ringCatSheaf
  letI : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive T
  have hexact : (S.map (Scheme.Modules.pushforward f)).Exact := by
    apply Functor.reflects_exact_of_faithful T
    apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
    intro y
    change ((S.map (Scheme.Modules.pushforward f)).map
      (schemeModuleStalkFunctor Y y)).Exact
    exact (hstalk y).exact
  have hmono : Mono ((S.map (Scheme.Modules.pushforward f)).f) := by
    letI : PreservesFiniteLimits (Scheme.Modules.pushforward f) := by
      change PreservesFiniteLimits
        (SheafOfModules.pushforward f.toRingCatSheafHom)
      exact SheafOfModules.pushforward_preservesFiniteLimits _
    exact Functor.map_mono (Scheme.Modules.pushforward f) S.f
  have hepiSheaf : Epi (T.map ((S.map (Scheme.Modules.pushforward f)).g)) := by
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
    apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mpr
    intro y
    change Function.Surjective
      ((schemeModuleStalkFunctor Y y).map
        ((S.map (Scheme.Modules.pushforward f)).g))
    exact (AddCommGrpCat.epi_iff_surjective _).mp (hstalk y).epi_g
  have hepi : Epi ((S.map (Scheme.Modules.pushforward f)).g) := by
    constructor
    intro Z g h hgh
    apply T.map_injective
    rw [← cancel_epi (T.map ((S.map (Scheme.Modules.pushforward f)).g))]
    simpa only [← T.map_comp] using congrArg T.map hgh
  exact ⟨hexact⟩

/-- Pushforward of module sheaves along a closed immersion is exact. -/
noncomputable instance
    schemeModulePushforward_preservesFiniteColimits_of_closedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    PreservesFiniteColimits (Scheme.Modules.pushforward f) := by
  have h := ((Functor.exact_tfae (Scheme.Modules.pushforward f)).out 0 3).mp
    (schemeModulePushforward_map_shortExact_of_closedImmersion f)
  exact h.2

/-- Degree-one cohomology of a module on a closed subscheme vanishes whenever
degree-one cohomology of its pushforward to the ambient scheme vanishes. -/
theorem schemeModuleCohomology_one_subsingleton_of_closedImmersion_pushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    [HasExt.{u} Y.Modules] [HasExt.{u} X.Modules]
    [EnoughInjectives X.Modules]
    (M : X.Modules)
    [Subsingleton (schemeModuleCohomology Y
      ((Scheme.Modules.pushforward f).obj M) 1)] :
    Subsingleton (schemeModuleCohomology X M 1) := by
  exact schemeModuleCohomology_one_subsingleton_of_pushforward f M

end PfaffianDescent
