import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualVanishing
import Mathlib.CategoryTheory.Whiskering

/-! # Actual vanishing after restriction to a zero-locus chart -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_map_zero_of_natIso
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {F G : C ⥤ D} (a : F ≅ G) {M N : C} (f : M ⟶ N)
    (hf : G.map f = 0) : F.map f = 0 := by
  apply (cancel_mono (a.hom.app N)).mp
  rw [a.hom.naturality, hf, comp_zero, zero_comp]

theorem cubicClosedPointSerreFiniteZeroResidual_restricted_pullback_zero
    {X Z : Scheme.{u}} (j : Z ⟶ X) (U : X.Opens)
    {M N : X.Modules} (a : M ⟶ N)
    (ha : (Scheme.Modules.pullback j).map a = 0) :
    (Scheme.Modules.pullback (pullback.snd j U.ι)).map
      ((Scheme.Modules.restrictFunctor U.ι).map a) = 0 := by
  let k := pullback.fst j U.ι
  let l := pullback.snd j U.ι
  let e : (Scheme.Modules.pullback U.ι) ⋙ (Scheme.Modules.pullback l) ≅
      (Scheme.Modules.pullback j) ⋙ (Scheme.Modules.pullback k) :=
    Scheme.Modules.pullbackComp l U.ι ≪≫
      Scheme.Modules.pullbackCongr (pullback.condition (f := j) (g := U.ι)).symm ≪≫
      (Scheme.Modules.pullbackComp k j).symm
  have h : (Scheme.Modules.pullback l).map ((Scheme.Modules.pullback U.ι).map a) = 0 := by
    apply cubicClosedPointSerreFiniteZeroResidual_map_zero_of_natIso e a
    change (Scheme.Modules.pullback k).map ((Scheme.Modules.pullback j).map a) = 0
    rw [ha, Functor.map_zero]
  apply cubicClosedPointSerreFiniteZeroResidual_map_zero_of_natIso
    (Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι)
      (Scheme.Modules.pullback l)) a
  exact h

theorem cubicClosedPointSerreFiniteZeroResidual_over_section_pullback_zero
    {X Z : Scheme.{u}} (j : Z ⟶ X) (U : X.Opens)
    (E : X.Modules) (s : E.sections)
    (hs : (Scheme.Modules.pullback j).map (E.unitHomEquiv.symm s) = 0) :
    (Scheme.Modules.pullback (pullback.snd j U.ι)).map
      (((Scheme.Modules.overEquiv U).functor.obj (E.over U)).unitHomEquiv.symm
        (BundleSectionZeroLocus.restrictSectionToOpen U s)) = 0 := by
  unfold BundleSectionZeroLocus.restrictSectionToOpen
  rw [Equiv.symm_apply_apply]
  apply cubicClosedPointSerreFiniteZeroResidual_map_zero_of_natIso
    (Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U)
      (Scheme.Modules.pullback (pullback.snd j U.ι))) (E.unitHomEquiv.symm s)
  exact cubicClosedPointSerreFiniteZeroResidual_restricted_pullback_zero j U _ hs

end PfaffianDescent
