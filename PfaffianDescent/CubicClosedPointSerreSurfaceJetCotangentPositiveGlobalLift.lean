import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveIdealTwist
import PfaffianDescent.FiniteProjectiveProjectionFormula

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Literal inclusion of the actual positive-three ideal into the actual positive twist. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveIdealInclusion
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i] :
    closedImmersionIdealTwist i (positiveSheafOfModules (grading I) 3) ⟶
      positiveSheafOfModules (grading I) 3 :=
  (closedImmersionIdealTwistSequence i (positiveSheafOfModules (grading I) 3)).f ≫
    (schemeModuleTensorUnitLeftIso (positiveSheafOfModules (grading I) 3)).hom

/-- The native positive twist supplies exactness internally. A cubic-section
map in its literal quotient kernel has a unique actual global ideal-section lift. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveIdealGlobalLift
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    (s : SheafOfModules.unit (scheme I).ringCatSheaf ⟶
      positiveSheafOfModules (grading I) 3)
    (hs : s ≫ (schemeModuleTensorUnitLeftIso
        (positiveSheafOfModules (grading I) 3)).inv ≫
      (closedImmersionIdealTwistSequence i
        (positiveSheafOfModules (grading I) 3)).g = 0) :
    ∃! t : SheafOfModules.unit (scheme I).ringCatSheaf ⟶
        closedImmersionIdealTwist i (positiveSheafOfModules (grading I) 3),
      t ≫ cubicClosedPointSerreSurfaceJetCotangent_positiveIdealInclusion I i = s := by
  let T := positiveSheafOfModules (grading I) 3
  let C := closedImmersionIdealTwistSequence i T
  let e := schemeModuleTensorUnitLeftIso T
  letI : PreservesFiniteLimits (schemeModuleTensorRight T) :=
    quotientPositiveTwist_tensorRight_preservesFiniteLimits I 3
  letI : PreservesFiniteColimits (schemeModuleTensorRight T) :=
    quotientPositiveTwist_tensorRight_preservesFiniteColimits I 3
  have he : C.ShortExact := closedImmersionIdealTwistSequence_shortExact i T
  let l := he.fIsKernel.lift (KernelFork.ofι (s ≫ e.inv) hs)
  have hl : l ≫ C.f = s ≫ e.inv :=
    he.fIsKernel.fac (KernelFork.ofι (s ≫ e.inv) hs) WalkingParallelPair.zero
  refine ⟨l, ?_, ?_⟩
  · change l ≫ C.f ≫ e.hom = s
    rw [← Category.assoc, hl]
    simp
  · intro t ht
    letI : Mono C.f := he.mono_f
    apply (cancel_mono C.f).mp
    rw [hl]
    change t ≫ C.f ≫ e.hom = s at ht
    have h := congrArg (fun a => a ≫ e.inv) ht
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

/-- A morphism into a sheaf supported on an open chart vanishes globally
when its literal restriction vanishes. This applies to the actual twisted
closed-immersion quotient by its checked restriction-unit isomorphism. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_eq_zero_of_restrict
    {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules}
    [IsIso ((Scheme.Modules.restrictAdjunction U.ι).unit.app N)]
    (a : M ⟶ N)
    (ha : (Scheme.Modules.restrictFunctor U.ι).map a = 0) : a = 0 := by
  apply (cancel_mono ((Scheme.Modules.restrictAdjunction U.ι).unit.app N)).mp
  rw [CategoryTheory.Limits.zero_comp]
  have h := (Scheme.Modules.restrictAdjunction U.ι).unit.naturality a
  rw [Functor.comp_map, ha, Functor.map_zero, CategoryTheory.Limits.comp_zero] at h
  simpa only [Functor.id_map] using h

end PfaffianDescent
