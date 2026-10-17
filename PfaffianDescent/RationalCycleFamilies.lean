import PfaffianDescent.IntrinsicFiniteCycle
import PfaffianDescent.ProjectiveLineConnected

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
universe u
section
variable {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsSeparated p]

/-- A finite flat curve family over the projective line, mapped to the scheme over the ground field. -/
structure RationalCycleFamily where
  curve : Scheme.{u}
  toLine : curve ⟶ projectiveLineProj K
  finite : IsFinite toLine
  flat : Flat toLine
  finitelyPresented : LocallyOfFinitePresentation toLine
  toScheme : curve ⟶ X
  overBase : toScheme ≫ p = toLine ≫ projectiveLineProjToBase K

attribute [instance] RationalCycleFamily.finite RationalCycleFamily.flat RationalCycleFamily.finitelyPresented

variable {p}

/-- The actual fiber at zero or infinity of a curve family. -/
noncomputable abbrev RationalCycleFamily.fiber (F : RationalCycleFamily p) (b : Bool) : Scheme.{u} :=
  pullback F.toLine (projectiveLineEndpoint K b)

noncomputable def RationalCycleFamily.fiberToScheme (F : RationalCycleFamily p) (b : Bool) : F.fiber b ⟶ X :=
  pullback.fst F.toLine (projectiveLineEndpoint K b) ≫ F.toScheme

lemma RationalCycleFamily.fiberToScheme_toBase (F : RationalCycleFamily p) (b : Bool) :
    F.fiberToScheme b ≫ p = pullback.snd F.toLine (projectiveLineEndpoint K b) := by
  change (pullback.fst _ _ ≫ F.toScheme) ≫ p = _
  rw [Category.assoc, F.overBase, ← Category.assoc, pullback.condition, Category.assoc,
    projectiveLineEndpoint_toBase, Category.comp_id]

instance RationalCycleFamily.fiberToScheme_isFinite (F : RationalCycleFamily p) (b : Bool) :
    IsFinite (F.fiberToScheme b) := by
  have : IsFinite (F.fiberToScheme b ≫ p) := by
    rw [F.fiberToScheme_toBase]
    infer_instance
  exact IsFinite.of_comp _ p

/-- The fiber cycle uses actual local lengths and actual residue-field pushforward degrees. -/
noncomputable def RationalCycleFamily.fiberCycle (F : RationalCycleFamily p) (b : Bool) : EffectiveZeroCycle X :=
  pushforwardCycle (F.fiberToScheme b)
    (finiteSchemeFundamentalCycle (pullback.snd F.toLine (projectiveLineEndpoint K b)))

lemma RationalCycleFamily.fiberCycle_degree (F : RationalCycleFamily p) (b : Bool) :
    EffectiveZeroCycle.degree p (F.fiberCycle b) =
      F.toLine.finrank (projectiveLineEndpoint K b (IsLocalRing.closedPoint K)) := by
  rw [RationalCycleFamily.fiberCycle, degree_pushforwardCycle, F.fiberToScheme_toBase]
  exact finiteFiberFundamentalCycle_degree F.toLine (projectiveLineEndpoint K b)

/-- Zero and infinity fibers have the same scheme-theoretic degree. -/
theorem RationalCycleFamily.fiberCycle_degree_eq (F : RationalCycleFamily p) :
    EffectiveZeroCycle.degree p (F.fiberCycle false) = EffectiveZeroCycle.degree p (F.fiberCycle true) :=
  (F.fiberCycle_degree false).trans
    ((projectiveLine_finite_flat_rank K F.toLine).trans (F.fiberCycle_degree true).symm)

/-- The signed difference of the actual zero and infinity fiber cycles. -/
noncomputable def RationalCycleFamily.cycleDifference (F : RationalCycleFamily p) : ZeroCycle X :=
  (F.fiberCycle false).toZeroCycle - (F.fiberCycle true).toZeroCycle

lemma RationalCycleFamily.cycleDifference_degree (F : RationalCycleFamily p) :
    ZeroCycle.degree p F.cycleDifference = 0 := by
  change ZeroCycle.degree p ((F.fiberCycle false).toZeroCycle - (F.fiberCycle true).toZeroCycle) = 0
  rw [map_sub, EffectiveZeroCycle.degree_toZeroCycle, EffectiveZeroCycle.degree_toZeroCycle,
    F.fiberCycle_degree_eq, sub_self]

end
end PfaffianDescent
