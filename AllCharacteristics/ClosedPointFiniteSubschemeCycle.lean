import AllCharacteristics.ClosedPointFiniteSubscheme
import AllCharacteristics.FiniteSubschemeRank
import PfaffianDescent.EffectiveSignedPushforward
import PfaffianDescent.ResidualCycles

/-!
# Cycles of closed-point finite-subscheme data

The canonical finite-subscheme datum attached to a closed point carries that
closed point itself, with multiplicity one, as its intrinsic zero-cycle.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics

universe u

/-- The canonical cycle of the finite-subscheme datum of a closed point is
the one-term cycle supported at that point. -/
theorem finiteSubschemeDatumCycle_closedPoint
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : closedPoints X) :
    finiteSubschemeDatumCycle f (finiteSubschemeDatumOfClosedPoint f x) =
      Finsupp.single x 1 := by
  let q : Spec (.of (X.residueField x.1)) ⟶ X := X.fromSpecResidueField x.1
  letI : IsClosedImmersion q := by
    dsimp only [q]
    exact isClosed_singleton_iff_isClosedImmersion.mp x.2
  letI : IsFinite (q ≫ f) := by
    dsimp only [q]
    infer_instance
  letI : Algebra k (X.residueField x.1) := pointAlgebra f x.1
  letI : Module.Finite k (X.residueField x.1) := closedPoint_moduleFinite f x
  letI : Flat (q ≫ f) := by
    rw [← pointAlgebra_spec f x.1]
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  letI : Module.FinitePresentation k (X.residueField x.1) :=
    Module.finitePresentation_of_finite k (X.residueField x.1)
  letI : Algebra.FinitePresentation k (X.residueField x.1) :=
    Algebra.FinitePresentation.of_finitePresentation k (X.residueField x.1)
  letI : LocallyOfFinitePresentation (q ≫ f) := by
    rw [← pointAlgebra_spec f x.1]
    exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have hcycle := finiteSubschemeDatumCycle_of_closedImmersion q f
    (f.residueDegree x.1) (fun s ↦ by
      have hs : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      subst s
      exact (finiteSchemeRank_eq_finrank (q ≫ f)).symm.trans
        (closedPoint_finiteSchemeRank_eq_residueDegree f x))
  let y : closedPoints (Spec (.of (X.residueField x.1))) :=
    ⟨IsLocalRing.closedPoint (X.residueField x.1), isClosed_singleton⟩
  have hfund : PfaffianDescent.finiteSchemeFundamentalCycle (q ≫ f) =
      Finsupp.single y 1 := by
    change fundamentalZeroCycle (Spec (.of (X.residueField x.1))) = _
    exact fundamentalZeroCycle_Spec_field (X.residueField x.1) y
  have himage : universallyClosedPointMap q y = x := by
    apply Subtype.ext
    change q (IsLocalRing.closedPoint (X.residueField x.1)) = x.1
    exact X.fromSpecResidueField_apply x.1
      (IsLocalRing.closedPoint (X.residueField x.1))
  have hcycle' : finiteSubschemeDatumCycle f (finiteSubschemeDatumOfClosedPoint f x) =
      Finsupp.single x (q.residueDegree y.1) := by
    calc
      finiteSubschemeDatumCycle f (finiteSubschemeDatumOfClosedPoint f x) =
          pushforwardCycle q (PfaffianDescent.finiteSchemeFundamentalCycle (q ≫ f)) := by
            simpa only [finiteSubschemeDatumOfClosedPoint] using hcycle
      _ = pushforwardCycle q (Finsupp.single y 1) := by rw [hfund]
      _ = Finsupp.single (universallyClosedPointMap q y)
          (1 * q.residueDegree y.1) :=
        PfaffianDescent.effectiveCyclePushforward_single q y 1
      _ = Finsupp.single x (q.residueDegree y.1) := by rw [himage, one_mul]
  have hdegree := finiteSubschemeDatumCycle_degree f
    (finiteSubschemeDatumOfClosedPoint f x)
  have hdegree' : q.residueDegree y.1 * f.residueDegree x.1 = f.residueDegree x.1 := by
    rw [hcycle', PfaffianDescent.effectiveCycle_degree_single] at hdegree
    exact hdegree
  have hpos : 0 < f.residueDegree x.1 := by
    rw [← closedPoint_finrank_eq_residueDegree f x]
    exact Module.finrank_pos
  have hcoeff : q.residueDegree y.1 = 1 := by
    apply mul_right_cancel₀ hpos.ne'
    simpa using hdegree'
  rw [hcycle', hcoeff]

/-- Reindexing the closed-point finite datum by a stated residue degree does
not change its canonical cycle. -/
theorem finiteSubschemeDatumCycle_closedPoint_of_residueDegree
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : closedPoints X) (n : ℕ)
    (hx : f.residueDegree x.1 = n) :
    finiteSubschemeDatumCycle f
      (finiteSubschemeDatumOfClosedPointOfResidueDegree f x n hx) =
      Finsupp.single x 1 := by
  cases hx
  exact finiteSubschemeDatumCycle_closedPoint f x

end AllCharacteristics
