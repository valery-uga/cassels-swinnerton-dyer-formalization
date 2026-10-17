import PfaffianDescent.ProjectiveLinePoints
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
section
variable (K : Type u) [Field K]

lemma lineGrassmannian_chart_one :
    grassmannianChartEvaluation K (lineChartMatrix K 1) ≫ grassmannianChartι K (lineChartPermutation false) =
      grassmannianChartEvaluation K (lineChartMatrix K 1) ≫ grassmannianChartι K (lineChartPermutation true) := by
  apply (grassmannianChartEvaluation_eq_iff_submodule K _ _ _ _).mpr
  apply (lineGrassmannianChartSubmodule_eq_iff K false true 1 1).mpr
  simp

/-- The two irreducible affine line charts share their unit-slope point, so the line Grassmannian is connected. -/
instance lineGrassmannian_preconnected : PreconnectedSpace (grassmannianScheme K 1 1) := by
  have : PreconnectedSpace (grassmannianChartScheme K 1 1) :=
    inferInstanceAs (PreconnectedSpace (Spec (.of (GrassmannianChartRing K 1 1))))
  let f := grassmannianChartι K (lineChartPermutation false)
  let g := grassmannianChartι K (lineChartPermutation true)
  have hcover : Set.range f ∪ Set.range g = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨b, y, hy⟩ := (projectiveLineOpenCover K).exists_eq x
    change ULift.{u} Bool at b
    rcases b with ⟨b⟩
    cases b
    · exact Or.inl ⟨y, hy⟩
    · exact Or.inr ⟨y, hy⟩
  let p := grassmannianChartEvaluation K (lineChartMatrix K 1) (IsLocalRing.closedPoint K)
  have hp : f p = g p := congrArg (fun q : Spec (.of K) ⟶ grassmannianScheme K 1 1 =>
    q (IsLocalRing.closedPoint K)) (lineGrassmannian_chart_one K)
  apply preconnectedSpace_iff_univ.mpr
  rw [← hcover]
  exact (isPreconnected_range f.continuous).union' ⟨f p, ⟨p, rfl⟩, ⟨p, hp.symm⟩⟩
    (isPreconnected_range g.continuous)

/-- The standard Proj projective line is preconnected over every field. -/
instance projectiveLineProj_preconnected : PreconnectedSpace (projectiveLineProj K) :=
  (lineGrassmannianProjIso K).hom.surjective.denseRange.preconnectedSpace
    (lineGrassmannianProjIso K).hom.continuous

/-- A finite flat finitely presented family over the projective line has the same rank at zero and infinity. -/
theorem projectiveLine_finite_flat_rank {W : Scheme.{u}}
    (f : W ⟶ projectiveLineProj K) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    f.finrank (projectiveLineEndpoint K false (IsLocalRing.closedPoint K)) =
      f.finrank (projectiveLineEndpoint K true (IsLocalRing.closedPoint K)) :=
  f.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _

end
end PfaffianDescent
