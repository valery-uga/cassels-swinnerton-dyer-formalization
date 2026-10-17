import PfaffianDescent.ProjectiveLineConnected
import Mathlib.Topology.Sets.OpenCover

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_lineGrassmannian_preirreducible
    (K : Type u) [Field K] : PreirreducibleSpace (grassmannianScheme K 1 1) := by
  let f := fun b : Bool => grassmannianChartι K (lineChartPermutation b)
  let U := fun b : Bool => (f b).opensRange
  have hU : IsOpenCover U := by
    change (⨆ b, U b) = ⊤
    apply top_unique
    intro x hx
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨b, y, hy⟩ := (projectiveLineOpenCover K).exists_eq x
    change ULift.{u} Bool at b
    exact ⟨b.down, y, hy⟩
  have h : ∀ b, PreirreducibleSpace (U b) := by
    intro b
    have : PreirreducibleSpace (grassmannianChartScheme K 1 1) :=
      inferInstanceAs (PreirreducibleSpace (Spec (.of (GrassmannianChartRing K 1 1))))
    exact (f b).isoOpensRange.hom.surjective.preirreducibleSpace
      (f b).isoOpensRange.hom.continuous
  have hn : Pairwise (fun b c => ¬ Disjoint (U b) (U c)) := by
    intro b c hbc
    let p := grassmannianChartEvaluation K (lineChartMatrix K 1) (IsLocalRing.closedPoint K)
    have hp : f false p = f true p := congrArg
      (fun q : Spec (.of K) ⟶ grassmannianScheme K 1 1 => q (IsLocalRing.closedPoint K))
      (lineGrassmannian_chart_one K)
    rw [← TopologicalSpace.Opens.coe_disjoint]
    apply Set.not_disjoint_iff_nonempty_inter.mpr
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact ⟨f false p, ⟨p, rfl⟩, ⟨p, hp.symm⟩⟩
    · exact ⟨f true p, ⟨p, rfl⟩, ⟨p, hp⟩⟩
    · exact (hbc rfl).elim
  exact PreirreducibleSpace.of_isOpenCover hn hU h

theorem cubicClosedPointSerreFiniteZeroResidual_projectiveLine_preirreducible
    (K : Type u) [Field K] : PreirreducibleSpace (projectiveLineProj K) := by
  letI := cubicClosedPointSerreFiniteZeroResidual_lineGrassmannian_preirreducible K
  exact (lineGrassmannianProjIso K).hom.surjective.preirreducibleSpace
    (lineGrassmannianProjIso K).hom.continuous

end PfaffianDescent
