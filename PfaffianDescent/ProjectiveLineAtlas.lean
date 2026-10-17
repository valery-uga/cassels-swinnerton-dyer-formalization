import PfaffianDescent.ProjectiveLineCharts
import PfaffianDescent.GrassmannianProper
import Mathlib.GroupTheory.Perm.Fin

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

lemma lineChartPermutation_bijective : Function.Bijective lineChartPermutation := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b h
    cases a <;> cases b <;> try rfl
    all_goals
      have he := congrArg (fun e : Equiv.Perm (Fin 1 ⊕ Fin 1) => e (Sum.inl 0)) h
      simp [lineChartPermutation] at he
  · norm_num [Fintype.card_perm, Fintype.card_sum]

section
variable (K : Type u) [CommRing K]

/-- The two standard affine charts cover the actual Grassmannian of lines in two-space. -/
noncomputable def projectiveLineOpenCover : Scheme.OpenCover.{u} (grassmannianScheme K 1 1) where
  I₀ := ULift.{u} Bool
  X _ := grassmannianChartScheme K 1 1
  f b := grassmannianChartι K (lineChartPermutation b.down)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      obtain ⟨i, y, hy⟩ := (grassmannianGlueData K 1 1).openCover.exists_eq x
      obtain ⟨b, hb⟩ := lineChartPermutation_bijective.surjective i.down
      refine ⟨⟨b⟩, y, ?_⟩
      change grassmannianChartι K (lineChartPermutation b) y = x
      rw [hb]
      exact hy
    · intro b
      exact grassmannianChartι_isOpenImmersion K (lineChartPermutation b.down)

end
end PfaffianDescent
