import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free

/-! SOURCE ONLY, UNVERIFIED. Exact finite-coordinate rank descent across
ANY field extension. No Algebra.IsEpi or presumed matrix-rank certificate. -/
noncomputable section
namespace PfaffianDescent
open Module
universe u
variable {E K : Type u} [Field E] [Field K] [Algebra E K]

theorem coefficientVector_mem_span
    {J : Type*} (v : J → Fin 4 → E) (w : Fin 4 → E)
    (hw : w ∈ Submodule.span E (Set.range v)) :
    (fun m => algebraMap E K (w m)) ∈
      Submodule.span K (Set.range (fun j m => algebraMap E K (v j m))) := by
  classical
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨j, rfl⟩ := hw
    exact Submodule.subset_span ⟨j, rfl⟩
  | zero =>
    have he : (fun m : Fin 4 => algebraMap E K ((0 : Fin 4 → E) m)) = 0 := by
      funext m
      exact map_zero _
    rw [he]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    have he : (fun m => algebraMap E K ((x + y) m)) =
        (fun m => algebraMap E K (x m)) + (fun m => algebraMap E K (y m)) := by
      funext m
      exact map_add _ _ _
    rw [he]
    exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    have he : (fun m => algebraMap E K ((a • x) m)) =
        algebraMap E K a • (fun m => algebraMap E K (x m)) := by
      funext m
      exact map_mul _ _ _
    rw [he]
    exact Submodule.smul_mem _ (algebraMap E K a) ih

theorem finiteCoordinateSpan_fieldExtension_finrank
    (v : Fin 4 → Fin 4 → E) :
    finrank K (Submodule.span K
      (Set.range (fun j m => algebraMap E K (v j m)))) =
      finrank E (Submodule.span E (Set.range v)) := by
  classical
  let W := Submodule.span E (Set.range v)
  let b := Module.finBasis E W
  let bv := fun i => (b i : Fin 4 → E)
  have hbspan : Submodule.span E (Set.range bv) = W := by
    have h := congrArg (fun S : Submodule E W => S.map W.subtype) b.span_eq
    simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
      Submodule.map_subtype_top, Submodule.subtype_apply, bv] using h
  have hbLI : LinearIndependent E bv :=
    b.linearIndependent.map' W.subtype W.ker_subtype
  have hbLIK : LinearIndependent K (fun i m => algebraMap E K (bv i m)) :=
    linearIndependent_algebraMap_comp_iff.mpr hbLI
  have hspan : Submodule.span K (Set.range (fun j m => algebraMap E K (v j m))) =
      Submodule.span K (Set.range (fun i m => algebraMap E K (bv i m))) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro w ⟨j, rfl⟩
      apply coefficientVector_mem_span (K := K) bv (v j)
      rw [hbspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    · apply Submodule.span_le.mpr
      rintro w ⟨i, rfl⟩
      exact coefficientVector_mem_span (K := K) v (bv i) (b i).property
  rw [hspan]
  simpa only [Fintype.card_fin] using (finrank_span_eq_card hbLIK)

theorem finiteCoordinateMatrix_fieldExtension_rank
    (M : Matrix (Fin 4) (Fin 4) E) :
    (M.map (algebraMap E K)).rank = M.rank := by
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  exact finiteCoordinateSpan_fieldExtension_finrank (K := K) M.col

end PfaffianDescent
