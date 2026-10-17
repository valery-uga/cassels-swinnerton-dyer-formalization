import PfaffianDescent.QuarticConjugateCoordinates

/-! SOURCE ONLY, UNVERIFIED. Nonzero tangent rows use the actual normalized
chart j, without reordering the original cubic's coordinates. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K]

theorem conjugateTangentMatrix_row_nonzero_at_normalized_chart
    (full : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p m))) = ⊤)
    (j : Fin 4) (hp : p j = 1) (hvj : v j = 0) (hv : v ≠ 0) (i : Fin 4) :
    ∃ r, conjugateTangentMatrix full p v hspan i r ≠ 0 := by
  classical
  by_contra! h
  let b := conjugateBasis full p hspan
  let x : Fin 4 → K := fun m => full i (v m)
  have hz (r : Fin 4) (hr : r ≠ i) : b.repr x r = 0 := by
    simpa only [conjugateTangentMatrix, Ne.symm hr, if_false, conjugateTangentRow, b, x]
      using h r
  have hRadial : x = b.repr x i • b i := by
    calc
      x = ∑ r, b.repr x r • b r := (b.sum_repr x).symm
      _ = _ := Finset.sum_eq_single i (fun r _ hr => by rw [hz r hr, zero_smul])
        (fun hi => (hi (Finset.mem_univ i)).elim)
  have hCoefficient : b.repr x i = 0 := by
    have h := congrFun hRadial j
    simpa only [x, hvj, map_zero, Pi.smul_apply, smul_eq_mul, b,
      conjugateBasis_apply, hp, map_one, mul_one] using h.symm
  rw [hCoefficient, zero_smul] at hRadial
  apply hv
  funext r
  exact (map_eq_zero (full i)).mp (congrFun hRadial r)

end PfaffianDescent.QuarticNet
