import PfaffianDescent.QuarticConjugateCoordinates
import PfaffianDescent.QuarticConjugateSpan

/-! SOURCE ONLY, UNVERIFIED. A simultaneous permutation of the ambient
coordinates of the point and tangent vector leaves the embedding-indexed
tangent matrix unchanged. No independent canonical extraction is compared. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K]

theorem conjugateTangentRow_coordinate_permutation
    (full : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (pi : Equiv.Perm (Fin 4))
    (hs : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p m))) = ⊤)
    (hs' : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p (pi m)))) = ⊤) (i r : Fin 4) :
    conjugateTangentRow full (fun m => p (pi m)) (fun m => v (pi m)) hs' i r =
      conjugateTangentRow full p v hs i r := by
  classical
  let b := conjugateBasis full p hs
  let b' := conjugateBasis full (fun m => p (pi m)) hs'
  let x : Fin 4 → K := fun m => full i (v m)
  let x' : Fin 4 → K := fun m => full i (v (pi m))
  have hexp : x' = ∑ s, b.repr x s • b' s := by
    funext m
    have h := congrFun (b.sum_repr x) (pi m)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b, b', x, x',
      conjugateBasis_apply] using h.symm
  change b'.repr x' r = b.repr x r
  rw [hexp, map_sum, Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

theorem conjugateTangentMatrix_basis_coordinate_permutation
    [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (full : Fin 4 ≃ (L →ₐ[k] K)) (b : Basis (Fin 4) k L)
    (v : Fin 4 → L) (pi : Equiv.Perm (Fin 4)) :
    conjugateTangentMatrix full (b.reindex pi.symm) (fun m => v (pi m))
      (conjugate_basis_span (b.reindex pi.symm) full) =
      conjugateTangentMatrix full b v (conjugate_basis_span b full) := by
  classical
  have hb : (b.reindex pi.symm : Fin 4 → L) = fun m => b (pi m) := by
    funext m
    exact Basis.reindex_apply b pi.symm m
  have hs' : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (b (pi m)))) = ⊤ := by
    simpa only [hb] using conjugate_basis_span (b.reindex pi.symm) full
  funext i r
  simp only [conjugateTangentMatrix, hb]
  exact congrArg (fun z : K => if i = r then 0 else z)
    (conjugateTangentRow_coordinate_permutation full b v pi
      (conjugate_basis_span b full) hs' i r)

end PfaffianDescent.QuarticNet
