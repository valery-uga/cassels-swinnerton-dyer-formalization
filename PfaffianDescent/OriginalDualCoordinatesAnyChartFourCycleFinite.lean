import PfaffianDescent.ConjugateTangentCoordinatePermutationInvariant
import PfaffianDescent.OriginalDualCoordinatesFourCycleGroundFullBaseFinite

/-! SOURCE ONLY, UNVERIFIED. The C4 finiteness consumer on the SAME original
coordinates and full intrinsic ideal. The temporary normalization at zero
is an actual permutation, and the embedding-indexed matrix is proved equal. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k L A : Type u} [Field k] [PerfectField k] [Field L] [CommRing A]
  [Algebra k L] [Algebra k A] [FiniteDimensional k L]
  [Algebra.IsSeparable k L] [FiniteDimensional k A]

theorem originalDualCoordinates_any_chart_fourCycle_groundFullBase_isFinite
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (j : Fin 4) (hxj : x j = 1) (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b j = 1) (hv : v j = 0)
    (full : Fin 4 ≃ (L →ₐ[k] AlgebraicClosure k))
    (l : Fin 4 → AlgebraicClosure k) (hl : ∀ r, l r ≠ 0)
    (rho : Equiv.Perm (Fin 4)) :
    let hs := conjugate_basis_span b full
    let U := rescaleTangentDirections l (conjugateTangentMatrix full b v hs)
    let V := tangentRelabel U rho
    (∀ r s, V r s = -V s r) →
    V 0 1 = 0 → V 2 3 = 0 →
    V 0 2 ≠ 0 → V 0 3 ≠ 0 → V 1 2 ≠ 0 → V 1 3 ≠ 0 →
    IsFinite (toBase (intrinsicFullQuadraticBaseIdeal
      (ambientNormalizedCoordinateChartPoint (F := k) x j hxj))) := by
  classical
  dsimp only
  intro hskew h01 h23 h02 h03 h12 h13
  let pi := Equiv.swap (0 : Fin 4) j
  let b' := b.reindex pi.symm
  let v' : Fin 4 → L := fun r => v (pi r)
  have hpi : pi 0 = j := by simp [pi]
  have hx' (r : Fin 4) : eA (x (pi r)) =
      TrivSqZeroExt.inl (b' r) + TrivSqZeroExt.inr (v' r) := by
    simpa only [b', v', Basis.reindex_apply, Equiv.symm_symm] using hx (pi r)
  have hb' : b' 0 = 1 := by
    simpa only [b', Basis.reindex_apply, Equiv.symm_symm, hpi] using hb
  have hv' : v' 0 = 0 := by simpa only [v', hpi] using hv
  have hU := conjugateTangentMatrix_basis_coordinate_permutation full b v pi
  simpa only [b', v', hU] using
    originalDualCoordinates_fourCycle_groundFullBase_isFinite
      eA x j hxj pi hpi b' v' hx' hb' hv' full l hl rho
      (by simpa only [b', v', hU] using hskew)
      (by simpa only [b', v', hU] using h01)
      (by simpa only [b', v', hU] using h23)
      (by simpa only [b', v', hU] using h02)
      (by simpa only [b', v', hU] using h03)
      (by simpa only [b', v', hU] using h12)
      (by simpa only [b', v', hU] using h13)

end PfaffianDescent.QuarticNet
