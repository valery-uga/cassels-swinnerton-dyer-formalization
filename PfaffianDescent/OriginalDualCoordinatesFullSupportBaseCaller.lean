import PfaffianDescent.ActualQuarticOriginalGroundFullBaseAlternative
import PfaffianDescent.ConjugateTangentCoordinatePermutationInvariant

/-! SOURCE ONLY. The same ORIGINAL coordinate basis is normalized at its
actual chart index; the embedding-indexed tangent matrix is unchanged. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k L A : Type u} [Field k] [PerfectField k] [Field L] [CommRing A]
  [Algebra k L] [Algebra k A] [FiniteDimensional k L]
  [Algebra.IsSeparable k L] [FiniteDimensional k A]

theorem originalDualCoordinates_any_chart_full_support_fullBase_alternative
    (eA : A ≃ₐ[k] DualNumber L) (x : Fin 4 → A)
    (hgen : Function.Surjective (aeval (R := k) x))
    (j : Fin 4) (hxj : x j = 1) (b : Basis (Fin 4) k L) (v : Fin 4 → L)
    (hx : ∀ r, eA (x r) = TrivSqZeroExt.inl (b r) + TrivSqZeroExt.inr (v r))
    (hb : b j = 1) (hv : v j = 0)
    (full : Fin 4 ≃ (L →ₐ[k] AlgebraicClosure k))
    (l : Fin 4 → AlgebraicClosure k) (hl : ∀ r, l r ≠ 0)
    (hskew : ∀ r s, l r * conjugateTangentMatrix full b v (conjugate_basis_span b full) r s =
      -(l s * conjugateTangentMatrix full b v (conjugate_basis_span b full) s r))
    (hnonzero : ∀ r s, r ≠ s →
      conjugateTangentMatrix full b v (conjugate_basis_span b full) r s ≠ 0) :
    IntrinsicFullBaseEmbeddedAlternative (ambientNormalizedCoordinateChartPoint (F := k) x j hxj) := by
  classical
  let pi : Equiv.Perm (Fin 4) := Equiv.swap 0 j
  let b' := b.reindex pi.symm
  let v' : Fin 4 → L := fun m => v (pi m)
  have hpi : pi 0 = j := Equiv.swap_apply_left 0 j
  have hx' : ∀ r, eA (x (pi r)) = TrivSqZeroExt.inl (b' r) + TrivSqZeroExt.inr (v' r) := by
    intro r
    simpa only [b', Basis.reindex_apply, Equiv.symm_symm, v'] using hx (pi r)
  have hb' : b' 0 = 1 := by
    simpa only [b', Basis.reindex_apply, Equiv.symm_symm, hpi] using hb
  have hv' : v' 0 = 0 := by
    simpa only [v', hpi] using hv
  have hMatrix : conjugateTangentMatrix full b' v' (conjugate_basis_span b' full) =
      conjugateTangentMatrix full b v (conjugate_basis_span b full) :=
    conjugateTangentMatrix_basis_coordinate_permutation full b v pi
  have hskew' : ∀ r s, l r * conjugateTangentMatrix full b' v' (conjugate_basis_span b' full) r s =
      -(l s * conjugateTangentMatrix full b' v' (conjugate_basis_span b' full) s r) := by
    rw [hMatrix]
    exact hskew
  have hnonzero' : ∀ r s, r ≠ s →
      conjugateTangentMatrix full b' v' (conjugate_basis_span b' full) r s ≠ 0 := by
    rw [hMatrix]
    exact hnonzero
  exact actualQuarticOriginalGround_fullBase_embedded_alternative
    eA x hgen j hxj pi hpi b' v' hx' hb' hv' full l hl hskew' hnonzero'

end PfaffianDescent.QuarticNet
