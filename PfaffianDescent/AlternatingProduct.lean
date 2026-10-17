import PfaffianDescent.AlternatingCoordinates
import Mathlib.LinearAlgebra.Prod

namespace PfaffianDescent
section
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- The off-diagonal block of an alternating form on a direct sum. -/
def alternatingMixedBlock (B : AlternatingTwoForms R (M × N)) : M →ₗ[R] N →ₗ[R] R :=
  (alternatingBilinear B).compl₁₂ (LinearMap.inl R M N) (LinearMap.inr R M N)

@[simp] lemma alternatingMixedBlock_apply (B : AlternatingTwoForms R (M × N)) (x : M) (y : N) :
    alternatingMixedBlock B x y = B ![(x, 0), (0, y)] := rfl

/-- An arbitrary mixed bilinear block extends to an alternating form. -/
def alternatingCross (Q : M →ₗ[R] N →ₗ[R] R) : AlternatingTwoForms R (M × N) where
  toFun v := Q (v 0).1 (v 1).2 - Q (v 1).1 (v 0).2
  map_update_add' v i x y := by
    fin_cases i <;> simp [map_add, sub_add_sub_comm]
  map_update_smul' v i c x := by
    fin_cases i <;> simp [mul_sub]
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j <;> simp_all

@[simp] lemma alternatingCross_apply (Q : M →ₗ[R] N →ₗ[R] R) (v : Fin 2 → M × N) :
    alternatingCross Q v = Q (v 0).1 (v 1).2 - Q (v 1).1 (v 0).2 := rfl

lemma alternating_comp_pair {P : Type*} [AddCommGroup P] [Module R P]
    (B : AlternatingTwoForms R P) (f : M →ₗ[R] P) (x y : M) :
    (B.compLinearMap f) ![x, y] = B ![f x, f y] := by
  change B (f ∘ ![x, y]) = _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Reassemble the three blocks of an alternating form. -/
def alternatingBlocksAssemble (A : AlternatingTwoForms R M)
    (Q : M →ₗ[R] N →ₗ[R] R) (C : AlternatingTwoForms R N) :
    AlternatingTwoForms R (M × N) :=
  A.compLinearMap (LinearMap.fst R M N) + alternatingCross Q +
    C.compLinearMap (LinearMap.snd R M N)

lemma alternatingBlocksAssemble_pair (A : AlternatingTwoForms R M)
    (Q : M →ₗ[R] N →ₗ[R] R) (C : AlternatingTwoForms R N) (x y : M × N) :
    alternatingBlocksAssemble A Q C ![x, y] =
      A ![x.1, y.1] + Q x.1 y.2 - Q y.1 x.2 + C ![x.2, y.2] := by
  simp only [alternatingBlocksAssemble, AlternatingMap.add_apply, alternating_comp_pair]
  simp [add_sub_assoc]

lemma alternatingBilinear_product (B : AlternatingTwoForms R (M × N))
    (a c : M) (b d : N) :
    alternatingBilinear B (a, b) (c, d) =
      alternatingBilinear B (a, 0) (c, 0) +
      alternatingBilinear B (a, 0) (0, d) -
      alternatingBilinear B (c, 0) (0, b) +
      alternatingBilinear B (0, b) (0, d) := by
  have h₁ : (a, b) = (a, 0) + (0, b) := by simp
  have h₂ : (c, d) = (c, 0) + (0, d) := by simp
  conv_lhs => rw [h₁, h₂]
  simp only [map_add, LinearMap.add_apply]
  rw [alternatingBilinear_swap B (0, b) (c, 0)]
  abel

lemma alternatingBlocksAssemble_decompose (B : AlternatingTwoForms R (M × N)) :
    alternatingBlocksAssemble (B.compLinearMap (LinearMap.inl R M N))
      (alternatingMixedBlock B) (B.compLinearMap (LinearMap.inr R M N)) = B := by
  ext v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, alternatingBlocksAssemble_pair]
  simp only [alternating_comp_pair, LinearMap.inl_apply, LinearMap.inr_apply,
    alternatingMixedBlock_apply]
  exact (alternatingBilinear_product B (v 0).1 (v 1).1 (v 0).2 (v 1).2).symm

/-- Alternating forms on a direct sum decompose into two alternating blocks
and one unrestricted mixed bilinear block. -/
def alternatingProductEquiv : AlternatingTwoForms R (M × N) ≃ₗ[R]
    AlternatingTwoForms R M × ((M →ₗ[R] N →ₗ[R] R) × AlternatingTwoForms R N) where
  toFun B := (B.compLinearMap (LinearMap.inl R M N),
    alternatingMixedBlock B, B.compLinearMap (LinearMap.inr R M N))
  invFun t := alternatingBlocksAssemble t.1 t.2.1 t.2.2
  left_inv := alternatingBlocksAssemble_decompose
  right_inv t := by
    rcases t with ⟨A, Q, C⟩
    apply Prod.ext
    · ext v
      simp [alternatingBlocksAssemble, AlternatingMap.compLinearMap_apply, ← Pi.zero_def]
    · apply Prod.ext
      · ext x y
        change alternatingBlocksAssemble A Q C ![(x, 0), (0, y)] = Q x y
        rw [alternatingBlocksAssemble_pair]
        have hA : A ![x, 0] = 0 := A.map_coord_zero 1 rfl
        have hC : C ![0, y] = 0 := C.map_coord_zero 0 rfl
        simp [hA, hC]
      · ext v
        simp [alternatingBlocksAssemble, AlternatingMap.compLinearMap_apply, ← Pi.zero_def]
  map_add' A B := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · ext x y; rfl
      · rfl
  map_smul' c B := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · ext x y; rfl
      · rfl

end
end PfaffianDescent
