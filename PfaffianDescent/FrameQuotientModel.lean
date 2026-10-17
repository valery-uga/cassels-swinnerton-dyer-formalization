import PfaffianDescent.FrameQuotientSpan
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PfaffianDescent
open Module

section
variable {K : Type*} [Field K] [CharZero K]

/-- The four variable classes in the explicitly constructed Artinian algebra. -/
noncomputable def frameArtinVariables : Fin 4 → FrameArtin K :=
  ![⟨![0, 1, 0, 0, 0]⟩, ⟨![0, 0, 1, 0, 0]⟩,
    ⟨![0, 0, 0, 1, 0]⟩, ⟨![0, -1, -1, -1, 0]⟩]

private theorem frameArtinRelations_vanish (i : Fin 6) :
    MvPolynomial.aeval (frameArtinVariables (K := K)) (frameArtinRelations (K := K) i) = 0 := by
  fin_cases i
  · change MvPolynomial.aeval (frameArtinVariables (K := K)) (MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 0 * MvPolynomial.X 1) = 0
    simp only [map_sub, map_mul, map_add, MvPolynomial.aeval_X]
    apply FrameArtin.ext
    funext j
    fin_cases j
    · change ((0*0)-(0*0) : K) = 0
      norm_num
    · change ((0*0+1*0)-(0*0+1*0) : K) = 0
      norm_num
    · change ((0*0+0*0)-(0*1+0*0) : K) = 0
      norm_num
    · change ((0*1+0*0)-(0*0+0*0) : K) = 0
      norm_num
    · change ((0*0+0*0+(-3)*1*0+1*0+1*1+0*0+(-3)*0*0+0*1+0*0+0*0+(-3)*0*1)-(0*0+0*0+(-3)*1*0+1*1+1*0+0*0+(-3)*0*1+0*0+0*0+0*1+(-3)*0*0) : K) = 0
      norm_num
  · change MvPolynomial.aeval (frameArtinVariables (K := K)) (MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 0 * MvPolynomial.X 1) = 0
    simp only [map_sub, map_mul, map_add, MvPolynomial.aeval_X]
    apply FrameArtin.ext
    funext j
    fin_cases j
    · change ((0*0)-(0*0) : K) = 0
      norm_num
    · change ((0*(-1)+1*0)-(0*0+1*0) : K) = 0
      norm_num
    · change ((0*(-1)+0*0)-(0*1+0*0) : K) = 0
      norm_num
    · change ((0*(-1)+0*0)-(0*0+0*0) : K) = 0
      norm_num
    · change ((0*0+0*0+(-3)*1*(-1)+1*(-1)+1*(-1)+0*(-1)+(-3)*0*(-1)+0*(-1)+0*(-1)+0*(-1)+(-3)*0*(-1))-(0*0+0*0+(-3)*1*0+1*1+1*0+0*0+(-3)*0*1+0*0+0*0+0*1+(-3)*0*0) : K) = 0
      norm_num
  · change MvPolynomial.aeval (frameArtinVariables (K := K)) (MvPolynomial.X 1 * MvPolynomial.X 2 - MvPolynomial.X 0 * MvPolynomial.X 1) = 0
    simp only [map_sub, map_mul, map_add, MvPolynomial.aeval_X]
    apply FrameArtin.ext
    funext j
    fin_cases j
    · change ((0*0)-(0*0) : K) = 0
      norm_num
    · change ((0*0+0*0)-(0*0+1*0) : K) = 0
      norm_num
    · change ((0*0+1*0)-(0*1+0*0) : K) = 0
      norm_num
    · change ((0*1+0*0)-(0*0+0*0) : K) = 0
      norm_num
    · change ((0*0+0*0+(-3)*0*0+0*0+0*1+1*0+(-3)*1*0+1*1+0*0+0*0+(-3)*0*1)-(0*0+0*0+(-3)*1*0+1*1+1*0+0*0+(-3)*0*1+0*0+0*0+0*1+(-3)*0*0) : K) = 0
      norm_num
  · change MvPolynomial.aeval (frameArtinVariables (K := K)) (MvPolynomial.X 1 * MvPolynomial.X 3 - MvPolynomial.X 0 * MvPolynomial.X 1) = 0
    simp only [map_sub, map_mul, map_add, MvPolynomial.aeval_X]
    apply FrameArtin.ext
    funext j
    fin_cases j
    · change ((0*0)-(0*0) : K) = 0
      norm_num
    · change ((0*(-1)+0*0)-(0*0+1*0) : K) = 0
      norm_num
    · change ((0*(-1)+1*0)-(0*1+0*0) : K) = 0
      norm_num
    · change ((0*(-1)+0*0)-(0*0+0*0) : K) = 0
      norm_num
    · change ((0*0+0*0+(-3)*0*(-1)+0*(-1)+0*(-1)+1*(-1)+(-3)*1*(-1)+1*(-1)+0*(-1)+0*(-1)+(-3)*0*(-1))-(0*0+0*0+(-3)*1*0+1*1+1*0+0*0+(-3)*0*1+0*0+0*0+0*1+(-3)*0*0) : K) = 0
      norm_num
  · change MvPolynomial.aeval (frameArtinVariables (K := K)) (MvPolynomial.X 2 * MvPolynomial.X 3 - MvPolynomial.X 0 * MvPolynomial.X 1) = 0
    simp only [map_sub, map_mul, map_add, MvPolynomial.aeval_X]
    apply FrameArtin.ext
    funext j
    fin_cases j
    · change ((0*0)-(0*0) : K) = 0
      norm_num
    · change ((0*(-1)+0*0)-(0*0+1*0) : K) = 0
      norm_num
    · change ((0*(-1)+0*0)-(0*1+0*0) : K) = 0
      norm_num
    · change ((0*(-1)+1*0)-(0*0+0*0) : K) = 0
      norm_num
    · change ((0*0+0*0+(-3)*0*(-1)+0*(-1)+0*(-1)+0*(-1)+(-3)*0*(-1)+0*(-1)+1*(-1)+1*(-1)+(-3)*1*(-1))-(0*0+0*0+(-3)*1*0+1*1+1*0+0*0+(-3)*0*1+0*0+0*0+0*1+(-3)*0*0) : K) = 0
      norm_num
  · change MvPolynomial.aeval (frameArtinVariables (K := K)) (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.X 3) = 0
    simp only [map_sub, map_mul, map_add, MvPolynomial.aeval_X]
    apply FrameArtin.ext
    funext j
    fin_cases j
    · change (0+0+0+0 : K) = 0
      norm_num
    · change (1+0+0+(-1) : K) = 0
      norm_num
    · change (0+1+0+(-1) : K) = 0
      norm_num
    · change (0+0+1+(-1) : K) = 0
      norm_num
    · change (0+0+0+0 : K) = 0
      norm_num

namespace FrameQuotient

/-- Evaluation descends through the actual ideal of the Artinian reduction. -/
noncomputable def toFrameArtin : FrameQuotient K →ₐ[K] FrameArtin K :=
  Ideal.Quotient.liftₐ frameArtinIdeal (MvPolynomial.aeval frameArtinVariables) (by
    have hle : frameArtinIdeal (K := K) ≤
        RingHom.ker (MvPolynomial.aeval (frameArtinVariables (K := K))).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact frameArtinRelations_vanish i
    intro a ha
    exact hle ha)

theorem toFrameArtin_x (i : Fin 4) :
    toFrameArtin (x (K := K) i) = frameArtinVariables i := by
  change MvPolynomial.aeval (frameArtinVariables (K := K)) (MvPolynomial.X i) = _
  exact MvPolynomial.aeval_X _ _

noncomputable def modelBasis : Basis (Fin 5) K (FrameArtin K) :=
  (Pi.basisFun K (Fin 5)).map FrameArtin.coeffLinearEquiv.symm

theorem modelBasis_coeff (i j : Fin 5) : (modelBasis (K := K) i).coeff j =
    if i = j then 1 else 0 := by
  simp only [modelBasis, Basis.map_apply, Pi.basisFun_apply]
  change (Pi.single i (1 : K) : Fin 5 → K) j = if i = j then 1 else 0
  simp only [Pi.single_apply, eq_comm]

/-- The five quotient normal forms map to a basis of the model algebra. -/
theorem toFrameArtin_generators (i : Fin 5) :
    toFrameArtin (generators (K := K) i) = modelBasis i := by
  apply FrameArtin.ext
  funext j
  rw [modelBasis_coeff]
  fin_cases i
  · change (toFrameArtin (1 : FrameQuotient K)).coeff j = if (0 : Fin 5) = j then 1 else 0
    rw [map_one]
    fin_cases j <;> rfl
  · change (toFrameArtin (x (K := K) 0)).coeff j = if (1 : Fin 5) = j then 1 else 0
    rw [toFrameArtin_x]
    fin_cases j <;> rfl
  · change (toFrameArtin (x (K := K) 1)).coeff j = if (2 : Fin 5) = j then 1 else 0
    rw [toFrameArtin_x]
    fin_cases j <;> rfl
  · change (toFrameArtin (x (K := K) 2)).coeff j = if (3 : Fin 5) = j then 1 else 0
    rw [toFrameArtin_x]
    fin_cases j <;> rfl
  · change (toFrameArtin (x (K := K) 0 * x 1)).coeff j = if (4 : Fin 5) = j then 1 else 0
    rw [map_mul, toFrameArtin_x, toFrameArtin_x]
    fin_cases j
    · change ((0*0) : K) = 0
      norm_num
    · change ((0*0+1*0) : K) = 0
      norm_num
    · change ((0*1+0*0) : K) = 0
      norm_num
    · change ((0*0+0*0) : K) = 0
      norm_num
    · change ((0*0+0*0+(-3)*1*0+1*1+1*0+0*0+(-3)*0*1+0*0+0*0+0*1+(-3)*0*0) : K) = 1
      norm_num

theorem generators_independent : LinearIndependent K (generators (K := K)) := by
  apply LinearIndependent.of_comp toFrameArtin.toLinearMap
  have h : toFrameArtin.toLinearMap ∘ (generators (K := K)) = modelBasis :=
    funext toFrameArtin_generators
  rw [h]
  exact modelBasis.linearIndependent

noncomputable def basis : Basis (Fin 5) K (FrameQuotient K) :=
  Basis.mk generators_independent (by rw [← normalSpan_eq_top]; exact le_rfl)

theorem finrank_eq_five : finrank K (FrameQuotient K) = 5 := by
  simpa using Module.finrank_eq_card_basis (basis (K := K))

theorem toFrameArtin_surjective : Function.Surjective (toFrameArtin (K := K)) := by
  apply (LinearMap.range_eq_top (f := toFrameArtin.toLinearMap)).mp
  apply top_unique
  rw [← modelBasis.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨generators i, toFrameArtin_generators i⟩

/-- The Artinian reduction of the five-point relations is exactly the model algebra. -/
noncomputable def algebraEquiv : FrameQuotient K ≃ₐ[K] FrameArtin K :=
  AlgEquiv.ofBijective toFrameArtin ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      ((finrank_eq_five (K := K)).trans FrameArtin.finrank_eq_five.symm)
      (f := toFrameArtin.toLinearMap)).mpr toFrameArtin_surjective,
    toFrameArtin_surjective⟩

end FrameQuotient
end
end PfaffianDescent
