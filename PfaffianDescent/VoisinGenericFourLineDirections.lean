import PfaffianDescent.VoisinGenericFourLineSeparability

/-!
# Nonzero cubic values in the four split directions

The diagonal specialization shows that the universal cubic does not vanish
at any of the four line directions. This property persists over the generic
coefficient field and any field extension thereof.
-/

namespace PfaffianDescent

open MvPolynomial VoisinExplicitSeparableFourLineExample

universe u

theorem diagonalCubicTensor_lineDirection_ne_zero
    (K : Type u) [Field K] [CharZero K] (i j : Fin 2) :
    (c₀ (K := K)).eval (lineDirection i j) ≠ 0 := by
  rw [c₀_eval]
  fin_cases i <;> fin_cases j <;>
    simp [lineDirection] <;> norm_num

theorem universalCubicTensor_lineDirection_ne_zero
    (K : Type u) [Field K] [CharZero K] (i j : Fin 2) :
    (universalCubicTensor K).eval (universalFourLineDirection K i j) ≠ 0 := by
  let φ := diagonalCubicTensorSpecialization K
  have h := Cubic.eval_map φ (universalCubicTensor K)
    (universalFourLineDirection K i j)
  rw [universalCubicTensor_map_diagonal] at h
  have hdirection : (fun k => φ (universalFourLineDirection K i j k)) =
      lineDirection i j := by
    funext k
    simp [φ, universalFourLineDirection, diagonalCubicTensorSpecialization]
  rw [hdirection] at h
  intro hz
  rw [hz, map_zero] at h
  exact diagonalCubicTensor_lineDirection_ne_zero K i j h

theorem genericCubicTensor_lineDirection_ne_zero_baseChange
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L)
    (i j : Fin 2) :
    ((genericCubicTensor K).map φ).eval (lineDirection i j) ≠ 0 := by
  let T := CubicTensorCoefficients K
  let F := FractionRing T
  let ι : T →+* F := algebraMap T F
  have hι : Function.Injective ι := FaithfulSMul.algebraMap_injective T F
  have hnonzero : (genericCubicTensor K).eval
      (genericFourLineDirection K i j) ≠ 0 := by
    have heval := Cubic.eval_map ι (universalCubicTensor K)
      (universalFourLineDirection K i j)
    change (genericCubicTensor K).eval (genericFourLineDirection K i j) =
      ι ((universalCubicTensor K).eval (universalFourLineDirection K i j)) at heval
    rw [heval]
    simpa using hι.ne (universalCubicTensor_lineDirection_ne_zero K i j)
  have heval := Cubic.eval_map φ (genericCubicTensor K)
    (genericFourLineDirection K i j)
  rw [genericFourLineDirection_baseChange_eq K φ i j] at heval
  rw [heval]
  exact (map_ne_zero φ).mpr hnonzero

/-- A root on a generic split line has nonzero first coordinate, so it
lies in the standard affine chart. -/
theorem genericCubicTensor_fourLine_root_parameter_ne_zero
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L)
    (i j : Fin 2) (t : L)
    (hroot : ((genericCubicTensor K).map φ).eval
      (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) = 0) :
    t ≠ 0 := by
  intro ht
  subst t
  simp only [zero_smul, zero_add] at hroot
  exact genericCubicTensor_lineDirection_ne_zero_baseChange K φ i j hroot

theorem fourLine_root_normalization
    {L : Type u} [Field L] (i j : Fin 2) (t : L) (ht : t ≠ 0) :
    t⁻¹ • (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) =
      (Pi.single 0 1 : Fin 4 → L) + t⁻¹ • lineDirection i j := by
  rw [smul_add, smul_smul, inv_mul_cancel₀ ht, one_smul]

theorem fourLine_root_parameters_injective
    {L : Type u} [Field L] (i j : Fin 2)
    (x : Fin 3 → Fin 4 → L) (t : Fin 3 → L)
    (hx : Function.Injective x)
    (hform : ∀ k, x k = t k • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) :
    Function.Injective t := by
  intro k l h
  apply hx
  rw [hform k, hform l, h]

theorem fourLine_normalized_root_parameters_injective
    {L : Type u} [Field L] (i j : Fin 2)
    (x : Fin 3 → Fin 4 → L) (t : Fin 3 → L)
    (hx : Function.Injective x)
    (hform : ∀ k, x k = t k • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) :
    Function.Injective (fun k => (t k)⁻¹) := by
  exact (inv_injective.comp (fourLine_root_parameters_injective i j x t hx hform))

end PfaffianDescent
