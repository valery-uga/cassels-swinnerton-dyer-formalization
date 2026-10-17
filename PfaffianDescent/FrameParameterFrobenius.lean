import PfaffianDescent.FrameParameterBasis
import PfaffianDescent.RingFrobenius
import PfaffianDescent.FiveByFiveGram

namespace PfaffianDescent.FrameCoordinateRing
open Polynomial Module
section
variable {K : Type*} [Field K] [CharZero K]

/-- The coefficient of the quadratic basis vector over the regular parameter. -/
noncomputable def parameterFunctional : Module.Dual K[X] (FrameCoordinateRing K) :=
  parameterBasis.coord 4

lemma parameterFunctional_generator (i : Fin 5) :
    parameterFunctional (parameterGenerators (K := K) i) = if i = 4 then 1 else 0 := by
  change parameterBasis.repr (parameterGenerators i) 4 = _
  rw [← parameterBasis_apply, Basis.repr_self_apply]

@[simp] lemma parameterFunctional_one : parameterFunctional (1 : FrameCoordinateRing K) = 0 := by
  simpa [parameterGenerators] using parameterFunctional_generator (K := K) 0

@[simp] lemma parameterFunctional_q : parameterFunctional (q (K := K)) = 1 := by
  simpa [parameterGenerators] using parameterFunctional_generator (K := K) 4

lemma parameterFunctional_x (i : Fin 3) :
    parameterFunctional (x (K := K) i.castSucc) = 0 := by
  fin_cases i
  · simpa [parameterGenerators] using parameterFunctional_generator (K := K) 1
  · simpa [parameterGenerators] using parameterFunctional_generator (K := K) 2
  · simpa [parameterGenerators] using parameterFunctional_generator (K := K) 3

lemma parameterFunctional_x_mul_x (i j : Fin 3) :
    parameterFunctional (x (K := K) i.castSucc * x j.castSucc) = if i = j then -3 else 1 := by
  by_cases h : i = j
  · subst j
    rw [if_pos rfl, ← pow_two, x_sq_parameter, ← parameter_X_smul]
    have hthree : (3 : K[X]) • q (K := K) = 3 * q := parameter_nat_smul 3 q
    rw [← hthree, map_sub, map_smul, map_smul, parameterFunctional_x, parameterFunctional_q]
    simp
  · rw [if_neg h, mixed _ _ (fun he => h (Fin.castSucc_injective _ he)), parameterFunctional_q]

lemma parameter_multiplicationGram : multiplicationGram (parameterBasis (K := K)) parameterFunctional =
    fiveByFiveGram (fun i : Fin 3 => parameterFunctional (x i.castSucc * q))
      (parameterFunctional (q^2)) := by
  have h0 : parameterFunctional (x (K := K) 0) = 0 := parameterFunctional_x 0
  have h1 : parameterFunctional (x (K := K) 1) = 0 := parameterFunctional_x 1
  have h2 : parameterFunctional (x (K := K) 2) = 0 := parameterFunctional_x 2
  have h00 : parameterFunctional (x (K := K) 0 * x 0) = -3 := by
    simpa only [show (0 : Fin 3).castSucc = (0 : Fin 4) from rfl,
      show (1 : Fin 3).castSucc = (1 : Fin 4) from rfl,
      show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl, show (0 : Fin 3) = 0 ↔ True from by decide, if_true, if_false] using
      parameterFunctional_x_mul_x (K := K) 0 0
  have h01 : parameterFunctional (x (K := K) 0 * x 1) = 1 := by
    simpa only [show (0 : Fin 3).castSucc = (0 : Fin 4) from rfl,
      show (1 : Fin 3).castSucc = (1 : Fin 4) from rfl,
      show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl, show (0 : Fin 3) = 1 ↔ False from by decide, if_true, if_false] using
      parameterFunctional_x_mul_x (K := K) 0 1
  have h02 : parameterFunctional (x (K := K) 0 * x 2) = 1 := by
    simpa only [show (0 : Fin 3).castSucc = (0 : Fin 4) from rfl,
      show (1 : Fin 3).castSucc = (1 : Fin 4) from rfl,
      show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl, show (0 : Fin 3) = 2 ↔ False from by decide, if_true, if_false] using
      parameterFunctional_x_mul_x (K := K) 0 2
  have h10 : parameterFunctional (x (K := K) 1 * x 0) = 1 := by
    simpa only [show (0 : Fin 3).castSucc = (0 : Fin 4) from rfl,
      show (1 : Fin 3).castSucc = (1 : Fin 4) from rfl,
      show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl, show (1 : Fin 3) = 0 ↔ False from by decide, if_true, if_false] using
      parameterFunctional_x_mul_x (K := K) 1 0
  have h11 : parameterFunctional (x (K := K) 1 * x 1) = -3 := by
    simpa only [show (0 : Fin 3).castSucc = (0 : Fin 4) from rfl,
      show (1 : Fin 3).castSucc = (1 : Fin 4) from rfl,
      show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl, show (1 : Fin 3) = 1 ↔ True from by decide, if_true, if_false] using
      parameterFunctional_x_mul_x (K := K) 1 1
  have h12 : parameterFunctional (x (K := K) 1 * x 2) = 1 := by
    simpa only [show (0 : Fin 3).castSucc = (0 : Fin 4) from rfl,
      show (1 : Fin 3).castSucc = (1 : Fin 4) from rfl,
      show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl, show (1 : Fin 3) = 2 ↔ False from by decide, if_true, if_false] using
      parameterFunctional_x_mul_x (K := K) 1 2
  have h20 : parameterFunctional (x (K := K) 2 * x 0) = 1 := by
    simpa only [show (0 : Fin 3).castSucc = (0 : Fin 4) from rfl,
      show (1 : Fin 3).castSucc = (1 : Fin 4) from rfl,
      show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl, show (2 : Fin 3) = 0 ↔ False from by decide, if_true, if_false] using
      parameterFunctional_x_mul_x (K := K) 2 0
  have h21 : parameterFunctional (x (K := K) 2 * x 1) = 1 := by
    simpa only [show (0 : Fin 3).castSucc = (0 : Fin 4) from rfl,
      show (1 : Fin 3).castSucc = (1 : Fin 4) from rfl,
      show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl, show (2 : Fin 3) = 1 ↔ False from by decide, if_true, if_false] using
      parameterFunctional_x_mul_x (K := K) 2 1
  have h22 : parameterFunctional (x (K := K) 2 * x 2) = -3 := by
    simpa only [show (0 : Fin 3).castSucc = (0 : Fin 4) from rfl,
      show (1 : Fin 3).castSucc = (1 : Fin 4) from rfl,
      show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl, show (2 : Fin 3) = 2 ↔ True from by decide, if_true, if_false] using
      parameterFunctional_x_mul_x (K := K) 2 2
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [multiplicationGram, parameterBasis_apply, parameterGenerators, fiveByFiveGram,
      h0, h1, h2, h00, h01, h02, h11, h12, h22, pow_two, mul_comm]

/-- The multiplication pairing is unimodular over the regular parameter ring. -/
theorem parameter_multiplicationGram_isUnit :
    IsUnit (multiplicationGram (parameterBasis (K := K)) parameterFunctional).det := by
  rw [parameter_multiplicationGram, fiveByFiveGram_det]
  have h : IsUnit (16 : K) := isUnit_iff_ne_zero.mpr (by norm_num)
  simpa only [map_ofNat] using h.map (C : K →+* K[X])

/-- The homogeneous coordinate ring is self-dual over the polynomial parameter,
via its actual multiplication pairing. -/
noncomputable def parameterFrobeniusEquiv :
    FrameCoordinateRing K ≃ₗ[K[X]] Module.Dual K[X] (FrameCoordinateRing K) :=
  ringFrobeniusEquiv parameterBasis parameterFunctional parameter_multiplicationGram_isUnit

end
end PfaffianDescent.FrameCoordinateRing
