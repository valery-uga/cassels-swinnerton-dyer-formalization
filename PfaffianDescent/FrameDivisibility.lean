import PfaffianDescent.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Prime.Lemmas

namespace PfaffianDescent
open MvPolynomial

section
variable {K : Type*} [Field K]

noncomputable def frameShearMinus : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 4) K :=
  MvPolynomial.aeval ![X 0, X 1, X 2 - X 1, X 3]

noncomputable def frameShearPlus : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 4) K :=
  MvPolynomial.aeval ![X 0, X 1, X 2 + X 1, X 3]

lemma frameShear_minus_plus : (frameShearMinus (K := K)).comp frameShearPlus = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [frameShearMinus, frameShearPlus]

lemma frameShear_plus_minus : (frameShearPlus (K := K)).comp frameShearMinus = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [frameShearMinus, frameShearPlus]

noncomputable def frameShear : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K :=
  AlgEquiv.ofAlgHom frameShearMinus frameShearPlus frameShear_minus_plus frameShear_plus_minus

lemma frame_difference_prime : Prime (X 2 - X 1 : MvPolynomial (Fin 4) K) := by
  have h : Prime (frameShear (K := K) (X 2)) :=
    (MulEquiv.prime_iff frameShear).mpr (MvPolynomial.X_prime (i := (2 : Fin 4)))
  simpa [frameShear, frameShearMinus] using h

lemma frame_X_zero_not_dvd_X_two : ¬ (X 0 : MvPolynomial (Fin 4) K) ∣ X 2 := by
  intro h
  have he := map_dvd (MvPolynomial.eval₂Hom (RingHom.id K) ![0, 0, 1, 0]) h
  simpa using he

lemma frame_X_zero_not_dvd_X_three : ¬ (X 0 : MvPolynomial (Fin 4) K) ∣ X 3 := by
  intro h
  have he := map_dvd (MvPolynomial.eval₂Hom (RingHom.id K) ![0, 0, 0, 1]) h
  simpa using he

lemma frame_difference_not_dvd_other :
    ¬ (X 2 - X 1 : MvPolynomial (Fin 4) K) ∣ X 3 - X 1 := by
  intro h
  have he := map_dvd (MvPolynomial.eval₂Hom (RingHom.id K) ![0, 0, 0, 1]) h
  simpa using he

end
end PfaffianDescent
