import PfaffianDescent.GoodFiberAlgebra
import Mathlib.RingTheory.Etale.Field
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PfaffianDescent.GoodFiberAlgebra
section
variable {K : Type*} [Field K] [NeZero (2 : K)]

lemma to_from : (toQuadratic (K := K)).comp fromQuadratic = AlgHom.id K _ := by
  apply AdjoinRoot.algHom_ext
  change toQuadratic (fromQuadratic (AdjoinRoot.root (goodFiberPolynomial K))) = _
  rw [fromQuadratic_root, toQuadratic_x]
  rfl

lemma from_to_x (i : Fin 3) : fromQuadratic (toQuadratic (x (K := K) i)) = x i := by
  have hh : fromQuadratic (half (K := K)) * 2 = (1 : GoodFiberAlgebra K) := by
    have h := congrArg (fromQuadratic (K := K)) (twice_half (K := K))
    simpa only [map_mul, map_ofNat, map_one, mul_comm] using h
  rw [toQuadratic_x]
  fin_cases i
  · exact fromQuadratic_root
  · change fromQuadratic (half (K := K) * AdjoinRoot.root (goodFiberPolynomial K)) = x 1
    rw [map_mul, fromQuadratic_root, first_eq_twice_second, ← mul_assoc, hh, one_mul]
  · change fromQuadratic (half (K := K) * AdjoinRoot.root (goodFiberPolynomial K)) = x 2
    rw [map_mul, fromQuadratic_root, first_eq_twice_third, ← mul_assoc, hh, one_mul]

lemma from_to : (fromQuadratic (K := K)).comp toQuadratic = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact from_to_x i

/-- The actual three-equation quotient, including its scheme structure, is the
quadratic algebra `K[t]/(t²+2)`. -/
noncomputable def quadraticEquiv : GoodFiberAlgebra K ≃ₐ[K] GoodFiberQuadratic K :=
  AlgEquiv.ofAlgHom toQuadratic fromQuadratic to_from from_to

instance : FiniteDimensional K (GoodFiberAlgebra K) :=
  quadraticEquiv.toLinearEquiv.symm.finiteDimensional

lemma finrank_eq_two : Module.finrank K (GoodFiberAlgebra K) = 2 := by
  rw [quadraticEquiv.toLinearEquiv.finrank_eq]
  exact goodFiberQuadratic_finrank K

instance : Algebra.Etale K (GoodFiberAlgebra K) :=
  Algebra.Etale.of_equiv quadraticEquiv.symm

instance : IsReduced (GoodFiberAlgebra K) :=
  Algebra.FormallyUnramified.isReduced_of_field K (GoodFiberAlgebra K)

end
end PfaffianDescent.GoodFiberAlgebra
