import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Exact.Basic

namespace PfaffianDescent
open scoped BigOperators
section
variable {K R n : Type*} [Field K] [CommRing R] [Algebra K R] [Fintype n]

noncomputable def coefficientVectorEquiv (E : R ≃ₐ[K] R) : (n → R) ≃ₗ[K] (n → R) :=
  LinearEquiv.piCongrRight (fun _ => E.toLinearEquiv)

lemma coefficientVectorEquiv_mulVec (E : R ≃ₐ[K] R) (T : Matrix n n R) (v : n → R) :
    coefficientVectorEquiv E (T.mulVec v) =
      (T.map E).mulVec (coefficientVectorEquiv E v) := by
  funext i
  exact RingHom.map_mulVec E.toRingHom T v i

lemma coefficientVectorEquiv_first (E : R ≃ₐ[K] R) (q : n → R) (r : R) :
    coefficientVectorEquiv E (r • q) = E r • (fun i => E (q i)) := by
  funext i
  exact map_mul E r (q i)

lemma coefficientVectorEquiv_last (E : R ≃ₐ[K] R) (q v : n → R) :
    E (Fintype.linearCombination R q v) =
      Fintype.linearCombination R (fun i => E (q i)) (coefficientVectorEquiv E v) := by
  change E (∑ i, v i * q i) = ∑ i, E (v i) * E (q i)
  simp only [map_sum, map_mul]

/-- Exactness at the first free module survives a polynomial coordinate automorphism. -/
theorem polynomial_complex_first_exact_equiv (E : R ≃ₐ[K] R) (q : n → R) (T : Matrix n n R)
    (h : LinearMap.range (LinearMap.toSpanSingleton R (n → R) q) = LinearMap.ker T.mulVecLin) :
    LinearMap.range (LinearMap.toSpanSingleton R (n → R) (fun i => E (q i))) =
      LinearMap.ker (T.map E).mulVecLin := by
  have hR : Function.Exact (LinearMap.toSpanSingleton R (n → R) q) T.mulVecLin :=
    LinearMap.exact_iff.mpr h.symm
  have hK : Function.Exact ((LinearMap.toSpanSingleton R (n → R) q).restrictScalars K)
      (T.mulVecLin.restrictScalars K) := hR
  have he := (LinearMap.exact_iff_of_surjective_of_bijective_of_injective
    ((LinearMap.toSpanSingleton R (n → R) q).restrictScalars K) (T.mulVecLin.restrictScalars K)
    ((LinearMap.toSpanSingleton R (n → R) (fun i => E (q i))).restrictScalars K)
    ((T.map E).mulVecLin.restrictScalars K) E.toLinearMap
    (coefficientVectorEquiv E).toLinearMap (coefficientVectorEquiv E).toLinearMap
    (by apply LinearMap.ext; intro r; exact (coefficientVectorEquiv_first E q r).symm)
    (by apply LinearMap.ext; intro v; exact (coefficientVectorEquiv_mulVec E T v).symm)
    E.surjective (coefficientVectorEquiv E).bijective (coefficientVectorEquiv E).injective).mp hK
  have heR : Function.Exact (LinearMap.toSpanSingleton R (n → R) (fun i => E (q i)))
      (T.map E).mulVecLin := he
  exact (LinearMap.exact_iff.mp heR).symm

/-- Exactness among the quadratic generators survives a polynomial coordinate automorphism. -/
theorem polynomial_complex_last_exact_equiv (E : R ≃ₐ[K] R) (q : n → R) (T : Matrix n n R)
    (h : LinearMap.range T.mulVecLin = LinearMap.ker (Fintype.linearCombination R q)) :
    LinearMap.range (T.map E).mulVecLin =
      LinearMap.ker (Fintype.linearCombination R (fun i => E (q i))) := by
  have hR : Function.Exact T.mulVecLin (Fintype.linearCombination R q) := LinearMap.exact_iff.mpr h.symm
  have hK : Function.Exact (T.mulVecLin.restrictScalars K)
      ((Fintype.linearCombination R q).restrictScalars K) := hR
  have he := (LinearMap.exact_iff_of_surjective_of_bijective_of_injective
    (T.mulVecLin.restrictScalars K) ((Fintype.linearCombination R q).restrictScalars K)
    ((T.map E).mulVecLin.restrictScalars K)
    ((Fintype.linearCombination R (fun i => E (q i))).restrictScalars K)
    (coefficientVectorEquiv E).toLinearMap (coefficientVectorEquiv E).toLinearMap E.toLinearMap
    (by apply LinearMap.ext; intro v; exact (coefficientVectorEquiv_mulVec E T v).symm)
    (by apply LinearMap.ext; intro v; exact (coefficientVectorEquiv_last E q v).symm)
    (coefficientVectorEquiv E).surjective (coefficientVectorEquiv E).bijective E.injective).mp hK
  have heR : Function.Exact (T.map E).mulVecLin
      (Fintype.linearCombination R (fun i => E (q i))) := he
  exact (LinearMap.exact_iff.mp heR).symm

end
end PfaffianDescent
