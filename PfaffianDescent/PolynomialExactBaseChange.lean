import PfaffianDescent.PolynomialVectorBaseChange

namespace PfaffianDescent
open MvPolynomial
open scoped TensorProduct
section
variable {K L σ m n o : Type*} [Field K] [Field L] [Algebra K L]
variable [Fintype m] [Fintype n] [Fintype o]

/-- Exact polynomial matrix complexes remain exact after a field extension. -/
theorem polynomial_matrix_exactness_ascends
    (A : Matrix m n (MvPolynomial σ K)) (B : Matrix o m (MvPolynomial σ K))
    (h : LinearMap.range A.mulVecLin = LinearMap.ker B.mulVecLin) :
    LinearMap.range (A.map (MvPolynomial.map (algebraMap K L))).mulVecLin =
      LinearMap.ker (B.map (MvPolynomial.map (algebraMap K L))).mulVecLin := by
  have hp : Function.Exact A.mulVecLin B.mulVecLin := LinearMap.exact_iff.mpr h.symm
  have hK : Function.Exact (A.mulVecLin.restrictScalars K) (B.mulVecLin.restrictScalars K) := hp
  have ht : Function.Exact ((A.mulVecLin.restrictScalars K).baseChange L)
      ((B.mulVecLin.restrictScalars K).baseChange L) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using Module.Flat.lTensor_exact L hK
  apply Eq.symm
  apply LinearMap.exact_iff.mp
  intro v
  constructor
  · intro hv
    let w := (polynomialVectorBaseChange K L σ m).symm v
    have hw : (B.mulVecLin.restrictScalars K).baseChange L w = 0 := by
      apply (polynomialVectorBaseChange K L σ o).injective
      rw [map_zero, polynomialVectorBaseChange_matrix]
      simpa only [w, LinearEquiv.apply_symm_apply, Matrix.mulVecLin_apply] using hv
    obtain ⟨y, hy⟩ := (ht w).mp hw
    refine ⟨polynomialVectorBaseChange K L σ n y, ?_⟩
    change (A.map (MvPolynomial.map (algebraMap K L))).mulVec _ = v
    rw [← polynomialVectorBaseChange_matrix, hy]
    exact (polynomialVectorBaseChange K L σ m).apply_symm_apply v
  · rintro ⟨y, rfl⟩
    let z := (polynomialVectorBaseChange K L σ n).symm y
    have hz := (ht ((A.mulVecLin.restrictScalars K).baseChange L z)).mpr ⟨z, rfl⟩
    have he := congrArg (polynomialVectorBaseChange K L σ o) hz
    rw [map_zero, polynomialVectorBaseChange_matrix,
      polynomialVectorBaseChange_matrix] at he
    simpa only [z, LinearEquiv.apply_symm_apply, Matrix.mulVecLin_apply] using he

/-- Exactness of a finite polynomial matrix complex is invariant under extending its field. -/
theorem polynomial_matrix_exactness_iff
    (A : Matrix m n (MvPolynomial σ K)) (B : Matrix o m (MvPolynomial σ K)) :
    (LinearMap.range (A.map (MvPolynomial.map (algebraMap K L))).mulVecLin =
      LinearMap.ker (B.map (MvPolynomial.map (algebraMap K L))).mulVecLin) ↔
    LinearMap.range A.mulVecLin = LinearMap.ker B.mulVecLin :=
  ⟨polynomial_matrix_exactness_descends A B, polynomial_matrix_exactness_ascends A B⟩

/-- Injectivity of a polynomial matrix is preserved by extension of its coefficient field. -/
theorem polynomial_matrix_injectivity_ascends
    (A : Matrix m n (MvPolynomial σ K)) (h : Function.Injective A.mulVecLin) :
    Function.Injective (A.map (MvPolynomial.map (algebraMap K L))).mulVecLin := by
  have ht : Function.Injective ((A.mulVecLin.restrictScalars K).baseChange L) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      Module.Flat.lTensor_preserves_injective_linearMap (M := L)
        (A.mulVecLin.restrictScalars K) h
  intro v w hvw
  apply (polynomialVectorBaseChange K L σ n).symm.injective
  apply ht
  apply (polynomialVectorBaseChange K L σ m).injective
  rw [polynomialVectorBaseChange_matrix, polynomialVectorBaseChange_matrix,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact hvw

end
end PfaffianDescent
