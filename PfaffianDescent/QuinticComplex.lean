import PfaffianDescent.QuinticPolynomialKernel

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
section
variable {K : Type*} [Field K]

noncomputable def quinticFirstMap (a : Vec K 5) :
    MvPolynomial (Fin 4) K →ₗ[MvPolynomial (Fin 4) K] (Fin 5 → MvPolynomial (Fin 4) K) :=
  LinearMap.toSpanSingleton _ _ (quinticRelations a)

noncomputable def quinticMiddleMap (a : Vec K 5) :
    (Fin 5 → MvPolynomial (Fin 4) K) →ₗ[MvPolynomial (Fin 4) K]
      (Fin 5 → MvPolynomial (Fin 4) K) := (quinticPolynomialMatrix a).mulVecLin

noncomputable def quinticLastMap (a : Vec K 5) :
    (Fin 5 → MvPolynomial (Fin 4) K) →ₗ[MvPolynomial (Fin 4) K] MvPolynomial (Fin 4) K :=
  Fintype.linearCombination _ (quinticRelations a)

noncomputable def quinticIdeal (a : Vec K 5) : Ideal (MvPolynomial (Fin 4) K) :=
  Ideal.span (Set.range (quinticRelations a))

lemma quinticFirstMap_injective (a : Vec K 5) : Function.Injective (quinticFirstMap a) := by
  apply (injective_iff_map_eq_zero (quinticFirstMap a)).mpr
  intro r hr
  have h := congrFun hr 0
  change r * quinticRelations a 0 = 0 at h
  exact (mul_eq_zero.mp h).resolve_right ((quinticRelations_independent a).ne_zero 0)

/-- Exactness at the first rank-five module of the ground-field quintic complex. -/
theorem quinticFirstMap_range_eq_middle_ker (a : Vec K 5) :
    LinearMap.range (quinticFirstMap a) = LinearMap.ker (quinticMiddleMap a) := by
  ext v
  constructor
  · rintro ⟨r, rfl⟩
    change (quinticPolynomialMatrix a).mulVec (r • quinticRelations a) = 0
    rw [Matrix.mulVec_smul, quinticPolynomialMatrix_quadrics, smul_zero]
  · intro hv
    obtain ⟨r, hr⟩ := quinticPolynomialMatrix_kernel a v hv
    exact ⟨r, hr.symm⟩

lemma quinticPolynomialMatrix_transpose (a : Vec K 5) :
    (quinticPolynomialMatrix a).transpose = -quinticPolynomialMatrix a := by
  funext i j
  exact (quinticSyzygyMatrix_alternating (fun i => C (a i)) X).2 i j

lemma quinticLastMap_comp_middle (a : Vec K 5) :
    (quinticLastMap a).comp (quinticMiddleMap a) = 0 := by
  apply LinearMap.ext
  intro v
  change dotProduct ((quinticPolynomialMatrix a).mulVec v) (quinticRelations a) = 0
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    quinticPolynomialMatrix_transpose, Matrix.neg_mulVec, quinticPolynomialMatrix_quadrics,
    neg_zero, zero_dotProduct]

lemma quinticLastMap_range (a : Vec K 5) : LinearMap.range (quinticLastMap a) = quinticIdeal a := by
  rw [quinticLastMap, Fintype.range_linearCombination]
  rfl

/-- The quotient augmentation of the explicit quintic complex is surjective
and has the expected kernel. -/
theorem quintic_augmentation_exact (a : Vec K 5) :
    Function.Surjective (Ideal.Quotient.mkₐ K (quinticIdeal a)) ∧
      ∀ p : MvPolynomial (Fin 4) K,
        Ideal.Quotient.mkₐ K (quinticIdeal a) p = 0 ↔ p ∈ LinearMap.range (quinticLastMap a) := by
  refine ⟨Ideal.Quotient.mkₐ_surjective K (quinticIdeal a), ?_⟩
  intro p
  rw [quinticLastMap_range]
  exact Ideal.Quotient.eq_zero_iff_mem

end
end PfaffianDescent
