import PfaffianDescent.GrassmannianQuotientBaseChange
import PfaffianDescent.GrassmannianQuotientCoordinates

namespace PfaffianDescent
open Module TensorProduct
section
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] {m n : ℕ}
  (W : Submodule R ((Fin m → R) × (Fin n → R)))

lemma grassmannianBaseChangeQuotientEquiv_mk (x : (Fin m → S) × (Fin n → S)) :
    grassmannianBaseChangeQuotientEquiv R S m n W
      ((grassmannianSubmoduleBaseChange (algebraMap R S) W).mkQ x) =
        grassmannianBaseChangeQuotientMap R S m n W x := rfl

lemma grassmannianBaseChangeQuotientMap_coeff (x : (Fin m → R) × (Fin n → R)) :
    grassmannianBaseChangeQuotientMap R S m n W (graphCoefficientMap (algebraMap R S) x) =
      1 ⊗ₜ[R] W.mkQ x := by
  change (W.mkQ.baseChange S) ((graphTensorEquiv R S m n).symm (graphCoefficientMap (algebraMap R S) x)) = _
  rw [← graphTensorEquiv_one_tmul, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]

lemma grassmannianQuotientCoordinateMap_coeff (σ : Equiv.Perm (Fin m ⊕ Fin n)) (v : Fin n → R) :
    grassmannianBaseChangeQuotientEquiv R S m n W
      (grassmannianQuotientCoordinateMap S (grassmannianSubmoduleBaseChange (algebraMap R S) W) σ
        (algebraMap R S ∘ v)) = 1 ⊗ₜ[R] grassmannianQuotientCoordinateMap R W σ v := by
  change grassmannianBaseChangeQuotientEquiv R S m n W
    ((grassmannianSubmoduleBaseChange (algebraMap R S) W).mkQ
      ((graphCoordinatePermutation S σ).symm (0, algebraMap R S ∘ v))) = _
  rw [grassmannianBaseChangeQuotientEquiv_mk]
  have he : (graphCoordinatePermutation S σ).symm (0, algebraMap R S ∘ v) =
      graphCoefficientMap (algebraMap R S) ((graphCoordinatePermutation R σ).symm (0, v)) := by
    rw [graphCoordinatePermutation_symm, graphCoordinatePermutation_symm]
    have hz : algebraMap R S ∘ (0 : Fin m → R) = 0 := by
      funext i
      exact map_zero _
    exact (congrArg (graphCoordinatePermutation S σ.symm) (congrArg (fun z => (z, algebraMap R S ∘ v)) hz.symm)).trans
      (graphCoordinatePermutation_map (algebraMap R S) σ.symm (0, v))
  rw [he, grassmannianBaseChangeQuotientMap_coeff]
  rfl

/-- Quotient coordinate maps commute with tensor-product extension of scalars. -/
lemma grassmannianQuotientCoordinateMap_baseChange (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (grassmannianBaseChangeQuotientEquiv R S m n W).toLinearMap.comp
      ((grassmannianQuotientCoordinateMap S (grassmannianSubmoduleBaseChange (algebraMap R S) W) σ).comp
        (TensorProduct.piScalarRight R S S (Fin n)).toLinearMap) =
      (grassmannianQuotientCoordinateMap R W σ).baseChange S := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s v
  rw [show s ⊗ₜ[R] v = s • ((1 : S) ⊗ₜ[R] v) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
  simp only [map_smul]
  congr 1
  change grassmannianBaseChangeQuotientEquiv R S m n W
    (grassmannianQuotientCoordinateMap S (grassmannianSubmoduleBaseChange (algebraMap R S) W) σ
      (TensorProduct.piScalarRight R S S (Fin n) (1 ⊗ₜ[R] v))) = _
  have he : TensorProduct.piScalarRight R S S (Fin n) (1 ⊗ₜ[R] v) = algebraMap R S ∘ v := by
    funext i
    simp [Algebra.smul_def, Function.comp_def]
  rw [he, grassmannianQuotientCoordinateMap_coeff, LinearMap.baseChange_tmul]

/-- Invertibility of a chart's quotient coordinates is unchanged by the canonical tensor coordinate identifications. -/
lemma grassmannianQuotientCoordinateMap_baseChange_bijective (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (h : Function.Bijective (grassmannianQuotientCoordinateMap S
      (grassmannianSubmoduleBaseChange (algebraMap R S) W) σ)) :
    Function.Bijective ((grassmannianQuotientCoordinateMap R W σ).baseChange S) := by
  rw [← grassmannianQuotientCoordinateMap_baseChange]
  exact (grassmannianBaseChangeQuotientEquiv R S m n W).bijective.comp
    (h.comp (TensorProduct.piScalarRight R S S (Fin n)).bijective)


lemma grassmannianQuotientCoordinateMap_baseChange_bijective_iff (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Function.Bijective ((grassmannianQuotientCoordinateMap R W σ).baseChange S) ↔
      Function.Bijective (grassmannianQuotientCoordinateMap S
        (grassmannianSubmoduleBaseChange (algebraMap R S) W) σ) := by
  rw [← grassmannianQuotientCoordinateMap_baseChange]
  change Function.Bijective ((grassmannianBaseChangeQuotientEquiv R S m n W) ∘
    ((grassmannianQuotientCoordinateMap S (grassmannianSubmoduleBaseChange (algebraMap R S) W) σ) ∘
      (TensorProduct.piScalarRight R S S (Fin n)))) ↔ _
  exact (Function.Bijective.of_comp_iff'
    (grassmannianBaseChangeQuotientEquiv R S m n W).bijective _).trans
      (Function.Bijective.of_comp_iff _ (TensorProduct.piScalarRight R S S (Fin n)).bijective)

end
end PfaffianDescent
