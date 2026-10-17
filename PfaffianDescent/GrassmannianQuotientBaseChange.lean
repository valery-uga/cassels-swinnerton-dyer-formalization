import PfaffianDescent.GrassmannianSubmoduleBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Grassmannian

namespace PfaffianDescent
open Module TensorProduct
section
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (m n : ℕ)

/-- Tensor extension of the ambient coordinate module is its usual coefficient extension. -/
noncomputable def graphTensorEquiv :
    S ⊗[R] ((Fin m → R) × (Fin n → R)) ≃ₗ[S] ((Fin m → S) × (Fin n → S)) :=
  (TensorProduct.prodRight R S S (Fin m → R) (Fin n → R)).trans
    ((TensorProduct.piScalarRight R S S (Fin m)).prodCongr (TensorProduct.piScalarRight R S S (Fin n)))

lemma graphTensorEquiv_tmul (s : S) (x : (Fin m → R) × (Fin n → R)) :
    graphTensorEquiv R S m n (s ⊗ₜ[R] x) = s • graphCoefficientMap (algebraMap R S) x := by
  apply Prod.ext <;> funext i <;>
    simp [graphTensorEquiv, graphCoefficientMap, Algebra.smul_def, Function.comp_def, mul_comm]

lemma graphTensorEquiv_one_tmul (x : (Fin m → R) × (Fin n → R)) :
    graphTensorEquiv R S m n (1 ⊗ₜ[R] x) = graphCoefficientMap (algebraMap R S) x := by
  rw [graphTensorEquiv_tmul, one_smul]

/-- The coordinate formula for submodule extension is the standard tensor-product base change. -/
lemma graphTensorEquiv_baseChange (W : Submodule R ((Fin m → R) × (Fin n → R))) :
    (W.baseChange S).map (graphTensorEquiv R S m n).toLinearMap =
      grassmannianSubmoduleBaseChange (algebraMap R S) W := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span]
  change Submodule.span S ((graphTensorEquiv R S m n) ''
      (TensorProduct.mk R S ((Fin m → R) × (Fin n → R)) 1 '' (W : Set ((Fin m → R) × (Fin n → R))))) = _
  rw [← Set.image_comp]
  have he : (graphTensorEquiv R S m n) ∘ TensorProduct.mk R S ((Fin m → R) × (Fin n → R)) 1 =
      graphCoefficientMap (algebraMap R S) := by
    funext x
    exact graphTensorEquiv_one_tmul R S m n x
  rw [he]
  rfl

variable (W : Submodule R ((Fin m → R) × (Fin n → R)))

noncomputable def grassmannianBaseChangeQuotientMap : ((Fin m → S) × (Fin n → S)) →ₗ[S]
    S ⊗[R] (((Fin m → R) × (Fin n → R)) ⧸ W) :=
  (W.mkQ.baseChange S).comp (graphTensorEquiv R S m n).symm.toLinearMap

lemma grassmannianBaseChangeQuotientMap_surjective :
    Function.Surjective (grassmannianBaseChangeQuotientMap R S m n W) :=
  (LinearMap.baseChange_surjective S (Submodule.mkQ_surjective W)).comp
    (graphTensorEquiv R S m n).symm.surjective

lemma grassmannianBaseChangeQuotientMap_ker :
    (grassmannianBaseChangeQuotientMap R S m n W).ker =
      grassmannianSubmoduleBaseChange (algebraMap R S) W := by
  have he : (W.mkQ.baseChange S).ker = W.baseChange S := by
    ext t
    change t ∈ (W.mkQ.lTensor S).ker ↔ t ∈ (W.subtype.lTensor S).range
    rw [lTensor_mkQ]
  rw [grassmannianBaseChangeQuotientMap, LinearMap.ker_comp, he,
    Submodule.comap_equiv_eq_map_symm]
  exact graphTensorEquiv_baseChange R S m n W

/-- The quotient after coordinate base change is the tensor product of the original quotient. -/
noncomputable def grassmannianBaseChangeQuotientEquiv :
    (((Fin m → S) × (Fin n → S)) ⧸ grassmannianSubmoduleBaseChange (algebraMap R S) W) ≃ₗ[S]
      S ⊗[R] (((Fin m → R) × (Fin n → R)) ⧸ W) :=
  (Submodule.quotEquivOfEq _ _ (grassmannianBaseChangeQuotientMap_ker R S m n W).symm).trans
    ((grassmannianBaseChangeQuotientMap R S m n W).quotKerEquivOfSurjective
      (grassmannianBaseChangeQuotientMap_surjective R S m n W))

end
section
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] {m n : ℕ}

/-- Scalar extension preserves the actual finite projective quotient and its constant rank. -/
noncomputable def grassmannianQuotientBaseChange
    (W : Module.Grassmannian R ((Fin m → R) × (Fin n → R)) n) :
    Module.Grassmannian S ((Fin m → S) × (Fin n → S)) n where
  toSubmodule := grassmannianSubmoduleBaseChange (algebraMap R S) W.toSubmodule
  finite_quotient := Module.Finite.equiv (grassmannianBaseChangeQuotientEquiv R S m n W.toSubmodule).symm
  projective_quotient := Module.Projective.of_equiv (grassmannianBaseChangeQuotientEquiv R S m n W.toSubmodule).symm
  rankAtStalk_eq p := by
    rw [Module.rankAtStalk_eq_of_equiv (grassmannianBaseChangeQuotientEquiv R S m n W.toSubmodule),
      Module.rankAtStalk_baseChange]
    exact W.rankAtStalk_eq _

end
end PfaffianDescent
