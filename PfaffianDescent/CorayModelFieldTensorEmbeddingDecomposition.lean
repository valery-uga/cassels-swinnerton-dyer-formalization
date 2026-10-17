import PfaffianDescent.CorayStabilizerHomogeneousIdealDescent
import Mathlib.RingTheory.TotallySplit
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Source only: canonical tensor/spectrum splitting indexed by ACTUAL
original-K embeddings of the actual component-model field. No supplied
splitting, arbitrary factor enumeration or point-transitivity premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K M Ω : Type u} [Field K] [Field M] [Field Ω]
  [Algebra K M] [Algebra K Ω] [Module.Finite K M] [Algebra.IsSeparable K M]
  [IsAlgClosed Ω]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ACTUAL embedding evaluation: each factor uses its own original-K
embedding M→Ω, on the literal tensor product Ω tensor_K M. -/
def fieldTensorEmbeddingEvaluation :
    Ω ⊗[K] M →ₐ[Ω] ((M →ₐ[K] Ω) → Ω) :=
  AlgHom.pi fun phi => (Algebra.TensorProduct.liftEquivRight K Ω M Ω) phi

/-- The actual embedding evaluation is bijective. Native finite separable
field base change is formally etale, and the native separably closed-field
splitting is reindexed by its ACTUAL evaluation kernels. No splitting or
desired decomposition witness is a hypothesis. -/
theorem finiteSeparableField_tensorEmbeddingEvaluation_bijective :
    Function.Bijective (fieldTensorEmbeddingEvaluation (K := K) (M := M) (Ω := Ω)) := by
  let B := Ω ⊗[K] M
  letI : Algebra.FormallyEtale K M := Algebra.FormallyEtale.of_isSeparable K M
  letI : Algebra.FormallyEtale Ω B := inferInstance
  letI : Module.Finite Ω B := inferInstance
  letI : Algebra.IsFiniteSplit Ω B := inferInstance
  let E := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω B
  let h : (M →ₐ[K] Ω) ≃ PrimeSpectrum B :=
    (Algebra.TensorProduct.liftEquivRight K Ω M Ω).trans
      (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum Ω B)
  let E' : B ≃ₐ[Ω] ((M →ₐ[K] Ω) → Ω) :=
    E.trans (AlgEquiv.piCongrLeft' Ω (fun _ : PrimeSpectrum B => Ω) h.symm)
  have heval (t : B) (phi : M →ₐ[K] Ω) : E' t phi = fieldTensorEmbeddingEvaluation t phi := by
    let p0 : PrimeSpectrum Ω := ⟨⊥, Ideal.isPrime_bot⟩
    let fphi : B →ₐ[Ω] Ω := (Algebra.TensorProduct.liftEquivRight K Ω M Ω) phi
    have hpoint : p0.comap fphi = h phi := by
      apply PrimeSpectrum.ext
      change Ideal.comap fphi.toRingHom ⊥ = RingHom.ker fphi.toRingHom
      exact (RingHom.ker_eq_comap_bot fphi.toRingHom).symm
    have hf := Algebra.FormallyEtale.equivPiOfIsSepClosed_comap fphi t p0
    rw [hpoint, Algebra.FormallyEtale.equivPiOfIsSepClosed_self_apply] at hf
    change E t (h phi) = fphi t
    exact hf
  have hfun : (fun t => E' t) = fieldTensorEmbeddingEvaluation (K := K) (M := M) (Ω := Ω) := by
    funext t phi
    exact heval t phi
  rw [← hfun]
  exact E'.bijective

/-- The canonical actual embedding-indexed tensor algebra equivalence. -/
def fieldTensorEmbeddingEquiv : Ω ⊗[K] M ≃ₐ[Ω] ((M →ₐ[K] Ω) → Ω) :=
  AlgEquiv.ofBijective fieldTensorEmbeddingEvaluation
    finiteSeparableField_tensorEmbeddingEvaluation_bijective

/-- Each actual factor sends the literal pure tensor to a*phi(m). This
fixes both coefficient maps of the native spectrum decomposition. -/
theorem fieldTensorEmbeddingEquiv_tmul (a : Ω) (m : M) (phi : M →ₐ[K] Ω) :
    fieldTensorEmbeddingEquiv (K := K) (M := M) (Ω := Ω) (a ⊗ₜ[K] m) phi = a * phi m := by
  change (Algebra.TensorProduct.liftEquivRight K Ω M Ω phi) (a ⊗ₜ[K] m) = _
  simp [Algebra.TensorProduct.liftEquivRight]

/-- Literal native spectrum coproduct morphism, indexed by actual original-K
embeddings; each summand is its own tensor evaluation map. -/
def fieldTensorEmbeddingSpectrumCoproductMap :
    (∐ fun _ : M →ₐ[K] Ω => Spec (.of Ω)) ⟶ Spec (.of (Ω ⊗[K] M)) :=
  Sigma.desc fun phi => Spec.map (CommRingCat.ofHom
    ((Algebra.TensorProduct.liftEquivRight K Ω M Ω) phi).toRingHom)

/-- The ACTUAL embedding-indexed spectrum coproduct morphism is an
isomorphism, constructed from native sigmaSpec and the actual tensor
evaluation equivalence. No spectrum decomposition witness is assumed. -/
theorem fieldTensorEmbeddingSpectrumCoproductMap_isIso :
    IsIso (fieldTensorEmbeddingSpectrumCoproductMap (K := K) (M := M) (Ω := Ω)) := by
  let e := fieldTensorEmbeddingEquiv (K := K) (M := M) (Ω := Ω)
  have hmap : fieldTensorEmbeddingSpectrumCoproductMap (K := K) (M := M) (Ω := Ω) =
      sigmaSpec (fun _ : M →ₐ[K] Ω => CommRingCat.of Ω) ≫
        Spec.map (CommRingCat.ofHom e.toRingHom) := by
    apply Sigma.hom_ext
    intro phi
    rw [fieldTensorEmbeddingSpectrumCoproductMap, Sigma.ι_desc, ← Category.assoc,
      ι_sigmaSpec, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.liftEquivRight K Ω M Ω) phi).toRingHom) = _
    congr 1
  letI : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
    change IsIso (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).hom
    infer_instance
  rw [hmap]
  infer_instance

/-- Each actual coproduct summand has its original model-field projection
given by EXACT phi and its Ω-structural projection the identity. Both native
spectrum maps are pinned; no scalar-square certificate is supplied. -/
theorem fieldTensorEmbeddingSpectrumCoproductMap_coefficient_components
    (phi : M →ₐ[K] Ω) :
    let i := Sigma.ι (fun _ : M →ₐ[K] Ω => Spec (.of Ω)) phi ≫
      fieldTensorEmbeddingSpectrumCoproductMap (K := K) (M := M) (Ω := Ω)
    i ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := K) (A := Ω) (B := M)).toRingHom) =
      Spec.map (CommRingCat.ofHom phi.toRingHom) ∧
      i ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[K] M))) = 𝟙 _ := by
  dsimp only
  rw [fieldTensorEmbeddingSpectrumCoproductMap, Sigma.ι_desc]
  constructor
  · rw [← Spec.map_comp]
    congr 1
    ext m
    change (Algebra.TensorProduct.liftEquivRight K Ω M Ω phi) (1 ⊗ₜ[K] m) = phi m
    simp [Algebra.TensorProduct.liftEquivRight]
  · rw [← Spec.map_comp]
    have hcomp : CommRingCat.ofHom (algebraMap Ω (Ω ⊗[K] M)) ≫
        CommRingCat.ofHom ((Algebra.TensorProduct.liftEquivRight K Ω M Ω) phi).toRingHom =
        𝟙 (CommRingCat.of Ω) := by
      ext a
      exact ((Algebra.TensorProduct.liftEquivRight K Ω M Ω) phi).commutes a
    rw [hcomp, Spec.map_id]

/-- For the ACTUAL whole-ideal stabilizer model field, the native tensor
spectrum is the coproduct of its ACTUAL embeddings into the SAME algebraic
closure target. Finiteness and separability come from the original finite
Galois definition field, not from any supplied tensor splitting. -/
theorem homogeneousIdealStabilizerFixedField_tensorEmbeddingSpectrumCoproductMap_isIso
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L)) :
    let M := homogeneousIdealStabilizerFixedField (K := K) C
    IsIso (fieldTensorEmbeddingSpectrumCoproductMap (K := K) (M := M) (Ω := Ω)) := by
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  letI : Module.Finite K M := inferInstance
  letI : Algebra.IsSeparable K M := inferInstance
  exact fieldTensorEmbeddingSpectrumCoproductMap_isIso

end PfaffianDescent.Coray
