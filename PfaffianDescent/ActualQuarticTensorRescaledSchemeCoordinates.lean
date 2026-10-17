import PfaffianDescent.ActualQuarticDualTensorCoordinates
import PfaffianDescent.FourTangentDualRescaleScheme

/-! The actual supplied algebra's tensor decomposition after tangent
rescaling, retaining both its componentwise ring evaluator and its Spec
isomorphism. No polynomial-kernel certificate stands in for the scheme map. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory Module
open scoped TensorProduct
universe u
variable {k L K A : Type u} [Field k] [Field L] [Field K] [CommRing A]
  [Algebra k L] [Algebra k K] [Algebra k A]
  [IsAlgClosed K] [FiniteDimensional k L] [Algebra.IsSeparable k L]

/-- The SAME embedding-indexed actual algebra decomposition, followed by
the actual nonzero epsilon rescaling in every component. -/
def actualQuarticDualTensorRescaledEquiv
    (eA : A ≃ₐ[k] DualNumber L) (b : Basis (Fin 4) k L)
    (full : Fin 4 ≃ (L →ₐ[k] K)) (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0) :
    (K ⊗[k] A) ≃ₐ[K] FourTangentDualAlgebra K :=
  (actualQuarticDualTensorEquiv eA b full).trans (fourTangentDualRescaleEquiv l hl)

/-- Literal values of original supplied-algebra elements, including their
nilpotent coordinates, in the actual rescaled component scheme. -/
@[simp] theorem actualQuarticDualTensorRescaledEquiv_tmul
    (eA : A ≃ₐ[k] DualNumber L) (b : Basis (Fin 4) k L)
    (full : Fin 4 ≃ (L →ₐ[k] K)) (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0)
    (c : K) (a : A) (i : Fin 4) :
    actualQuarticDualTensorRescaledEquiv eA b full l hl (c ⊗ₜ[k] a) i =
      (c * full i (eA a).fst, l i * (c * full i (eA a).snd)) := by
  simp only [actualQuarticDualTensorRescaledEquiv, AlgEquiv.trans_apply,
    fourTangentDualRescaleEquiv_apply, actualQuarticDualTensorEquiv_tmul]
  apply TrivSqZeroExt.ext
  · exact TrivSqZeroExt.fst_map (LinearMap.mulLeft K (l i)) _
  · exact TrivSqZeroExt.snd_map (LinearMap.mulLeft K (l i)) _

/-- The actual scalar-extended supplied algebra has this literal Spec
isomorphism, oriented from its tensor scheme to the rescaled four factors. -/
def actualQuarticDualTensorRescaledSpecIso
    (eA : A ≃ₐ[k] DualNumber L) (b : Basis (Fin 4) k L)
    (full : Fin 4 ≃ (L →ₐ[k] K)) (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0) :
    Spec (.of (K ⊗[k] A)) ≅ Spec (.of (FourTangentDualAlgebra K)) :=
  Scheme.Spec.mapIso
    (actualQuarticDualTensorRescaledEquiv eA b full l hl).toRingEquiv.toCommRingCatIso.symm.op

theorem actualQuarticDualTensorRescaledSpecIso_hom
    (eA : A ≃ₐ[k] DualNumber L) (b : Basis (Fin 4) k L)
    (full : Fin 4 ≃ (L →ₐ[k] K)) (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0) :
    (actualQuarticDualTensorRescaledSpecIso eA b full l hl).hom =
      Spec.map (CommRingCat.ofHom
        (actualQuarticDualTensorRescaledEquiv eA b full l hl).symm.toRingHom) := rfl

theorem actualQuarticDualTensorRescaledSpecIso_inv
    (eA : A ≃ₐ[k] DualNumber L) (b : Basis (Fin 4) k L)
    (full : Fin 4 ≃ (L →ₐ[k] K)) (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0) :
    (actualQuarticDualTensorRescaledSpecIso eA b full l hl).inv =
      Spec.map (CommRingCat.ofHom
        (actualQuarticDualTensorRescaledEquiv eA b full l hl).toRingHom) := rfl

end PfaffianDescent.QuarticNet
