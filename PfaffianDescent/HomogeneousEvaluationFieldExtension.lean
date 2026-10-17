import PfaffianDescent.HomogeneousVanishingLinearSystem
import PfaffianDescent.HomogeneousIdealPieceCoefficientBaseChange
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Finite

/-! Flat scalar extension of the ACTUAL homogeneous evaluation kernel.
The target is an arbitrary finite algebra, including nonreduced algebras.
All extension-field coefficients occur in the conclusion. -/

noncomputable section
namespace PfaffianDescent
open MvPolynomial Module TensorProduct
open scoped TensorProduct
universe u
variable {k K A : Type u} [Field k] [Field K] [CommRing A]
  [Algebra k K] [Algebra k A] [Module.Finite k A]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

def homogeneousPolynomialCoefficientSpan
    (W : Submodule k (MvPolynomial (Fin 4) k)) :
    Submodule K (MvPolynomial (Fin 4) K) :=
  Submodule.span K (MvPolynomial.map (algebraMap k K) '' (W : Set _))

/-- The actual restriction square on the homogeneous tensor component. -/
theorem homogeneousSectionRestriction_coefficientTensor_square
    (x : Fin 4 → A) (d : ℕ) :
    (homogeneousSectionRestriction (K := K)
      (fun r => (1 : K) ⊗ₜ[k] x r) d).comp
        (homogeneousIdealPieceAmbientCoefficientTensorMap (k := k) (K := K) d) =
      AlgebraTensorModule.lTensor K K (homogeneousSectionRestriction (K := k) x d) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul c p =>
    change homogeneousSectionRestriction (K := K) _ d
        (c • homogeneousIdealPieceAmbientCoefficientMap (k := k) (K := K) d p) =
      c ⊗ₜ[k] homogeneousSectionRestriction (K := k) x d p
    rw [map_smul]
    change c • aeval (R := K) (fun r => (1 : K) ⊗ₜ[k] x r)
        (MvPolynomial.map (algebraMap k K) p.val) =
      c ⊗ₜ[k] aeval (R := k) x p.val
    rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq k K (K ⊗[k] A)]
    change c • aeval (R := k) (fun r => (1 : K) ⊗ₜ[k] x r) p.val =
      c ⊗ₜ[k] aeval (R := k) x p.val
    rw [aeval_one_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private def homogeneousKernelCoefficientMap (x : Fin 4 → A) (d : ℕ) :
    LinearMap.ker (homogeneousSectionRestriction (K := k) x d) →ₗ[k]
      MvPolynomial (Fin 4) K :=
  (MvPolynomial.mapAlgHom (Algebra.ofId k K)).toLinearMap.comp
    ((homogeneousSubmodule (Fin 4) k d).subtype.comp
      (LinearMap.ker (homogeneousSectionRestriction (K := k) x d)).subtype)

private theorem homogeneousKernelCoefficientMap_tensor
    (x : Fin 4 → A) (d : ℕ)
    (z : K ⊗[k] LinearMap.ker (homogeneousSectionRestriction (K := k) x d)) :
    ((homogeneousIdealPieceAmbientCoefficientTensorMap (k := k) (K := K) d)
      ((AlgebraTensorModule.lTensor K K
        (LinearMap.ker (homogeneousSectionRestriction (K := k) x d)).subtype) z)).val =
      (LinearMap.liftBaseChange K (homogeneousKernelCoefficientMap (K := K) x d)) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, Submodule.coe_add, hz, hw]
  | tmul c p => rfl

/-- No quadratic-generation or full-system comparison certificate occurs:
flatness of the FIELD extension itself supplies the exact kernel equality. -/
theorem homogeneousVanishingPolynomialSubmodule_fieldExtension
    (x : Fin 4 → A) (d : ℕ) :
    homogeneousVanishingPolynomialSubmodule (K := K)
      (fun r => (1 : K) ⊗ₜ[k] x r) d =
    homogeneousPolynomialCoefficientSpan (K := K)
      (homogeneousVanishingPolynomialSubmodule (K := k) x d) := by
  apply le_antisymm
  · intro p hp
    obtain ⟨hphom, hpzero⟩ :=
      (mem_homogeneousVanishingPolynomialSubmodule_iff _ d p).mp hp
    let q : homogeneousSubmodule (Fin 4) K d := ⟨p, hphom⟩
    obtain ⟨z, hz⟩ :=
      (homogeneousIdealPieceAmbientCoefficientTensorMap_bijective (k := k) (K := K) d).2 q
    have hzker : z ∈ LinearMap.ker
        (AlgebraTensorModule.lTensor K K (homogeneousSectionRestriction (K := k) x d)) := by
      change AlgebraTensorModule.lTensor K K
        (homogeneousSectionRestriction (K := k) x d) z = 0
      rw [← homogeneousSectionRestriction_coefficientTensor_square x d]
      change homogeneousSectionRestriction (K := K) _ d
        (homogeneousIdealPieceAmbientCoefficientTensorMap d z) = 0
      rw [hz]
      exact hpzero
    rw [Module.Flat.ker_lTensor_eq K K] at hzker
    obtain ⟨w, hw⟩ := hzker
    have hvalue : (LinearMap.liftBaseChange K
        (homogeneousKernelCoefficientMap (K := K) x d)) w = p := by
      rw [← homogeneousKernelCoefficientMap_tensor x d w, hw, hz]
    have hrange : p ∈ LinearMap.range (LinearMap.liftBaseChange K
        (homogeneousKernelCoefficientMap (K := K) x d)) := ⟨w, hvalue⟩
    rw [LinearMap.range_liftBaseChange] at hrange
    apply (Submodule.span_mono ?_) hrange
    rintro _ ⟨s, rfl⟩
    refine ⟨s.val.val, ?_, rfl⟩
    exact ⟨s.val, s.property, rfl⟩
  · apply Submodule.span_le.mpr
    rintro p ⟨q, hq, rfl⟩
    obtain ⟨hqhom, hqzero⟩ :=
      (mem_homogeneousVanishingPolynomialSubmodule_iff x d q).mp hq
    apply (mem_homogeneousVanishingPolynomialSubmodule_iff _ d _).mpr
    refine ⟨hqhom.map _, ?_⟩
    change aeval (R := K) (fun r => (1 : K) ⊗ₜ[k] x r)
      (MvPolynomial.map (algebraMap k K) q) = 0
    rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq k K (K ⊗[k] A)]
    change aeval (R := k) (fun r => (1 : K) ⊗ₜ[k] x r) q = 0
    rw [aeval_one_tmul]
    change (1 : K) ⊗ₜ[k] aeval (R := k) x q = 0
    change aeval (R := k) x q = 0 at hqzero
    rw [hqzero, TensorProduct.tmul_zero]

private def homogeneousRestrictionTensorKernelMap (x : Fin 4 → A) (d : ℕ) :
    LinearMap.ker (AlgebraTensorModule.lTensor K K
      (homogeneousSectionRestriction (K := k) x d)) →ₗ[K]
        LinearMap.ker (homogeneousSectionRestriction (K := K)
          (fun r => (1 : K) ⊗ₜ[k] x r) d) where
  toFun z := ⟨homogeneousIdealPieceAmbientCoefficientTensorMap d z.val, by
    change homogeneousSectionRestriction (K := K) _ d
      (homogeneousIdealPieceAmbientCoefficientTensorMap d z.val) = 0
    have h := LinearMap.congr_fun
      (homogeneousSectionRestriction_coefficientTensor_square (K := K) x d) z.val
    exact h.trans z.property⟩
  map_add' z w := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c z := by apply Subtype.ext; exact map_smul _ _ _

private theorem homogeneousRestrictionTensorKernelMap_bijective
    (x : Fin 4 → A) (d : ℕ) :
    Function.Bijective (homogeneousRestrictionTensorKernelMap (k := k) (K := K) x d) := by
  obtain ⟨hi, hs⟩ :=
    homogeneousIdealPieceAmbientCoefficientTensorMap_bijective (k := k) (K := K) d
  constructor
  · intro z w h
    apply Subtype.ext
    apply hi
    exact congrArg Subtype.val h
  · intro q
    obtain ⟨z, hz⟩ := hs q.val
    have hzero : AlgebraTensorModule.lTensor K K
        (homogeneousSectionRestriction (K := k) x d) z = 0 := by
      rw [← homogeneousSectionRestriction_coefficientTensor_square x d]
      change homogeneousSectionRestriction (K := K) _ d
        (homogeneousIdealPieceAmbientCoefficientTensorMap d z) = 0
      rw [hz]
      exact q.property
    exact ⟨⟨z, hzero⟩, Subtype.ext hz⟩

/-- The restriction kernel is the actual flat base change of the original
kernel; this equivalence is not inferred from a numerical dimension bound. -/
def homogeneousSectionRestriction_fieldExtensionKernelEquiv
    (x : Fin 4 → A) (d : ℕ) :
    K ⊗[k] LinearMap.ker (homogeneousSectionRestriction (K := k) x d) ≃ₗ[K]
      LinearMap.ker (homogeneousSectionRestriction (K := K)
        (fun r => (1 : K) ⊗ₜ[k] x r) d) :=
  (LinearMap.tensorKerEquiv K K (homogeneousSectionRestriction (K := k) x d)).trans
    (LinearEquiv.ofBijective (homogeneousRestrictionTensorKernelMap (k := k) (K := K) x d)
      (homogeneousRestrictionTensorKernelMap_bijective (k := k) (K := K) x d))

theorem homogeneousVanishingPolynomialSubmodule_fieldExtension_finrank
    (x : Fin 4 → A) (d : ℕ) :
    finrank K (homogeneousVanishingPolynomialSubmodule (K := K)
      (fun r => (1 : K) ⊗ₜ[k] x r) d) =
      finrank k (homogeneousVanishingPolynomialSubmodule (K := k) x d) := by
  letI : Module.Free k (LinearMap.ker (homogeneousSectionRestriction (K := k) x d)) :=
    Module.Free.of_divisionRing k
      (LinearMap.ker (homogeneousSectionRestriction (K := k) x d))
  rw [homogeneousVanishingPolynomialSubmodule_finrank,
    homogeneousVanishingPolynomialSubmodule_finrank]
  rw [← (homogeneousSectionRestriction_fieldExtensionKernelEquiv (K := K) x d).finrank_eq]
  exact Module.finrank_baseChange
    (R := K) (S := k) (M' := LinearMap.ker (homogeneousSectionRestriction (K := k) x d))

end PfaffianDescent
