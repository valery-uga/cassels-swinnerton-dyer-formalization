import PfaffianDescent.HomogeneousEvaluationFieldExtension
import Mathlib.RingTheory.TensorProduct.Pi

/-! Exact flat scalar extension of the intersection of FOUR restriction
kernels. Different charts have different finite algebras and coordinates;
no global unit coordinate or ground hyperplane avoidance is required. -/

noncomputable section
namespace PfaffianDescent
open MvPolynomial Module
open scoped TensorProduct
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable (A : Fin 4 → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra k (A j)]
  [∀ j, Module.Finite k (A j)]

def homogeneousFourChartVanishingSystem
    (x : ∀ j, Fin 4 → A j) (d : ℕ) : Submodule k (MvPolynomial (Fin 4) k) :=
  ⨅ j : Fin 4, homogeneousVanishingPolynomialSubmodule (K := k) (x j) d

private theorem aeval_fourChart_product_apply
    (x : ∀ j, Fin 4 → A j) (p : MvPolynomial (Fin 4) k) (j : Fin 4) :
    (aeval (R := k) (fun r j => x j r) p) j = aeval (R := k) (x j) p :=
  comp_aeval_apply _ (Pi.evalAlgHom k A j) p

private theorem homogeneousFourChartVanishingSystem_eq_product_kernel
    (x : ∀ j, Fin 4 → A j) (d : ℕ) :
    homogeneousFourChartVanishingSystem A x d =
      homogeneousVanishingPolynomialSubmodule (K := k) (fun r j => x j r) d := by
  ext p
  constructor
  · intro hp
    have hall := (Submodule.mem_iInf _).mp hp
    apply (mem_homogeneousVanishingPolynomialSubmodule_iff _ d p).mpr
    refine ⟨((mem_homogeneousVanishingPolynomialSubmodule_iff _ d p).mp (hall 0)).1, ?_⟩
    apply funext
    intro j
    change (aeval (R := k) (fun r j => x j r) p) j = 0
    rw [aeval_fourChart_product_apply]
    exact ((mem_homogeneousVanishingPolynomialSubmodule_iff _ d p).mp (hall j)).2
  · intro hp
    obtain ⟨hhom, hzero⟩ := (mem_homogeneousVanishingPolynomialSubmodule_iff _ d p).mp hp
    apply (Submodule.mem_iInf _).mpr
    intro j
    apply (mem_homogeneousVanishingPolynomialSubmodule_iff _ d p).mpr
    exact ⟨hhom, (aeval_fourChart_product_apply A x p j).symm.trans (congrFun hzero j)⟩

private theorem aeval_fourChart_tensorProduct_zero_iff
    (x : ∀ j, Fin 4 → A j) (p : MvPolynomial (Fin 4) K) :
    aeval (R := K) (fun r => (1 : K) ⊗ₜ[k] (fun j => x j r)) p = 0 ↔
      ∀ j : Fin 4, aeval (R := K) (fun r => (1 : K) ⊗ₜ[k] x j r) p = 0 := by
  let e := Algebra.TensorProduct.piRight k K K A
  have he : e (aeval (R := K) (fun r => (1 : K) ⊗ₜ[k] (fun j => x j r)) p) =
      aeval (R := K) (fun r j => (1 : K) ⊗ₜ[k] x j r) p :=
    comp_aeval_apply _ e.toAlgHom p
  have hj (j : Fin 4) :
      e (aeval (R := K) (fun r => (1 : K) ⊗ₜ[k] (fun j => x j r)) p) j =
        aeval (R := K) (fun r => (1 : K) ⊗ₜ[k] x j r) p := by
    rw [he]
    exact comp_aeval_apply _ (Pi.evalAlgHom K (fun j => K ⊗[k] A j) j) p
  constructor
  · intro hz j
    rw [← hj j, hz, map_zero]
    rfl
  · intro hz
    apply e.injective
    rw [map_zero]
    apply funext
    intro j
    exact (hj j).trans (hz j)

/-- The new four-chart intersection is EXACTLY the span of coefficient
extensions of the old intersection. Field flatness commutes with the
combined product-valued restriction, not merely each equation separately. -/
theorem homogeneousFourChartVanishingSystem_fieldExtension
    (x : ∀ j, Fin 4 → A j) (d : ℕ) :
    homogeneousFourChartVanishingSystem (k := K) (fun j => K ⊗[k] A j)
      (fun j r => (1 : K) ⊗ₜ[k] x j r) d =
      homogeneousPolynomialCoefficientSpan (K := K)
        (homogeneousFourChartVanishingSystem (k := k) A x d) := by
  have hnew : homogeneousFourChartVanishingSystem (k := K) (fun j => K ⊗[k] A j)
      (fun j r => (1 : K) ⊗ₜ[k] x j r) d =
      homogeneousVanishingPolynomialSubmodule (K := K)
        (fun r => (1 : K) ⊗ₜ[k] (fun j => x j r)) d := by
    ext p
    constructor
    · intro hp
      have hall := (Submodule.mem_iInf _).mp hp
      apply (mem_homogeneousVanishingPolynomialSubmodule_iff _ d p).mpr
      refine ⟨((mem_homogeneousVanishingPolynomialSubmodule_iff _ d p).mp (hall 0)).1, ?_⟩
      apply (aeval_fourChart_tensorProduct_zero_iff A x p).mpr
      intro j
      exact ((mem_homogeneousVanishingPolynomialSubmodule_iff _ d p).mp (hall j)).2
    · intro hp
      obtain ⟨hhom, hzero⟩ := (mem_homogeneousVanishingPolynomialSubmodule_iff _ d p).mp hp
      have hall := (aeval_fourChart_tensorProduct_zero_iff A x p).mp hzero
      apply (Submodule.mem_iInf _).mpr
      intro j
      exact (mem_homogeneousVanishingPolynomialSubmodule_iff _ d p).mpr ⟨hhom, hall j⟩
  rw [hnew, homogeneousFourChartVanishingSystem_eq_product_kernel (k := k)]
  exact homogeneousVanishingPolynomialSubmodule_fieldExtension (K := K) (fun r j => x j r) d

theorem homogeneousFourChartVanishingSystem_fieldExtension_finrank
    (x : ∀ j, Fin 4 → A j) (d : ℕ) :
    finrank K (homogeneousFourChartVanishingSystem (k := K) (fun j => K ⊗[k] A j)
      (fun j r => (1 : K) ⊗ₜ[k] x j r) d) =
      finrank k (homogeneousFourChartVanishingSystem (k := k) A x d) := by
  rw [homogeneousFourChartVanishingSystem_fieldExtension]
  rw [homogeneousFourChartVanishingSystem_eq_product_kernel (k := k) A x d]
  rw [← homogeneousVanishingPolynomialSubmodule_fieldExtension (K := K)
    (fun r j => x j r) d]
  exact homogeneousVanishingPolynomialSubmodule_fieldExtension_finrank (K := K)
    (fun r j => x j r) d

end PfaffianDescent
