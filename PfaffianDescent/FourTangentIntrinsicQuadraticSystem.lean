import PfaffianDescent.FourTangentEmbeddedFullBaseAlternative
import PfaffianDescent.NormalizedPointIntrinsicQuadraticRestriction

/-! The FULL intrinsic quadratic series of the actual four-double-point
immersion equals its product-dual evaluation kernel, also in the exceptional
twisted-cubic branch. No finite-base or complete-intersection premise is used. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem fourTangent_intrinsicQuadraticSystem_eq_normalizedKernel
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ i, U i i = 0) :
    intrinsicFullQuadraticSystem
      (fourTangentDualToProjective U ≫ quotientProjMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))) =
      homogeneousVanishingPolynomialSubmodule (fourTangentNormalizedCoordinates U) 2 := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) := ⊥
  let x := fourTangentNormalizedCoordinates U
  let ell := fourTangentChartLinearForm (K := K)
  let hell := fourTangentChartLinearForm_homogeneous (K := K)
  let hOne := fourTangentNormalizedLinearForm_eval U
  let he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K (FourTangentDualAlgebra K)) x = 0 := by
    intro p hp
    have hp0 : p = 0 := by simpa [I] using hp
    subst p
    simp
  apply le_antisymm
  · intro p hp
    apply (mem_homogeneousVanishingPolynomialSubmodule_iff x 2 p).mpr
    refine ⟨hp.1, ?_⟩
    change aeval (R := K) x p = 0
    funext row
    let φ := Pi.evalAlgHom K (fun _ : Fin 4 => DualNumber K) row
    let y : Fin 4 → DualNumber K := fun j => φ (x j)
    letI : Module.Finite K (DualNumber K) := dualNumber_moduleFinite
    have hyOne : ell.eval₂ (algebraMap K (DualNumber K)) y = 1 := by
      change aeval (R := K) (fun j => φ (x j)) ell = 1
      rw [← comp_aeval_apply x φ ell]
      exact (congrArg φ hOne).trans (map_one φ)
    let heY : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K (DualNumber K)) y = 0 := by
      intro p hp
      have hp0 : p = 0 := by simpa [I] using hp
      subst p
      simp
    have hpoint : linearNormalizedPoint I y ell hell hyOne heY =
        Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ fourTangentDualToProjective U := by
      simpa only [linearNormalizedPoint, linearNormalizedPointChartMap,
        fourTangentDualToProjective, fourTangentNormalizedEquationPoint,
        linearNormalizedPointAt, linearNormalizedPointChartMapAt, I, x, ell, hell] using
        linearNormalizedPointAt_naturality I x he φ y (fun _ => rfl) heY
          (Ideal.Quotient.mk I.toIdeal ell) (polynomial_class_mem_grading I ell hell)
          (by change ell.eval₂ (algebraMap K (FourTangentDualAlgebra K)) x = 1; exact hOne)
          (by change ell.eval₂ (algebraMap K (DualNumber K)) y = 1; exact hyOne)
    have hyRow : y row = fourTangentChartScale U row := by
      simp [y, φ, x, fourTangentNormalizedCoordinates, fourTangentRawCoordinates,
        tangentDualPoint, hdiag row]
    have huRow : IsUnit (y row) := by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨fourTangentChartScaleInverse U row, ?_⟩
      rw [hyRow]
      exact congrFun (fourTangentChartScale_mul_inverse U) row
    obtain ⟨u, hu⟩ := huRow
    have hpRow : p ∈ intrinsicFullQuadraticSystem
        (linearNormalizedPoint I y ell hell hyOne heY ≫ quotientProjMap I) := by
      rw [hpoint, Category.assoc]
      exact intrinsicFullQuadraticSystem_le_comp
        (Spec.map (CommRingCat.ofHom φ.toRingHom))
        (fourTangentDualToProjective U ≫ quotientProjMap I) hp
    have hzero := linearNormalizedPoint_intrinsicQuadratics_evaluation_zero_of_unit_coordinate
      I y ell hell hyOne heY row u hu p hpRow
    have hcomponent : φ (aeval (R := K) x p) = 0 := by
      rw [comp_aeval_apply]
      exact hzero
    exact hcomponent
  · simpa only [fourTangentDualToProjective, fourTangentNormalizedEquationPoint,
      normalizedFiniteEquationPoint, I, x, ell, hell] using
      normalizedFiniteEquationPoint_evaluationQuadrics_le_intrinsic I x ell hell hOne he

theorem fourTangent_intrinsicQuadraticSystem_eq_tangentKernel
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ i, U i i = 0) :
    intrinsicFullQuadraticSystem
      (fourTangentDualToProjective U ≫ quotientProjMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))) =
      homogeneousTangentQuadrics U :=
  (fourTangent_intrinsicQuadraticSystem_eq_normalizedKernel U hdiag).trans
    (fourTangentNormalized_quadratic_kernel U)

theorem fourTangent_intrinsicFullQuadraticBaseIdeal_eq
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ i, U i i = 0) :
    intrinsicFullQuadraticBaseIdeal
      (fourTangentDualToProjective U ≫ quotientProjMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))) =
      fourTangentFullQuadraticBaseIdeal U := by
  apply HomogeneousIdeal.toIdeal_injective
  change Ideal.span (intrinsicFullQuadraticSystem
    (fourTangentDualToProjective U ≫ quotientProjMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))) :
        Set (MvPolynomial (Fin 4) K)) =
      Ideal.span (homogeneousTangentQuadrics U : Set (MvPolynomial (Fin 4) K))
  rw [fourTangent_intrinsicQuadraticSystem_eq_tangentKernel U hdiag]

end PfaffianDescent.QuarticNet
