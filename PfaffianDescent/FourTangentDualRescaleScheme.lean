import PfaffianDescent.QuarticTangentRescalingExactKernel
import PfaffianDescent.FourTangentDualCoordinates
import PfaffianDescent.FourTangentEmbeddedFullBaseAlternative

/-! Nonzero tangent rescaling as an actual product-dual algebra equivalence
and exact scheme morphism. The source stays the same four double points;
its nilpotent coordinates transform by the existing dualNumberRescale map. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Inverse nonzero tangent rescaling multiplies epsilon by c⁻¹. -/
def dualNumberRescaleEquiv (c : K) (hc : c ≠ 0) : DualNumber K ≃ₐ[K] DualNumber K :=
  AlgEquiv.ofAlgHom (dualNumberRescale c) (dualNumberRescale c⁻¹)
    (by
      apply AlgHom.ext
      intro z
      apply TrivSqZeroExt.ext <;>
        simp [dualNumberRescale, AlgHom.comp_apply, TrivSqZeroExt.fst_map,
          TrivSqZeroExt.snd_map, mul_assoc, hc])
    (by
      apply AlgHom.ext
      intro z
      apply TrivSqZeroExt.ext <;>
        simp [dualNumberRescale, AlgHom.comp_apply, TrivSqZeroExt.fst_map,
          TrivSqZeroExt.snd_map, mul_assoc, hc])

/-- The SAME four components are rescaled independently, with no relabeling. -/
def fourTangentDualRescaleEquiv (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0) :
    FourTangentDualAlgebra K ≃ₐ[K] FourTangentDualAlgebra K :=
  AlgEquiv.piCongrRight (fun i => dualNumberRescaleEquiv (l i) (hl i))

@[simp] theorem fourTangentDualRescaleEquiv_apply
    (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0) (z : FourTangentDualAlgebra K) (i : Fin 4) :
    fourTangentDualRescaleEquiv l hl z i = dualNumberRescale (l i) (z i) := rfl

theorem fourTangentDualRescaleEquiv_raw
    (U : Fin 4 → Fin 4 → K) (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0) (r : Fin 4) :
    fourTangentDualRescaleEquiv l hl (fourTangentRawCoordinates U r) =
      fourTangentRawCoordinates (rescaleTangentDirections l U) r := by
  funext i
  rw [fourTangentDualRescaleEquiv_apply]
  apply TrivSqZeroExt.ext <;>
    simp [fourTangentRawCoordinates, dualNumberRescale, tangentDualPoint,
      rescaleTangentDirections, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map] <;> ring

theorem fourTangentDualRescaleEquiv_chartScale
    (U : Fin 4 → Fin 4 → K) (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0) :
    fourTangentDualRescaleEquiv l hl (fourTangentChartScale U) =
      fourTangentChartScale (rescaleTangentDirections l U) := by
  funext i
  rw [fourTangentDualRescaleEquiv_apply]
  apply TrivSqZeroExt.ext <;>
    simp [fourTangentChartScale, dualNumberRescale, rescaleTangentDirections,
      TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, Finset.sum_mul, Finset.mul_sum,
      mul_comm]

/-- The normalized coordinate algebra itself is transported, not merely
the polynomial zero kernel. -/
theorem fourTangentDualRescaleEquiv_normalized
    (U : Fin 4 → Fin 4 → K) (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0) (r : Fin 4) :
    fourTangentDualRescaleEquiv l hl (fourTangentNormalizedCoordinates U r) =
      fourTangentNormalizedCoordinates (rescaleTangentDirections l U) r := by
  simp only [fourTangentNormalizedCoordinates, map_mul,
    fourTangentDualRescaleEquiv_chartScale, fourTangentDualRescaleEquiv_raw]

/-- Exact projective embedding square for the actual product-dual scheme.
The nonzero row factors act on its epsilon coordinates by an actual algebra
isomorphism, hence by the literal Spec map on the same source scheme. -/
theorem fourTangentDualToProjective_rescale
    (U : Fin 4 → Fin 4 → K) (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0) :
    fourTangentDualToProjective (rescaleTangentDirections l U) =
      Spec.map (CommRingCat.ofHom (fourTangentDualRescaleEquiv l hl).toRingHom) ≫
        fourTangentDualToProjective U := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) := ⊥
  let x := fourTangentNormalizedCoordinates U
  let y := fourTangentNormalizedCoordinates (rescaleTangentDirections l U)
  let ell := fourTangentChartLinearForm (K := K)
  let hell := fourTangentChartLinearForm_homogeneous (K := K)
  let heX : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K (FourTangentDualAlgebra K)) x = 0 := by
    intro p hp
    have hp0 : p = 0 := Ideal.mem_bot.mp hp
    simp [hp0]
  let heY : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K (FourTangentDualAlgebra K)) y = 0 := by
    intro p hp
    have hp0 : p = 0 := Ideal.mem_bot.mp hp
    simp [hp0]
  have hcoords : ∀ r, y r = (fourTangentDualRescaleEquiv l hl).toAlgHom (x r) :=
    fun r => (fourTangentDualRescaleEquiv_normalized U l hl r).symm
  have hRing : (fourTangentDualRescaleEquiv l hl).toAlgHom.toRingHom =
      (fourTangentDualRescaleEquiv l hl).toRingHom := rfl
  simpa only [fourTangentDualToProjective, fourTangentNormalizedEquationPoint,
    I, x, y, ell, hell, hRing] using
    linearNormalizedPointAt_naturality I x heX
      (fourTangentDualRescaleEquiv l hl).toAlgHom y hcoords heY
      (Ideal.Quotient.mk I.toIdeal ell) (polynomial_class_mem_grading I ell hell)
      (by change ell.eval₂ (algebraMap K (FourTangentDualAlgebra K)) x = 1
          exact fourTangentNormalizedLinearForm_eval U)
      (by change ell.eval₂ (algebraMap K (FourTangentDualAlgebra K)) y = 1
          exact fourTangentNormalizedLinearForm_eval (rescaleTangentDirections l U))

end PfaffianDescent.QuarticNet
