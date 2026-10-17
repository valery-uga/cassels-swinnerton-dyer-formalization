import PfaffianDescent.AmbientNormalizedPointUnitChartComparison
import PfaffianDescent.CoordinateVertexLengthTwoActualTangent
import PfaffianDescent.FourTangentIntrinsicFullBaseAlternative

/-! Each component of the actual normalized product-dual embedding equals
its own raw vertex tangent point in its own vertex chart. This is a scheme
morphism identity, derived across the change of common linear normalizer. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem fourTangentDual_component_actual_ambient_square
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ r, U r r = 0) (row : Fin 4) :
    Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun _ : Fin 4 => DualNumber K) row)) ≫
      fourTangentDualToProjective U ≫ quotientProjMap ⊥ =
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun r => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) row r) +
          TrivSqZeroExt.inr (U row r)) row
        (by simp [coordinateVertexCoordinates, hdiag]) := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) := ⊥
  let x := fourTangentNormalizedCoordinates U
  let phi := Pi.evalAlgHom K (fun _ : Fin 4 => DualNumber K) row
  let y : Fin 4 → DualNumber K := fun r => phi (x r)
  let ell := fourTangentChartLinearForm (K := K)
  let hell := fourTangentChartLinearForm_homogeneous (K := K)
  let heX : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K (FourTangentDualAlgebra K)) x = 0 := by
    intro p hp
    simp [Ideal.mem_bot.mp hp]
  let heY : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K (DualNumber K)) y = 0 := by
    intro p hp
    simp [Ideal.mem_bot.mp hp]
  have hOneX : ell.eval₂ (algebraMap K (FourTangentDualAlgebra K)) x = 1 :=
    fourTangentNormalizedLinearForm_eval U
  have hOneY : ell.eval₂ (algebraMap K (DualNumber K)) y = 1 := by
    change aeval (R := K) y ell = 1
    have h : aeval (R := K) y ell = phi (aeval (R := K) x ell) :=
      (comp_aeval_apply x phi ell).symm
    rw [h]
    change phi (ell.eval₂ (algebraMap K (FourTangentDualAlgebra K)) x) = 1
    rw [hOneX, map_one]
  have hNatural : linearNormalizedPoint I y ell hell hOneY heY =
      Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ fourTangentDualToProjective U := by
    simpa only [linearNormalizedPoint, linearNormalizedPointChartMap,
      fourTangentDualToProjective, fourTangentNormalizedEquationPoint,
      linearNormalizedPointAt, linearNormalizedPointChartMapAt, I, x, y, ell, hell] using
      linearNormalizedPointAt_naturality I x heX phi y (fun _ => rfl) heY
        (Ideal.Quotient.mk I.toIdeal ell) (polynomial_class_mem_grading I ell hell)
        (by exact hOneX) (by exact hOneY)
  let c : DualNumber K := 1 - TrivSqZeroExt.inr (∑ r : Fin 4, U row r)
  let d : DualNumber K := 1 + TrivSqZeroExt.inr (∑ r : Fin 4, U row r)
  have hcd : c * d = 1 := by
    apply TrivSqZeroExt.ext <;> simp [c, d, DualNumber.snd_mul]
  have hdc : d * c = 1 := by rw [mul_comm]; exact hcd
  let cu : (DualNumber K)ˣ := ⟨c, d, hcd, hdc⟩
  have hyrow : (cu : DualNumber K) = y row := by
    simp [cu, c, y, phi, x, fourTangentNormalizedCoordinates,
      fourTangentChartScale, fourTangentRawCoordinates, tangentDualPoint, hdiag]
  have hcoords : (fun r => (↑(cu⁻¹) : DualNumber K) * y r) =
      (fun r => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) row r) +
        TrivSqZeroExt.inr (U row r)) := by
    funext r
    change d * (c * tangentDualPoint U row r) = _
    rw [← mul_assoc, hdc, one_mul]
    apply TrivSqZeroExt.ext <;>
      simp [coordinateVertexCoordinates, tangentDualPoint]
  change Spec.map (CommRingCat.ofHom phi.toRingHom) ≫
      fourTangentDualToProjective U ≫ quotientProjMap I = _
  rw [← Category.assoc, ← hNatural, linearNormalizedPoint_toAmbient_eq_unit_coordinateChartPoint
    I y ell hell hOneY heY row cu hyrow]
  have hcongr (a b : Fin 4 → DualNumber K) (ha : a row = 1) (hb : b row = 1)
      (hab : a = b) : ambientNormalizedCoordinateChartPoint (F := K) a row ha =
        ambientNormalizedCoordinateChartPoint (F := K) b row hb := by
    subst b
    rfl
  exact hcongr _ _ _ _ hcoords

end PfaffianDescent.QuarticNet
