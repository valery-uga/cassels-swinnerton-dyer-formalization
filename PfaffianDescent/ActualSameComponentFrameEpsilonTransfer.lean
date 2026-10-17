import PfaffianDescent.FramedDualTangentCoefficientComparison
import PfaffianDescent.ActualSuppliedFrameSupportLabeling

/-! SOURCE ONLY, UNVERIFIED. INTERNAL consumer of actual construction data:
SAME component/source/original ambient q throughout. Actual source isos and
embedding squares are literal presentations, not assertions of any desired
matrix equality, Galois graph or full-base conclusion. The original-Z caller
must derive its canonical presentations from its actual component factory. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- All ambient-square transport and independent epsilon rescaling are
proved here. The frame comparison hBasis is an INTERNAL input derived by the
actual-support-set theorem; it is not a final paper-facing premise. -/
theorem actual_same_component_frame_epsilon_transfer
    (b supplied : Basis (Fin 4) K (Fin 4 → K)) (j : Fin 4)
    (hb : ∀ r, b r j = 1) (rho : Equiv.Perm (Fin 4))
    (hc : ∀ r, supplied r j ≠ 0)
    (hBasis : supplied = QuarticNet.scaledRelabeledFrame b rho
      (fun r => Units.mk0 (supplied r j) (hc r)))
    (Z : Fin 4 → Scheme.{u})
    (q : ∀ r, Z r ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (U V : Fin 4 → Fin 4 → K) (hU : ∀ r, U r r = 0) (hV : ∀ r, V r r = 0)
    (canonicalE suppliedE : ∀ r, Z r ≅ Spec (.of (DualNumber K)))
    (hCanonical : ∀ r, (canonicalE r).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K) (QuarticNet.tangentDualPoint U (rho r))
        (rho r) (by simp [QuarticNet.tangentDualPoint, hU]) ≫
      (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix b)
        (QuarticNet.basisCoordinateMatrix_isUnit b)).inv = q r)
    (hSupplied : ∀ r, (suppliedE r).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K) (QuarticNet.tangentDualPoint V r)
        r (by simp [QuarticNet.tangentDualPoint, hV]) ≫
      (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
        (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv = q r) :
    ∃ (epsilon : Fin 4 → K) (hepsilon : ∀ r, epsilon r ≠ 0),
      V = QuarticNet.suppliedFrameTangent U rho (fun r => supplied r j) epsilon ∧
      (∀ r, (suppliedE r).hom ≫ Spec.map (CommRingCat.ofHom
        (QuarticNet.dualNumberRescaleEquiv (epsilon r) (hepsilon r)).toRingHom) =
          (canonicalE r).hom) := by
  classical
  have hPresentations (r : Fin 4) :
      ∃ (epsilon : K) (hepsilon : epsilon ≠ 0),
        (∀ m, QuarticNet.framedDualCommonChart supplied V r j (hc r) m =
          QuarticNet.dualNumberRescaleEquiv epsilon hepsilon
            (QuarticNet.framedDualCommonChart b U (rho r) j
              (by rw [hb]; exact one_ne_zero) m)) ∧
        (suppliedE r).hom ≫ Spec.map (CommRingCat.ofHom
          (QuarticNet.dualNumberRescaleEquiv epsilon hepsilon).toRingHom) =
            (canonicalE r).hom := by
    have hCan : (canonicalE r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (QuarticNet.framedDualCommonChart b U (rho r) j
          (by rw [hb]; exact one_ne_zero)) j
        (QuarticNet.framedDualCommonChart_one b U (rho r) j
          (by rw [hb]; exact one_ne_zero)) = q r := by
      rw [← QuarticNet.framedDual_common_chart_actual_square b U hU (rho r) j
        (by rw [hb]; exact one_ne_zero)]
      exact hCanonical r
    have hSup : (suppliedE r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (QuarticNet.framedDualCommonChart supplied V r j (hc r)) j
        (QuarticNet.framedDualCommonChart_one supplied V r j (hc r)) = q r := by
      rw [← QuarticNet.framedDual_common_chart_actual_square supplied V hV r j (hc r)]
      exact hSupplied r
    exact actual_normalized_dual_presentations_epsilon_comparison (q r)
      (QuarticNet.framedDualCommonChart b U (rho r) j
        (by rw [hb]; exact one_ne_zero))
      (QuarticNet.framedDualCommonChart supplied V r j (hc r)) j
      (QuarticNet.framedDualCommonChart_one b U (rho r) j
        (by rw [hb]; exact one_ne_zero))
      (QuarticNet.framedDualCommonChart_one supplied V r j (hc r))
      (canonicalE r) (suppliedE r) hCan hSup
  choose epsilon hepsilon hCoords hSquares using hPresentations
  refine ⟨epsilon, hepsilon, ?_, hSquares⟩
  funext r s
  exact QuarticNet.actual_framed_component_epsilon_tangent_comparison b supplied j hb rho hc
    hBasis U V hU hV r (epsilon r) (hepsilon r) (hCoords r) s

end PfaffianDescent
