import PfaffianDescent.ActualFieldPointChartNormalizer
import PfaffianDescent.ScaledRelabeledFrameTangent

/-! SOURCE ONLY, UNVERIFIED. Unlike the earlier common-chart adapter, this
one assumes NO supplied-column normalizer nonvanishing. Every normalizer is
derived from equality of actual field-valued support maps. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem actual_cross_chart_frame_basis_eq_scaled_relabel
    (b supplied : Basis (Fin 4) K (Fin 4 → K)) (j : Fin 4)
    (hb : ∀ i, b i j = 1) (rho : Equiv.Perm (Fin 4))
    (hPoint : ∀ i r (hr : supplied i r ≠ 0),
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => supplied i s / supplied i r) r (by exact div_self hr) =
      ambientNormalizedCoordinateChartPoint (F := K) (b (rho i)) j (hb (rho i))) :
    ∃ hNormalizer : ∀ i, supplied i j ≠ 0,
      supplied = QuarticNet.scaledRelabeledFrame b rho
        (fun i => Units.mk0 (supplied i j) (hNormalizer i)) := by
  classical
  have hColumns (i : Fin 4) : supplied i j ≠ 0 ∧
      ∀ s, supplied i s = supplied i j * b (rho i) s := by
    obtain ⟨r, hr⟩ : ∃ r, supplied i r ≠ 0 := by
      by_contra h
      push_neg at h
      exact supplied.ne_zero i (funext h)
    obtain ⟨hRatioNe, hRatio⟩ := actual_normalized_point_equal_cross_chart_coordinates
      (fun s => supplied i s / supplied i r) (b (rho i)) r j
      (by exact div_self hr) (hb (rho i)) (hPoint i r hr)
    refine ⟨?_, ?_⟩
    · intro hz
      apply hRatioNe
      simp [hz]
    · intro s
      calc
        supplied i s = supplied i r * (supplied i s / supplied i r) := by
          field_simp [hr]
          <;> ring
        _ = supplied i r * ((supplied i j / supplied i r) * b (rho i) s) :=
          congrArg (fun a => supplied i r * a) (hRatio s)
        _ = supplied i j * b (rho i) s := by
          field_simp [hr]
          <;> ring
  refine ⟨fun i => (hColumns i).1, ?_⟩
  apply DFunLike.ext
  intro i
  funext s
  rw [QuarticNet.scaledRelabeledFrame_column]
  change supplied i s = supplied i j * b (rho i) s
  exact (hColumns i).2 s

end PfaffianDescent
