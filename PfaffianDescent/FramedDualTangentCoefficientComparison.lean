import PfaffianDescent.FramedDualCommonChartCoordinates
import PfaffianDescent.ScaledRelabeledFrameTangent
import PfaffianDescent.ActualNormalizedDualPresentationComparison

/-! SOURCE ONLY, UNVERIFIED. Extract off-diagonal tangent coefficients from
true SAME-component normalized epsilon comparison. Common-chart radial
terms disappear by basis-coordinate evaluation, never by deleting nilpotents. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Exact normalized first-order vector, including its radial correction. -/
theorem framedDualCommonChart_snd_vector
    (b : Basis (Fin 4) K (Fin 4 → K)) (U : Fin 4 → Fin 4 → K)
    (i j : Fin 4) (hc : b i j ≠ 0) :
    (fun m => (framedDualCommonChart b U i j hc m).snd) =
      (b i j)⁻¹ • (∑ s, U i s • b s) -
        ((b i j)⁻¹ ^ 2 * (∑ s, b s j * U i s)) • b i := by
  funext m
  change (↑((framedDualChartUnit b U i j hc)⁻¹) * framedDualRaw b U i m).snd = _
  rw [DualNumber.snd_mul, framedDualRaw_fst, framedDualRaw_snd]
  have hfst : (↑((framedDualChartUnit b U i j hc)⁻¹) : DualNumber K).fst = (b i j)⁻¹ := by
    simp [framedDualChartUnit]
  have hsnd : (↑((framedDualChartUnit b U i j hc)⁻¹) : DualNumber K).snd =
      -(b i j)⁻¹ ^ 2 * (∑ s, b s j * U i s) := by
    simp [framedDualChartUnit]
  rw [hfst, hsnd]
  change (b i j)⁻¹ * (∑ s, b s m * U i s) +
    (-(b i j)⁻¹ ^ 2 * (∑ s, b s j * U i s)) * b i m = _
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  have hs : (∑ s, b s m * U i s) = ∑ s, U i s * b s m := by
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hs]
  ring

theorem framedDualCommonChart_snd_repr_off_diagonal
    (b : Basis (Fin 4) K (Fin 4 → K)) (U : Fin 4 → Fin 4 → K)
    (i j s : Fin 4) (hc : b i j ≠ 0) (his : i ≠ s) :
    b.repr (fun m => (framedDualCommonChart b U i j hc m).snd) s =
      (b i j)⁻¹ * U i s := by
  rw [framedDualCommonChart_snd_vector]
  simp [map_sub, map_smul, map_sum, Finsupp.sub_apply, Finsupp.smul_apply,
    Finsupp.finset_sum_apply, Finsupp.single_apply, Basis.repr_self_apply, his, smul_eq_mul]

/-- INTERNAL bridge: its actual frame equality is derived by
actual_supplied_frame_support_labeling_and_basis_comparison. -/
theorem actual_framed_component_epsilon_tangent_comparison
    (b supplied : Basis (Fin 4) K (Fin 4 → K)) (j : Fin 4)
    (hb : ∀ i, b i j = 1) (rho : Equiv.Perm (Fin 4))
    (hc : ∀ i, supplied i j ≠ 0)
    (hBasis : supplied = scaledRelabeledFrame b rho
      (fun i => Units.mk0 (supplied i j) (hc i)))
    (U V : Fin 4 → Fin 4 → K) (hU : ∀ i, U i i = 0) (hV : ∀ i, V i i = 0)
    (i : Fin 4) (epsilon : K) (hepsilon : epsilon ≠ 0)
    (hCoords : ∀ m, framedDualCommonChart supplied V i j (hc i) m =
      dualNumberRescaleEquiv epsilon hepsilon
        (framedDualCommonChart b U (rho i) j (by rw [hb]; exact one_ne_zero) m)) :
    ∀ s, V i s = epsilon * supplied i j * U (rho i) (rho s) / supplied s j := by
  intro s
  by_cases his : i = s
  · subst s
    simp [hU, hV]
  have hrho : rho i ≠ rho s := fun h => his (rho.injective h)
  have hDirs : (fun m => (framedDualCommonChart supplied V i j (hc i) m).snd) =
      epsilon • (fun m => (framedDualCommonChart b U (rho i) j
        (by rw [hb]; exact one_ne_zero) m).snd) := by
    funext m
    have h := congrArg TrivSqZeroExt.snd (hCoords m)
    change (framedDualCommonChart supplied V i j (hc i) m).snd =
      (dualNumberRescale epsilon (framedDualCommonChart b U (rho i) j
        (by rw [hb]; exact one_ne_zero) m)).snd at h
    simpa only [dualNumberRescale, TrivSqZeroExt.snd_map,
      LinearMap.mulLeft_apply, Pi.smul_apply, smul_eq_mul] using h
  have hCoeff := congrArg (fun x : Fin 4 → K => supplied.repr x s) hDirs
  rw [framedDualCommonChart_snd_repr_off_diagonal supplied V i j s (hc i) his] at hCoeff
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hCoeff
  have hRepr (x : Fin 4 → K) : supplied.repr x s =
      (supplied s j)⁻¹ * b.repr x (rho s) := by
    calc
      supplied.repr x s = (scaledRelabeledFrame b rho
          (fun i => Units.mk0 (supplied i j) (hc i))).repr x s :=
        congrArg (fun e : Basis (Fin 4) K (Fin 4 → K) => e.repr x s) hBasis
      _ = _ := by
        simp only [scaledRelabeledFrame, Basis.repr_unitsSMul, Basis.repr_reindex_apply,
          Equiv.symm_symm, Units.smul_def, smul_eq_mul, Units.val_inv_eq_inv_val,
          Units.val_mk0]
  have hRight : supplied.repr (fun m => (framedDualCommonChart b U (rho i) j
      (by rw [hb]; exact one_ne_zero) m).snd) s =
      (supplied s j)⁻¹ * U (rho i) (rho s) := by
    rw [hRepr, framedDualCommonChart_snd_repr_off_diagonal b U (rho i) j (rho s)
      (by rw [hb]; exact one_ne_zero) hrho, hb]
    simp
  rw [hRight] at hCoeff
  have hMul := congrArg (fun a => supplied i j * a) hCoeff
  have hOut : V i s = supplied i j *
      (epsilon * ((supplied s j)⁻¹ * U (rho i) (rho s))) := by
    simpa only [← mul_assoc, mul_inv_cancel₀ (hc i), one_mul] using hMul
  rw [hOut, div_eq_mul_inv]
  ring

end PfaffianDescent.QuarticNet
