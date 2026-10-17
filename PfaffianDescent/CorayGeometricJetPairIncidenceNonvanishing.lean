import PfaffianDescent.CorayOriginalNativeFullJetHyperplaneDictionary
import PfaffianDescent.CorayBoundedOriginalGeometricEvaluation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A genuine nonzero equation for geometric tangent-plane pair incidence.
The hyperplane is constructed from actual full-jet values; the SAME original
geometric generic image proves its other-point value nonzero. No good line,
incidence dimension or noninclusion premise is supplied. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- A full surface jet has exactly three coefficient-field linear conditions.
For m>3, construct a nonzero hyperplane containing that entire actual jet. -/
theorem surfacePlaneJet_values_exists_nonzero_hyperplane001
    {M : Type u} [Field M] {m : ℕ} (hm : 3 < m)
    (w : Fin m → SurfacePlaneJet M) :
    ∃ c : Fin m → M, c ≠ 0 ∧ ∑ i, c i • w i = 0 := by
  classical
  letI : FiniteDimensional M (SurfacePlaneJet M) := by
    change FiniteDimensional M (M × (Fin 2 → M))
    infer_instance
  let E : (Fin m → M) →ₗ[M] SurfacePlaneJet M := Fintype.linearCombination M w
  have hDim : finrank M (SurfacePlaneJet M) = 3 := by
    change finrank M (M × (Fin 2 → M)) = 3
    simp [Module.finrank_prod, Module.finrank_pi_fintype]
  have hSource : finrank M (Fin m → M) = m := by
    simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_id]
  have hKer : LinearMap.ker E ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    simpa only [hDim, hSource] using hm)
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKer
  refine ⟨c, hc0, ?_⟩
  simpa only [E, Fintype.linearCombination_apply] using LinearMap.mem_ker.mp hc

/-- ORIGINAL p/W/b and an actual normalized surface jet construct a
hyperplane with zero whole first-point jet, and its value at the fresh
geometric generic point of the SAME evaluation image is PROVED nonzero.
Taking M to be the original source function field gives a nonzero rational
pair-incidence equation. No hyperplane outcome is assumed. -/
theorem cubicThroughPointBasis_originalJet_exists_geometricHyperplane_notWholeImage001
    {K L M : Type u} [Field K] [CommRing L] [Field M]
    [Algebra K L] [Algebra K M] [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m)
    (hsize : finrank K L + 5 ≤ (n + 3).choose 3 - n.choose 3)
    (z : Fin 4 → M) (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) = 0)
    (hAnchor : surfacePlaneJetCoordinates z v j = 1) :
    let F := (hypersurface p hp).functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    letI : IsDomain (M ⊗[K] F) := cubicOriginalFunctionField_tensor_isDomain (B := M) p hp hp0
    let gJ := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    ∃ c : Fin m → M, c ≠ 0 ∧
      (∑ i, c i • gJ (e (b i))) = 0 ∧
      projectiveEvaluationChartMap
        (cubicTensorFractionCoefficientHom (B := M) p hp)
        (cubicThroughPointBasisTensorFractionCoordinates (B := M) p hp n y hpy j b) a
        (cubicThroughPointBasisTensorFractionCoordinates_ne_zero (B := M) p hp hp0 n y hpy j b a)
        (projectiveChartLinearForm a c) ≠ 0 := by
  classical
  let F := (hypersurface p hp).functionField
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  letI : IsDomain (M ⊗[K] F) := cubicOriginalFunctionField_tensor_isDomain (B := M) p hp hp0
  let gJ := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  have hRank := cubicThroughCoordinateSections_finrank_ge_five p hp hp0 n y hpy hsize
  have hm : 3 < m := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin] at hRank
    omega
  obtain ⟨c, hc, hJet⟩ := surfacePlaneJet_values_exists_nonzero_hyperplane001 hm
    (fun i => gJ (e (b i)))
  refine ⟨c, hc, hJet, ?_⟩
  intro hZero
  exact hc ((cubicThroughPointBasisTensorFractionPoint_linearForm_zero_iff
    (B := M) p hp hp0 n y hpy j b a c).mp hZero)

end PfaffianDescent.Coray
