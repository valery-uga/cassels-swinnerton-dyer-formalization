import PfaffianDescent.CorayOriginalFiniteEtaleKernelDescent

noncomputable section
namespace PfaffianDescent.Coray
open TensorProduct
universe u
set_option autoImplicit false

/-- The literal scalar-extended ORIGINAL basis evaluation, in actual
coefficient coordinates. Its target is ALL actual points of the SAME
scalar-extended finite etale algebra. -/
def originalFiniteEtaleGeometricCoefficientEvaluation
    {K A M : Type u} [Field K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Algebra.FiniteType K A]
    [Algebra.FormallyEtale K A] [IsSepClosed M]
    {m : ℕ} (v : Fin m → A) :
    (Fin m → M) →ₗ[M] (PrimeSpectrum (M ⊗[K] A) → M) :=
  ((originalFiniteEtaleGeometricSplit (K := K) (A := A) (M := M)).toLinearMap.comp
    (AlgebraTensorModule.lTensor M M (Fintype.linearCombination K v))).comp
      (TensorProduct.piScalarRight K M M (Fin m)).symm.toLinearMap

/-- Every literal coefficient row is evaluation of the ORIGINAL values
at its actual geometric point; the originalK coefficient square is exact. -/
theorem originalFiniteEtaleGeometricCoefficientEvaluation_apply001
    {K A M : Type u} [Field K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Algebra.FiniteType K A]
    [Algebra.FormallyEtale K A] [IsSepClosed M]
    {m : ℕ} (v : Fin m → A) (c : Fin m → M)
    (p : PrimeSpectrum (M ⊗[K] A)) :
    originalFiniteEtaleGeometricCoefficientEvaluation (K := K) v c p =
      ∑ i, c i * originalFiniteEtaleGeometricPoint (K := K) (A := A) (M := M) p (v i) := by
  classical
  let F := originalFiniteEtaleGeometricCoefficientEvaluation (K := K) (M := M) v
  have hSingle (i : Fin m) (a : M) : F (Pi.single i a) p =
      a * originalFiniteEtaleGeometricPoint (K := K) (A := A) (M := M) p (v i) := by
    change originalFiniteEtaleGeometricSplit (K := K) (A := A) (M := M)
      (AlgebraTensorModule.lTensor M M (Fintype.linearCombination K v)
        ((TensorProduct.piScalarRight K M M (Fin m)).symm (Pi.single i a))) p = _
    rw [TensorProduct.piScalarRight_symm_single, AlgebraTensorModule.lTensor_tmul]
    have hValue : Fintype.linearCombination K v (Pi.single i 1) = v i := by
      simp [Fintype.linearCombination_apply]
    rw [hValue]
    exact originalFiniteEtaleGeometricSplit_tmul_apply001 a (v i) p
  calc
    F c p = F (∑ i, Pi.single i (c i)) p :=
      congrArg (fun t => F t p) (Finset.univ_sum_single c).symm
    _ = ∑ i, F (Pi.single i (c i)) p := by rw [map_sum, Finset.sum_apply]
    _ = _ := Finset.sum_congr rfl (fun i _ => hSingle i (c i))

/-- The ACTUAL row kernel in extension-field coefficients is the actual
coefficient image of the tensorized ORIGINAL-K through-point kernel.
No row-kernel identification or splitting outcome is supplied. -/
theorem originalFiniteEtaleGeometricCoefficientEvaluation_kernel_eq_originalKernelCoefficientImage001
    {K A M : Type u} [Field K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Algebra.FiniteType K A]
    [Algebra.FormallyEtale K A] [IsSepClosed M]
    {m : ℕ} (v : Fin m → A) :
    LinearMap.ker (originalFiniteEtaleGeometricCoefficientEvaluation (K := K) (M := M) v) =
      (LinearMap.range (AlgebraTensorModule.lTensor M M
        (LinearMap.ker (Fintype.linearCombination K v)).subtype)).map
          (TensorProduct.piScalarRight K M M (Fin m)).toLinearMap := by
  let f := Fintype.linearCombination K v
  let E := TensorProduct.piScalarRight K M M (Fin m)
  let G := (originalFiniteEtaleGeometricSplit (K := K) (A := A) (M := M)).toLinearMap.comp
    (AlgebraTensorModule.lTensor M M f)
  ext c
  change E.symm c ∈ LinearMap.ker G ↔
    c ∈ (LinearMap.range (AlgebraTensorModule.lTensor M M (LinearMap.ker f).subtype)).map E.toLinearMap
  rw [Submodule.mem_map_equiv,
    originalFiniteEtale_allGeometricEvaluations_kernel_eq_tensorOriginalKernel001 f]

/-- A section in the actual geometric row kernel with a nonzero SAME jet
DERIVES ORIGINAL-K coefficients vanishing in the SAME A and retaining
that nonzero jet. This is genuine descent of nonvanishing, not descent
of one particular extension-field hyperplane. -/
theorem originalFiniteEtaleGeometricRowKernel_nonzeroJet_exists_originalCoefficients001
    {K A M V : Type u} [Field K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Algebra.FiniteType K A]
    [Algebra.FormallyEtale K A] [IsSepClosed M]
    [AddCommGroup V] [Module M V]
    {m : ℕ} (v : Fin m → A) (J : (Fin m → M) →ₗ[M] V)
    (hNonzero : ∃ c : Fin m → M,
      originalFiniteEtaleGeometricCoefficientEvaluation (K := K) (M := M) v c = 0 ∧ J c ≠ 0) :
    ∃ c : Fin m → K, (∑ i, c i • v i) = 0 ∧
      J (fun i => algebraMap K M (c i)) ≠ 0 := by
  let f := Fintype.linearCombination K v
  let E := TensorProduct.piScalarRight K M M (Fin m)
  let JT := J.comp E.toLinearMap
  obtain ⟨cM, hRows, hJet⟩ := hNonzero
  have hTensorNonzero : ∃ z : M ⊗[K] (Fin m → K),
      originalFiniteEtaleGeometricSplit (K := K) (A := A) (M := M)
        (AlgebraTensorModule.lTensor M M f z) = 0 ∧ JT z ≠ 0 := by
    refine ⟨E.symm cM, hRows, ?_⟩
    simpa only [JT, LinearMap.comp_apply, LinearEquiv.coe_coe, E.apply_symm_apply] using hJet
  obtain ⟨c, hc, hJc⟩ :=
    originalFiniteEtale_nonzeroGeometricKernelJet_exists_originalKernelSection001 f JT hTensorNonzero
  have hCoords : E ((1 : M) ⊗ₜ[K] c) = fun i => algebraMap K M (c i) := by
    ext i
    simp only [E, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Algebra.smul_def, mul_one]
  refine ⟨c, ?_, ?_⟩
  · simpa only [f, Fintype.linearCombination_apply] using hc
  · change J (E ((1 : M) ⊗ₜ[K] c)) ≠ 0 at hJc
    rw [hCoords] at hJc
    exact hJc

end PfaffianDescent.Coray
