import PfaffianDescent.CorayOriginalBadPairLineEquationSpecialization
import PfaffianDescent.CorayOriginalJetPairSpecialization

/-! Pointwise exclusion from ONE whole bad-pair kernel equation. The
actual original pair coordinates, quotient, native scalar structure and
SAME selected graph matrix are preserved through the proof. -/
noncomputable section
namespace PfaffianDescent.Coray
open Module TrivSqZeroExt MvPolynomial
open scoped TensorProduct
universe u
set_option autoImplicit false

private theorem jointGuard_nativeJetAnnihilator_dot_zero_on_span001
    {M : Type u} [Field M] {m : ℕ} (c : Fin m → M) (w : Fin m → SurfacePlaneJet M)
    (hJet : (∑ i, c i • w i) = 0) :
    ∀ B : Fin m → M, B ∈ nativeSurfaceJetCoordinateSpan w →
      (∑ i, c i * B i) = 0 := by
  classical
  let phi : (Fin m → M) →ₗ[M] M := Fintype.linearCombination M c
  have hResidue : phi (fun i => (w i).fst) = 0 := by
    have h := congrArg TrivSqZeroExt.fst hJet
    simpa only [phi, Fintype.linearCombination_apply, TrivSqZeroExt.fst_sum,
      TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_zero, smul_eq_mul, mul_comm] using h
  have hDirection (r : Fin 2) : phi (fun i => (w i).snd r) = 0 := by
    have h := congrArg (fun t : SurfacePlaneJet M => t.snd r) hJet
    simpa only [phi, Fintype.linearCombination_apply, TrivSqZeroExt.snd_sum,
      TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_zero, Finset.sum_apply,
      Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_comm] using h
  have hSpan : nativeSurfaceJetCoordinateSpan w ≤ LinearMap.ker phi := by
    apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    induction r using Fin.cases with
    | zero => exact hResidue
    | succ r => exact hDirection r
  intro B hB
  have h := hSpan hB
  change phi B = 0 at h
  simpa only [phi, Fintype.linearCombination_apply, smul_eq_mul, mul_comm] using h

/-- A full kernel equation for ONE fixed F, nonzero on the SAME
selected graph, rules out every boundary or native-tangent bad pair of
normalized distinct original points on that graph. -/
theorem nativeFixedWholePairKernelEquation_nonzero_on_sameGraph_excludes_badPair001
    {K R M : Type u} [Field K] [CommRing R] [Field M]
    [Algebra K R] [Algebra K M] {m : ℕ}
    (A f : Fin m → R) (u : R)
    (xy : ((Fin 2 → R ⊗[K] R) × (Fin 2 → R ⊗[K] R)) ×
      ((Fin 2 → R ⊗[K] R) × (Fin 2 → R ⊗[K] R)))
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2))
    (bad : GrassmannianChartRing K 2 2)
    (hKernel :
      let Q : R ⊗[K] R := ∑ i, A i ⊗ₜ[K] f i
      let F := Q * (u ⊗ₜ[K] (1 : R)) * ((1 : R) ⊗ₜ[K] u)
      let B := (R ⊗[K] R) ⧸ Ideal.span ({F} : Set (R ⊗[K] R))
      let mk : R ⊗[K] R →+* B := Ideal.Quotient.mk (Ideal.span ({F} : Set (R ⊗[K] R)))
      let x := graphCoefficientMap mk xy.1
      let y := graphCoefficientMap mk xy.2
      let d := originalPairGrassmannMinor rho x y
      let C := Localization.Away d
      let xC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho x)
      let yC := graphCoefficientMap (algebraMap B C) (graphCoordinatePermutation B rho y)
      let N := originalPairMinorGraphMatrix xC yC (IsLocalization.Away.invSelf d)
      (MvPolynomial.aeval (R := K) (fun ij : Fin 2 × Fin 2 => N ij.1 ij.2)) bad = 0)
    (h h' : R →ₐ[K] M) (w : Fin m → SurfacePlaneJet M)
    (hNative : h u ≠ 0 → (∑ i, h (A i) • w i) = 0)
    (T : Matrix (Fin 2) (Fin 2) M)
    (ell : ((Fin 2 → M) × (Fin 2 → M)) →ₗ[M] M)
    (hx : graphCoefficientMap (Algebra.TensorProduct.lift h h' (fun _ _ => Commute.all _ _)).toRingHom xy.1 ∈
      grassmannianChartSubmodule M rho T)
    (hy : graphCoefficientMap (Algebra.TensorProduct.lift h h' (fun _ _ => Commute.all _ _)).toRingHom xy.2 ∈
      grassmannianChartSubmodule M rho T)
    (hEllx : ell (graphCoefficientMap (Algebra.TensorProduct.lift h h' (fun _ _ => Commute.all _ _)).toRingHom xy.1) = 1)
    (hElly : ell (graphCoefficientMap (Algebra.TensorProduct.lift h h' (fun _ _ => Commute.all _ _)).toRingHom xy.2) = 1)
    (hne : graphCoefficientMap (Algebra.TensorProduct.lift h h' (fun _ _ => Commute.all _ _)).toRingHom xy.1 ≠
      graphCoefficientMap (Algebra.TensorProduct.lift h h' (fun _ _ => Commute.all _ _)).toRingHom xy.2)
    (hBadValue : (MvPolynomial.aeval (R := K) (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2)) bad ≠ 0) :
    h u ≠ 0 ∧ h' u ≠ 0 ∧ (fun i => h' (f i)) ∉ nativeSurfaceJetCoordinateSpan w ∧
      Algebra.TensorProduct.lift h h' (fun _ _ => Commute.all _ _) (∑ i, A i ⊗ₜ[K] f i) ≠ 0 := by
  classical
  let pair : R ⊗[K] R →ₐ[K] M := Algebra.TensorProduct.lift h h' (fun _ _ => Commute.all _ _)
  let Q : R ⊗[K] R := ∑ i, A i ⊗ₜ[K] f i
  let F : R ⊗[K] R := Q * (u ⊗ₜ[K] (1 : R)) * ((1 : R) ⊗ₜ[K] u)
  have hNoBad : ¬ (h u = 0 ∨ h' u = 0 ∨
      (fun i => h' (f i)) ∈ nativeSurfaceJetCoordinateSpan w ∨ pair Q = 0) := by
    intro hBad
    have hPairQ : pair Q = ∑ i, h (A i) * h' (f i) := by
      simp only [Q, pair, map_sum, Algebra.TensorProduct.lift_tmul]
    have hPairF : pair F = pair Q * h u * h' u := by
      simp only [F, pair, map_mul, Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul]
    have hZero : pair F = 0 := by
      rcases hBad with hBoundary | hBoundary | hTangent | hEquation
      · rw [hPairF, hBoundary, mul_zero, zero_mul]
      · rw [hPairF, hBoundary, mul_zero]
      · by_cases hBoundary : h u = 0
        · rw [hPairF, hBoundary, mul_zero, zero_mul]
        · have hDot := jointGuard_nativeJetAnnihilator_dot_zero_on_span001
            (fun i => h (A i)) w (hNative hBoundary) (fun i => h' (f i)) hTangent
          have hZeroQ : pair Q = 0 := hPairQ.trans hDot
          rw [hPairF, hZeroQ, zero_mul, zero_mul]
      · rw [hPairF, hEquation, zero_mul, zero_mul]
    let B := (R ⊗[K] R) ⧸ Ideal.span ({F} : Set (R ⊗[K] R))
    let mk : R ⊗[K] R →+* B := Ideal.Quotient.mk (Ideal.span ({F} : Set (R ⊗[K] R)))
    have hSpan : Ideal.span ({F} : Set (R ⊗[K] R)) ≤ RingHom.ker pair.toRingHom := by
      apply Ideal.span_le.mpr
      intro r hr
      obtain rfl := Set.mem_singleton_iff.mp hr
      exact hZero
    let psi : B →ₐ[K] M := Ideal.Quotient.liftₐ _ pair (fun r hr => hSpan hr)
    have hPsi : psi.toRingHom.comp mk = pair.toRingHom := Ideal.Quotient.lift_comp_mk _ _ _
    have hMap (V : (Fin 2 → R ⊗[K] R) × (Fin 2 → R ⊗[K] R)) :
        graphCoefficientMap psi.toRingHom (graphCoefficientMap mk V) = graphCoefficientMap pair.toRingHom V := by
      change graphCoefficientMap (psi.toRingHom.comp mk) V = _
      rw [hPsi]
    have hVanishing := originalPairMinorOpen_fullKernelEquation_vanishes_on_sameGraph001
      rho (graphCoefficientMap mk xy.1) (graphCoefficientMap mk xy.2) psi T ell
      (by rw [hMap]; exact hx) (by rw [hMap]; exact hy)
      (by rw [hMap]; exact hEllx) (by rw [hMap]; exact hElly)
      (by rw [hMap, hMap]; exact hne) bad hKernel
    exact hBadValue hVanishing
  exact ⟨fun hz => hNoBad (Or.inl hz), fun hz => hNoBad (Or.inr (Or.inl hz)),
    fun hT => hNoBad (Or.inr (Or.inr (Or.inl hT))),
    fun hQ => hNoBad (Or.inr (Or.inr (Or.inr hQ)))⟩

end PfaffianDescent.Coray
