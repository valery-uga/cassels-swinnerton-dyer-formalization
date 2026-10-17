import PfaffianDescent.CorayOriginalJetPairSpecialization
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Fixed-data whole badpair localization. The actual line equation and
native tangent argument can consume one constructed Q,u,F without
making unrelated existential choices. All maps retain the original
K-algebra triangle, including the WHOLE quotient and localization. -/
noncomputable section
namespace PfaffianDescent.Coray
open Module TrivSqZeroExt
open scoped TensorProduct
universe u
set_option autoImplicit false

private theorem fixedPair_nativeJetAnnihilator_dot_zero_on_span001
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

/-- The actual original-K point killing F, with actual nonzero rho,
constructs a K-algebra point of its WHOLE principal quotient localization. -/
theorem algHom_exists_point_principalQuotient_away001
    {K T M : Type u} [Field K] [CommRing T] [Field M]
    [Algebra K T] [Algebra K M] (f : T →ₐ[K] M)
    (F rho : T) (hF : f F = 0) (hRho : f rho ≠ 0) :
    let B := T ⧸ Ideal.span ({F} : Set T)
    let mk : T →+* B := Ideal.Quotient.mk (Ideal.span ({F} : Set T))
    ∃ ell : Localization.Away (mk rho) →ₐ[K] M,
      ell.comp ((IsScalarTower.toAlgHom K B (Localization.Away (mk rho))).comp
        (Ideal.Quotient.mkₐ K (Ideal.span ({F} : Set T)))) = f := by
  let B := T ⧸ Ideal.span ({F} : Set T)
  let mk : T →+* B := Ideal.Quotient.mk (Ideal.span ({F} : Set T))
  have hSpan : Ideal.span ({F} : Set T) ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    intro r hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    exact hF
  let psi : B →ₐ[K] M := Ideal.Quotient.liftₐ (Ideal.span ({F} : Set T)) f (fun r hr => hSpan hr)
  have hPsi : psi.comp (Ideal.Quotient.mkₐ K (Ideal.span ({F} : Set T))) = f :=
    Ideal.Quotient.liftₐ_comp _ _ _
  have hValue : psi (mk rho) = f rho := AlgHom.congr_fun hPsi rho
  have hUnit : IsUnit (psi (mk rho)) := isUnit_iff_ne_zero.mpr (by rw [hValue]; exact hRho)
  let ell : Localization.Away (mk rho) →ₐ[K] M := IsLocalization.Away.liftAlgHom (mk rho) hUnit
  refine ⟨ell, ?_⟩
  apply AlgHom.ext
  intro t
  change ell (algebraMap B (Localization.Away (mk rho)) (mk t)) = f t
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact AlgHom.congr_fun hPsi t

/-- One FIXED literal Q and boundary factor F: a boundary failure or
second-point membership in the actual first native fulljet span produces
an actual original-K point of the SAME whole quotient Away rho. The
weighted jet identity is the literal structural relation proved by the
natural original producer, not a chosen good-line or section outcome. -/
theorem nativeFixedPairBoundary_badPair_exists_localizationAlgHom001
    {K R M : Type u} [Field K] [CommRing R] [Field M]
    [Algebra K R] [Algebra K M] {m : ℕ} (A f : Fin m → R)
    (u : R) (h h' : R →ₐ[K] M) (w : Fin m → SurfacePlaneJet M)
    (hNative : h u ≠ 0 → (∑ i, h (A i) • w i) = 0)
    (rho : R ⊗[K] R)
    (hRho : Algebra.TensorProduct.lift h h' (fun _ _ => Commute.all _ _) rho ≠ 0)
    (hBad : h u = 0 ∨ h' u = 0 ∨ (fun i => h' (f i)) ∈ nativeSurfaceJetCoordinateSpan w) :
    let Q : R ⊗[K] R := ∑ i, A i ⊗ₜ[K] f i
    let F : R ⊗[K] R := Q * (u ⊗ₜ[K] (1 : R)) * ((1 : R) ⊗ₜ[K] u)
    let B := (R ⊗[K] R) ⧸ Ideal.span ({F} : Set (R ⊗[K] R))
    let mk : R ⊗[K] R →+* B := Ideal.Quotient.mk (Ideal.span ({F} : Set (R ⊗[K] R)))
    ∃ ell : Localization.Away (mk rho) →ₐ[K] M,
      ell.comp ((IsScalarTower.toAlgHom K B (Localization.Away (mk rho))).comp
        (Ideal.Quotient.mkₐ K (Ideal.span ({F} : Set (R ⊗[K] R))))) =
        Algebra.TensorProduct.lift h h' (fun _ _ => Commute.all _ _) := by
  classical
  let Q : R ⊗[K] R := ∑ i, A i ⊗ₜ[K] f i
  let F : R ⊗[K] R := Q * (u ⊗ₜ[K] (1 : R)) * ((1 : R) ⊗ₜ[K] u)
  let pair : R ⊗[K] R →ₐ[K] M := Algebra.TensorProduct.lift h h' (fun _ _ => Commute.all _ _)
  have hPairQ : pair Q = ∑ i, h (A i) * h' (f i) := by
    simp only [Q, pair, map_sum, Algebra.TensorProduct.lift_tmul]
  have hPairF : pair F = pair Q * h u * h' u := by
    simp only [F, pair, map_mul, Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul]
  have hZero : pair F = 0 := by
    rcases hBad with hBoundary | hBoundary | hTangent
    · rw [hPairF, hBoundary, mul_zero, zero_mul]
    · rw [hPairF, hBoundary, mul_zero]
    · by_cases hBoundary : h u = 0
      · rw [hPairF, hBoundary, mul_zero, zero_mul]
      · have hDot := fixedPair_nativeJetAnnihilator_dot_zero_on_span001
          (fun i => h (A i)) w (hNative hBoundary) (fun i => h' (f i)) hTangent
        have hZeroQ : pair Q = 0 := hPairQ.trans hDot
        rw [hPairF, hZeroQ, zero_mul, zero_mul]
  exact algHom_exists_point_principalQuotient_away001 pair F rho hZero hRho

end PfaffianDescent.Coray
