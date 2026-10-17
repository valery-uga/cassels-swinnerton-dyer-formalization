import PfaffianDescent.CorayNativeSurfaceJetThreePointSeparation
import Mathlib.LinearAlgebra.Pi

/-! The actually constructed three-point hyperplane gives explicit
coefficients vanishing on those three ordinary rows, with nonzero native
fulljet value. This is finite geometry; original-K descent is separate. -/
noncomputable section
namespace PfaffianDescent.Coray
open Module TrivSqZeroExt
universe u
set_option autoImplicit false

private theorem coefficientSeparation_nativeJetAnnihilator_dot_zero_on_span001
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

private theorem coefficientSeparation_dual_apply_eq001
    {M : Type u} [Field M] {m : ℕ} (phi : Module.Dual M (Fin m → M))
    (B : Fin m → M) :
    phi B = ∑ i, phi (Pi.single i 1) * B i := by
  classical
  have hSingle (i : Fin m) : Pi.single i (B i) = B i • Pi.single i (1 : M) := by
    ext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [Pi.single_apply, hk, Ne.symm hk]
  calc
    phi B = phi (∑ i, Pi.single i (B i)) :=
      congrArg phi (Finset.univ_sum_single B).symm
    _ = ∑ i, phi (Pi.single i (B i)) := by rw [map_sum]
    _ = ∑ i, phi (Pi.single i 1) * B i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hSingle, map_smul]
      exact mul_comm _ _

/-- Extraction from the SAME actual hyperplane: its coordinate
coefficients annihilate all three actual ordinary rows and do not
annihilate the native fulljet. No extension-field section is presumed. -/
theorem nativeSurfaceJetThreePoint_hyperplane_exists_coefficients001
    {M : Type u} [Field M] {m : ℕ} (w : Fin m → SurfacePlaneJet M)
    (B C : Fin m → M) (phi : Module.Dual M (Fin m → M))
    (hRows : Submodule.span M (Set.range
      (Fin.cons (fun i => (w i).fst) (Fin.cons B (fun _ : Fin 1 => C)))) ≤ LinearMap.ker phi)
    (hNot : ¬ nativeSurfaceJetCoordinateSpan w ≤ LinearMap.ker phi) :
    ∃ c : Fin m → M,
      (∑ i, c i * (w i).fst) = 0 ∧
      (∑ i, c i * B i) = 0 ∧
      (∑ i, c i * C i) = 0 ∧
      (∑ i, c i • w i) ≠ 0 := by
  classical
  let c : Fin m → M := fun i => phi (Pi.single i 1)
  have hEval (V : Fin m → M) : phi V = ∑ i, c i * V i :=
    coefficientSeparation_dual_apply_eq001 phi V
  let rows : Fin 3 → (Fin m → M) :=
    Fin.cons (fun i => (w i).fst) (Fin.cons B (fun _ : Fin 1 => C))
  have hRowsTyped : Submodule.span M (Set.range rows) ≤ LinearMap.ker phi := hRows
  have hRow (r : Fin 3) : phi (rows r) = 0 := by
    have hMember : rows r ∈ Submodule.span M (Set.range rows) :=
      Submodule.subset_span ⟨r, rfl⟩
    have hKernel := hRowsTyped hMember
    change phi (rows r) = 0 at hKernel
    exact hKernel
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · exact (hEval _).symm.trans (hRow 0)
  · exact (hEval _).symm.trans (hRow 1)
  · exact (hEval _).symm.trans (hRow 2)
  · intro hJet
    apply hNot
    intro V hV
    change phi V = 0
    exact (hEval V).trans
      (coefficientSeparation_nativeJetAnnihilator_dot_zero_on_span001 c w hJet V hV)

/-- Literal normalized minor and nonzero pair value construct actual
three-row vanishing coefficients with nonzero native jet value. This
consumes the finite rank argument and constructs the hyperplane, rather
than supplying its existence as a premise. -/
theorem nativeSurfaceJetThreePoint_exists_coefficients_of_pairValue001
    {M : Type u} [Field M] {m : ℕ} (w : Fin m → SurfacePlaneJet M)
    (a i k : Fin m) (v : (SurfacePlaneJet M)ˣ) (ha : w a = (↑v : SurfacePlaneJet M))
    (hMinor :
      (w i * (↑(v⁻¹) : SurfacePlaneJet M)).snd 0 *
        (w k * (↑(v⁻¹) : SurfacePlaneJet M)).snd 1 -
      (w k * (↑(v⁻¹) : SurfacePlaneJet M)).snd 0 *
        (w i * (↑(v⁻¹) : SurfacePlaneJet M)).snd 1 ≠ 0)
    (c B C : Fin m → M) (hJet : (∑ i, c i • w i) = 0)
    (hPair : (∑ i, c i * B i) ≠ 0) :
    ∃ d : Fin m → M,
      (∑ i, d i * (w i).fst) = 0 ∧
      (∑ i, d i * B i) = 0 ∧
      (∑ i, d i * C i) = 0 ∧
      (∑ i, d i • w i) ≠ 0 := by
  obtain ⟨phi, hRows, hNot⟩ :=
    nativeSurfaceJetCoordinateSpan_exists_hyperplane_threePointSpan001
      w a i k v ha hMinor c B C hJet hPair
  exact nativeSurfaceJetThreePoint_hyperplane_exists_coefficients001 w B C phi hRows hNot

end PfaffianDescent.Coray
