import PfaffianDescent.CorayNativeSurfaceJetCoordinateSpanRank
import PfaffianDescent.CorayLinearTangentIncidence
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Finite geometry of the actual three conjugate image vectors. A
proved normalized native minor and a nonzero pair value exclude the bad
three-point span without presupposing a transverse original section. -/
noncomputable section
namespace PfaffianDescent.Coray
open Module TrivSqZeroExt
universe u
set_option autoImplicit false

private theorem nativeJetAnnihilator_dot_zero_on_span001
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

/-- The actual nonzero Q pair value excludes the second image vector
from the SAME native full-jet span that its annihilator contains. -/
theorem nativeSurfaceJetCoordinateSpan_pairValue_ne_zero_not_mem001
    {M : Type u} [Field M] {m : ℕ} (w : Fin m → SurfacePlaneJet M)
    (c B : Fin m → M) (hJet : (∑ i, c i • w i) = 0)
    (hPair : (∑ i, c i * B i) ≠ 0) :
    B ∉ nativeSurfaceJetCoordinateSpan w := by
  intro hB
  exact hPair (nativeJetAnnihilator_dot_zero_on_span001 c w hJet B hB)

/-- The literal normalized native minor constructs rank3 of the fulljet
span. If that span lay in the span of three point images, those spans
would be equal, forcing the second point into it and contradicting the
actual nonzero pair value. Lower three-point dimension is handled by the
same rank comparison, without a separate general-position premise. -/
theorem nativeSurfaceJetCoordinateSpan_not_le_threePointSpan_of_pairValue001
    {M : Type u} [Field M] {m : ℕ} (w : Fin m → SurfacePlaneJet M)
    (a i k : Fin m) (v : (SurfacePlaneJet M)ˣ) (ha : w a = (↑v : SurfacePlaneJet M))
    (hMinor :
      (w i * (↑(v⁻¹) : SurfacePlaneJet M)).snd 0 *
        (w k * (↑(v⁻¹) : SurfacePlaneJet M)).snd 1 -
      (w k * (↑(v⁻¹) : SurfacePlaneJet M)).snd 0 *
        (w i * (↑(v⁻¹) : SurfacePlaneJet M)).snd 1 ≠ 0)
    (c B C : Fin m → M) (hJet : (∑ i, c i • w i) = 0)
    (hPair : (∑ i, c i * B i) ≠ 0) :
    ¬ nativeSurfaceJetCoordinateSpan w ≤
      Submodule.span M (Set.range
        (Fin.cons (fun i => (w i).fst) (Fin.cons B (fun _ : Fin 1 => C)))) := by
  classical
  let rows : Fin 3 → Fin m → M :=
    Fin.cons (fun i => (w i).fst) (Fin.cons B (fun _ : Fin 1 => C))
  let U : Submodule M (Fin m → M) := Submodule.span M (Set.range rows)
  have hRank : finrank M (nativeSurfaceJetCoordinateSpan w) = 3 :=
    nativeSurfaceJetCoordinateSpan_finrank_three_of_normalizedMinor001 w a i k v ha hMinor
  have hDimU : finrank M U ≤ 3 := by
    change (Set.range rows).finrank M ≤ 3
    simpa only [Fintype.card_fin] using finrank_range_le_card (R := M) rows
  change ¬ nativeSurfaceJetCoordinateSpan w ≤ U
  intro hIncluded
  have hEqual : nativeSurfaceJetCoordinateSpan w = U :=
    Submodule.eq_of_le_of_finrank_le hIncluded (by rw [hRank]; exact hDimU)
  have hB : B ∈ U := Submodule.subset_span ⟨(1 : Fin 3), rfl⟩
  rw [← hEqual] at hB
  exact nativeSurfaceJetCoordinateSpan_pairValue_ne_zero_not_mem001 w c B hJet hPair hB

/-- The literal normalized native minor constructs rank3 of the fulljet
span. If that span lay in the span of three point images, those spans
would be equal, forcing the second point into it and contradicting the
actual nonzero pair value. Lower three-point dimension is handled by the
same rank comparison, without a separate general-position premise. -/
theorem nativeSurfaceJetCoordinateSpan_exists_hyperplane_threePointSpan001
    {M : Type u} [Field M] {m : ℕ} (w : Fin m → SurfacePlaneJet M)
    (a i k : Fin m) (v : (SurfacePlaneJet M)ˣ) (ha : w a = (↑v : SurfacePlaneJet M))
    (hMinor :
      (w i * (↑(v⁻¹) : SurfacePlaneJet M)).snd 0 *
        (w k * (↑(v⁻¹) : SurfacePlaneJet M)).snd 1 -
      (w k * (↑(v⁻¹) : SurfacePlaneJet M)).snd 0 *
        (w i * (↑(v⁻¹) : SurfacePlaneJet M)).snd 1 ≠ 0)
    (c B C : Fin m → M) (hJet : (∑ i, c i • w i) = 0)
    (hPair : (∑ i, c i * B i) ≠ 0) :
    ∃ phi : Module.Dual M (Fin m → M),
      Submodule.span M (Set.range
        (Fin.cons (fun i => (w i).fst) (Fin.cons B (fun _ : Fin 1 => C)))) ≤ LinearMap.ker phi ∧
      ¬ nativeSurfaceJetCoordinateSpan w ≤ LinearMap.ker phi := by
  have hNot := nativeSurfaceJetCoordinateSpan_not_le_threePointSpan_of_pairValue001
    w a i k v ha hMinor c B C hJet hPair
  exact (exists_hyperplane_through_span_not_tangent_iff _ _).mpr hNot

end PfaffianDescent.Coray
