import PfaffianDescent.CorayOriginalJetPairSpecialization
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Exact full-jet coordinate span under unit normalization. A literal
normalized native 2x2 tangent minor constructs its rank-three span. -/
noncomputable section
namespace PfaffianDescent.Coray
open Module TrivSqZeroExt
universe u
set_option autoImplicit false

private theorem nativeSurfaceJetCoordinateSpan_mul_le001
    {M : Type u} [Field M] {m : ℕ} (w : Fin m → SurfacePlaneJet M)
    (v : SurfacePlaneJet M) :
    nativeSurfaceJetCoordinateSpan (fun i => w i * v) ≤ nativeSurfaceJetCoordinateSpan w := by
  classical
  have hResidue : (fun i => (w i).fst) ∈ nativeSurfaceJetCoordinateSpan w :=
    Submodule.subset_span ⟨(0 : Fin 3), rfl⟩
  have hDirection (r : Fin 2) : (fun i => (w i).snd r) ∈ nativeSurfaceJetCoordinateSpan w :=
    Submodule.subset_span ⟨r.succ, rfl⟩
  have hFst : (fun i => (w i * v).fst) = v.fst • (fun i => (w i).fst) := by
    funext i
    change (w i).fst * v.fst = v.fst * (w i).fst
    exact mul_comm _ _
  have hSnd (r : Fin 2) : (fun i => (w i * v).snd r) =
      v.fst • (fun i => (w i).snd r) + v.snd r • (fun i => (w i).fst) := by
    funext i
    change (w i).fst * v.snd r + (w i).snd r * v.fst =
      v.fst * (w i).snd r + v.snd r * (w i).fst
    ring
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  induction r using Fin.cases with
  | zero =>
    change (fun i => (w i * v).fst) ∈ nativeSurfaceJetCoordinateSpan w
    rw [hFst]
    exact Submodule.smul_mem _ _ hResidue
  | succ r =>
    change (fun i => (w i * v).snd r) ∈ nativeSurfaceJetCoordinateSpan w
    rw [hSnd r]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hDirection r))
      (Submodule.smul_mem _ _ hResidue)

/-- Multiplication by a whole-jet unit preserves the actual coordinate
span, including its residue and nilpotent directional vectors. -/
theorem nativeSurfaceJetCoordinateSpan_unitNormalization_eq001
    {M : Type u} [Field M] {m : ℕ} (w : Fin m → SurfacePlaneJet M)
    (v : (SurfacePlaneJet M)ˣ) :
    nativeSurfaceJetCoordinateSpan (fun i => w i * (↑(v⁻¹) : SurfacePlaneJet M)) =
      nativeSurfaceJetCoordinateSpan w := by
  have hForward := nativeSurfaceJetCoordinateSpan_mul_le001 w (↑(v⁻¹) : SurfacePlaneJet M)
  have hBackward := nativeSurfaceJetCoordinateSpan_mul_le001
    (fun i => w i * (↑(v⁻¹) : SurfacePlaneJet M)) (↑v : SurfacePlaneJet M)
  have hCancel : (fun i => (w i * (↑(v⁻¹) : SurfacePlaneJet M)) * (↑v : SurfacePlaneJet M)) = w := by
    funext i
    simp only [mul_assoc, Units.inv_mul, mul_one]
  rw [hCancel] at hBackward
  exact le_antisymm hForward hBackward

private theorem nativeJetRows_linearIndependent_of_minor001
    {M : Type u} [Field M] {m : ℕ} (V : Fin 3 → Fin m → M) (a i k : Fin m)
    (h0 : V 0 a = 1) (h1 : V 1 a = 0) (h2 : V 2 a = 0)
    (hMinor : V 1 i * V 2 k - V 1 k * V 2 i ≠ 0) :
    LinearIndependent M V := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hSum
  have hCoordinate (r : Fin m) : (∑ t, c t * V t r) = 0 := by
    have h := congrArg (fun v : Fin m → M => v r) hSum
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] using h
  have hc0 : c 0 = 0 := by
    have h := hCoordinate a
    simpa only [Fin.sum_univ_three, h0, h1, h2, mul_one, mul_zero, add_zero] using h
  have hi : c 1 * V 1 i + c 2 * V 2 i = 0 := by
    simpa only [Fin.sum_univ_three, hc0, zero_mul, zero_add] using hCoordinate i
  have hk : c 1 * V 1 k + c 2 * V 2 k = 0 := by
    simpa only [Fin.sum_univ_three, hc0, zero_mul, zero_add] using hCoordinate k
  have hc1Product : c 1 * (V 1 i * V 2 k - V 1 k * V 2 i) = 0 := by
    calc
      _ = V 2 k * (c 1 * V 1 i + c 2 * V 2 i) -
          V 2 i * (c 1 * V 1 k + c 2 * V 2 k) := by ring
      _ = 0 := by rw [hi, hk]; ring
  have hc1 : c 1 = 0 := (mul_eq_zero.mp hc1Product).resolve_right hMinor
  have hc2Product : c 2 * (V 1 i * V 2 k - V 1 k * V 2 i) = 0 := by
    calc
      _ = V 1 i * (c 1 * V 1 k + c 2 * V 2 k) -
          V 1 k * (c 1 * V 1 i + c 2 * V 2 i) := by ring
      _ = 0 := by rw [hi, hk]; ring
  have hc2 : c 2 = 0 := (mul_eq_zero.mp hc2Product).resolve_right hMinor
  intro t
  fin_cases t
  · exact hc0
  · exact hc1
  · exact hc2

/-- The literal normalized tangent minor constructs a three-dimensional
whole-jet coordinate span. The pivot and original normalized maps may be
chosen by their actual producer; no rank-three certificate is supplied. -/
theorem nativeSurfaceJetCoordinateSpan_finrank_three_of_normalizedMinor001
    {M : Type u} [Field M] {m : ℕ} (w : Fin m → SurfacePlaneJet M)
    (a i k : Fin m) (v : (SurfacePlaneJet M)ˣ) (ha : w a = (↑v : SurfacePlaneJet M))
    (hMinor :
      (w i * (↑(v⁻¹) : SurfacePlaneJet M)).snd 0 *
        (w k * (↑(v⁻¹) : SurfacePlaneJet M)).snd 1 -
      (w k * (↑(v⁻¹) : SurfacePlaneJet M)).snd 0 *
        (w i * (↑(v⁻¹) : SurfacePlaneJet M)).snd 1 ≠ 0) :
    finrank M (nativeSurfaceJetCoordinateSpan w) = 3 := by
  let wn : Fin m → SurfacePlaneJet M := fun t => w t * (↑(v⁻¹) : SurfacePlaneJet M)
  have hAnchor : wn a = 1 := by
    change w a * (↑(v⁻¹) : SurfacePlaneJet M) = 1
    rw [ha, Units.mul_inv]
  let V : Fin 3 → Fin m → M :=
    Fin.cons (fun t => (wn t).fst) (fun r : Fin 2 => fun t => (wn t).snd r)
  have h0 : V 0 a = 1 := by
    change (wn a).fst = 1
    rw [hAnchor, TrivSqZeroExt.fst_one]
  have h1 : V 1 a = 0 := by
    change (wn a).snd 0 = 0
    rw [hAnchor, TrivSqZeroExt.snd_one, Pi.zero_apply]
  have h2 : V 2 a = 0 := by
    change (wn a).snd 1 = 0
    rw [hAnchor, TrivSqZeroExt.snd_one, Pi.zero_apply]
  have hLI : LinearIndependent M V := nativeJetRows_linearIndependent_of_minor001 V a i k h0 h1 h2 hMinor
  have hRank : finrank M (nativeSurfaceJetCoordinateSpan wn) = 3 := by
    change finrank M (Submodule.span M (Set.range V)) = 3
    simpa only [Fintype.card_fin] using finrank_span_eq_card hLI
  change finrank M (nativeSurfaceJetCoordinateSpan
    (fun t => w t * (↑(v⁻¹) : SurfacePlaneJet M))) = 3 at hRank
  rw [nativeSurfaceJetCoordinateSpan_unitNormalization_eq001 w v] at hRank
  exact hRank

end PfaffianDescent.Coray
