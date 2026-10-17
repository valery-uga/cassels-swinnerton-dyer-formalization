import PfaffianDescent.CorayOriginalJetPairSpecialization
import PfaffianDescent.CubicFullJetTangentFrameTransport

/-! Whole native full-jet coordinate spans are independent of a genuine
invertible tangent-frame change, hence of a chosen nonzero native pivot. -/
noncomputable section
namespace PfaffianDescent.Coray
open Module TrivSqZeroExt MvPolynomial
universe u
set_option autoImplicit false

private theorem nativeSurfaceJetCoordinateSpan_frameMap_le001
    {M : Type u} [Field M] {m : ℕ} (w : Fin m → SurfacePlaneJet M)
    (T : (Fin 2 → M) →ₗ[M] (Fin 2 → M)) :
    nativeSurfaceJetCoordinateSpan (fun i => TrivSqZeroExt.map T (w i)) ≤
      nativeSurfaceJetCoordinateSpan w := by
  classical
  have hResidue : (fun i => (w i).fst) ∈ nativeSurfaceJetCoordinateSpan w :=
    Submodule.subset_span ⟨(0 : Fin 3), rfl⟩
  have hDirection (r : Fin 2) : (fun i => (w i).snd r) ∈ nativeSurfaceJetCoordinateSpan w :=
    Submodule.subset_span ⟨r.succ, rfl⟩
  have hVector (v : Fin 2 → M) :
      v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
    funext r
    fin_cases r <;> simp [Pi.single_apply]
  have hT (v : Fin 2 → M) (r : Fin 2) : T v r =
      (T (Pi.single 0 1) r) * v 0 + (T (Pi.single 1 1) r) * v 1 := by
    calc
      T v r = T (v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1) r :=
        congrArg (fun z => T z r) (hVector v)
      _ = _ := by simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hSnd (r : Fin 2) : (fun i => (TrivSqZeroExt.map T (w i)).snd r) =
      (T (Pi.single 0 1) r) • (fun i => (w i).snd 0) +
      (T (Pi.single 1 1) r) • (fun i => (w i).snd 1) := by
    funext i
    rw [TrivSqZeroExt.snd_map]
    change T (w i).snd r = _
    exact hT (w i).snd r
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  induction r using Fin.cases with
  | zero =>
    change (fun i => (TrivSqZeroExt.map T (w i)).fst) ∈ nativeSurfaceJetCoordinateSpan w
    simpa only [TrivSqZeroExt.fst_map] using hResidue
  | succ r =>
    change (fun i => (TrivSqZeroExt.map T (w i)).snd r) ∈ nativeSurfaceJetCoordinateSpan w
    rw [hSnd r]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hDirection 0))
      (Submodule.smul_mem _ _ (hDirection 1))

/-- A bijective native tangent-frame map leaves the whole residue-plus-
direction coordinate span unchanged, with its square-zero data retained. -/
theorem nativeSurfaceJetCoordinateSpan_bijectiveFrame_eq001
    {M : Type u} [Field M] {m : ℕ} (w : Fin m → SurfacePlaneJet M)
    (T : (Fin 2 → M) →ₗ[M] (Fin 2 → M)) (hT : Function.Bijective T) :
    nativeSurfaceJetCoordinateSpan (fun i => TrivSqZeroExt.map T (w i)) =
      nativeSurfaceJetCoordinateSpan w := by
  let e : (Fin 2 → M) ≃ₗ[M] (Fin 2 → M) := LinearEquiv.ofBijective T hT
  have hForward := nativeSurfaceJetCoordinateSpan_frameMap_le001 w T
  have hBackward := nativeSurfaceJetCoordinateSpan_frameMap_le001
    (fun i => TrivSqZeroExt.map T (w i)) e.symm.toLinearMap
  have hCancel : (fun i => TrivSqZeroExt.map e.symm.toLinearMap
      (TrivSqZeroExt.map T (w i))) = w := by
    funext i
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_map]
    · rw [TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_map]
      change e.symm (e (w i).snd) = (w i).snd
      exact e.symm_apply_apply (w i).snd
  rw [hCancel] at hBackward
  exact le_antisymm hForward hBackward

/-- Two internally constructed NONZERO native Jacobian pivots give the
SAME polynomial full-jet coordinate span. Their equality is not assumed;
the existing actual gradient-frame theorem constructs their bijective
frame change. This applies to the SAME original-K basis polynomials. -/
theorem nativeSurfaceJetCoordinateSpan_polynomialJets_eq_of_nonzeroPivots001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (j : Fin 4) (z g : Fin 4 → M) (pivot pivot' : Fin 3)
    (hpivot : g (j.succAbove pivot) ≠ 0) (hpivot' : g (j.succAbove pivot') ≠ 0)
    {m : ℕ} (q : Fin m → MvPolynomial (Fin 4) K) :
    let v : Fin 2 → Fin 4 → M := fun r i =>
      PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j (fun t => g (j.succAbove t)) pivot i r
    let v' : Fin 2 → Fin 4 → M := fun r i =>
      PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j (fun t => g (j.succAbove t)) pivot' i r
    nativeSurfaceJetCoordinateSpan (fun i => (q i).eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v)) =
    nativeSurfaceJetCoordinateSpan (fun i => (q i).eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v')) := by
  let row := PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j (fun t => g (j.succAbove t)) pivot
  let row' := PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j (fun t => g (j.succAbove t)) pivot'
  obtain ⟨T, hT, hRow⟩ := PfaffianDescent.cubicNormalizedTangentRow_exists_frameMap
    j g pivot hpivot row'
    (PfaffianDescent.cubicClosedPointSerreSurfaceJets_row_diag j _ pivot')
    (PfaffianDescent.cubicClosedPointSerreSurfaceJets_row_gradient_zero j g pivot' hpivot')
    (PfaffianDescent.cubicClosedPointSerreSurfaceJets_row_surjective j _ pivot')
  let v : Fin 2 → Fin 4 → M := fun r i => row i r
  let v' : Fin 2 → Fin 4 → M := fun r i => row' i r
  let phi : SurfacePlaneJet M →ₐ[K] SurfacePlaneJet M :=
    (TrivSqZeroExt.map T).restrictScalars K
  have hPhi (w : SurfacePlaneJet M) : phi w = TrivSqZeroExt.map T w := rfl
  have hCoordinates : (fun i => phi (surfacePlaneJetCoordinates z v i)) =
      surfacePlaneJetCoordinates z v' := by
    funext i
    rw [hPhi]
    apply TrivSqZeroExt.ext
    · rw [TrivSqZeroExt.fst_map]
      rfl
    · rw [TrivSqZeroExt.snd_map]
      simpa only [surfacePlaneJetCoordinates, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, v, v', row] using (hRow i).symm
  have hCoeff : phi.toRingHom.comp (algebraMap K (SurfacePlaneJet M)) =
      algebraMap K (SurfacePlaneJet M) := RingHom.ext phi.commutes
  have hPolynomial (i : Fin m) :
      (q i).eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v') =
      TrivSqZeroExt.map T ((q i).eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates z v)) := by
    have h := MvPolynomial.hom_eval₂ (q i) (algebraMap K (SurfacePlaneJet M))
      phi.toRingHom (surfacePlaneJetCoordinates z v)
    change phi ((q i).eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v)) =
      (q i).eval₂ (phi.toRingHom.comp (algebraMap K (SurfacePlaneJet M)))
        (fun j => phi (surfacePlaneJetCoordinates z v j)) at h
    rw [hCoeff, hCoordinates, hPhi] at h
    exact h.symm
  have hFamily : (fun i => (q i).eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v')) =
      (fun i => TrivSqZeroExt.map T ((q i).eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates z v))) := funext hPolynomial
  change nativeSurfaceJetCoordinateSpan (fun i => (q i).eval₂ (algebraMap K (SurfacePlaneJet M))
    (surfacePlaneJetCoordinates z v)) =
    nativeSurfaceJetCoordinateSpan (fun i => (q i).eval₂ (algebraMap K (SurfacePlaneJet M))
    (surfacePlaneJetCoordinates z v'))
  rw [hFamily, nativeSurfaceJetCoordinateSpan_bijectiveFrame_eq001 _ T hT]

end PfaffianDescent.Coray
