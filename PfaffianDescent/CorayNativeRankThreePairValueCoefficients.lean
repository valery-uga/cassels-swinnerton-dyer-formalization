import PfaffianDescent.CorayNativeThreePointCoefficientSeparation
import PfaffianDescent.CorayLinearTangentIncidence

/-! A bounded finite proof cut: the rank genuinely obtained from the
uniform original native minor/frame dictionary, and the actual nonzero
pair value, construct the three-row nonzero native-jet coefficients. -/
noncomputable section
namespace PfaffianDescent.Coray
open Module TrivSqZeroExt
universe u
set_option autoImplicit false

private theorem rankThreePairValue_not_le_threePointSpan001
    {M : Type u} [Field M] {m : ℕ} (w : Fin m → SurfacePlaneJet M)
    (hRank : finrank M (nativeSurfaceJetCoordinateSpan w) = 3)
    (c B C : Fin m → M) (hJet : (∑ t, c t • w t) = 0)
    (hPair : (∑ t, c t * B t) ≠ 0) :
    ¬ nativeSurfaceJetCoordinateSpan w ≤ Submodule.span M (Set.range
      (Fin.cons (fun t => (w t).fst) (Fin.cons B (fun _ : Fin 1 => C)))) := by
  classical
  let rows : Fin 3 → Fin m → M :=
    Fin.cons (fun t => (w t).fst) (Fin.cons B (fun _ : Fin 1 => C))
  let U : Submodule M (Fin m → M) := Submodule.span M (Set.range rows)
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

/-- The constructed rank3 fulljet span and literal nonzero pair value
produce actual three-row vanishing coefficients with nonzero fulljet.
This generic finite lemma is used AFTER deriving rank from the original
uniform native minor; it is not an original geometric existence adapter. -/
theorem nativeSurfaceJetThreePoint_exists_coefficients_of_rankThree_pairValue001
    {M : Type u} [Field M] {m : ℕ} (w : Fin m → SurfacePlaneJet M)
    (hRank : finrank M (nativeSurfaceJetCoordinateSpan w) = 3)
    (c B C : Fin m → M) (hJet : (∑ t, c t • w t) = 0)
    (hPair : (∑ t, c t * B t) ≠ 0) :
    ∃ d : Fin m → M,
      (∑ t, d t * (w t).fst) = 0 ∧
      (∑ t, d t * B t) = 0 ∧
      (∑ t, d t * C t) = 0 ∧
      (∑ t, d t • w t) ≠ 0 := by
  have hNot := rankThreePairValue_not_le_threePointSpan001 w hRank c B C hJet hPair
  obtain ⟨phi, hRows, hTangent⟩ := (exists_hyperplane_through_span_not_tangent_iff _ _).mpr hNot
  exact nativeSurfaceJetThreePoint_hyperplane_exists_coefficients001 w B C phi hRows hTangent

end PfaffianDescent.Coray
