import PfaffianDescent.QuarticHomogeneousJets
import PfaffianDescent.HomogeneousVanishingLinearSystem

/-! The complete quadratic system of the selected jet has dimension at
least three, including after a permutation back to the original coordinates.
Evaluation retains the square-zero direction. -/
noncomputable section
namespace PfaffianDescent
open MvPolynomial Module
universe u

theorem quartic_actualJet_fullQuadrics_finrank_ge_three
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (p v : Fin 3 → L) (σ : Fin 4 ≃ Fin 4)
    (hdim : 3 ≤ finrank K (QuarticNet.affineJetQuadrics (k := K) p v)) :
    letI : Module.Finite K (DualNumber L) := QuarticNet.dualNumber_moduleFinite
    3 ≤ finrank K (homogeneousVanishingPolynomialSubmodule (K := K)
      (QuarticNet.homogeneousAffineDualPoint p v ∘ σ.symm) 2) := by
  letI : Module.Finite K (DualNumber L) := QuarticNet.dualNumber_moduleFinite
  obtain ⟨Q, hQ, hhom, hvan⟩ :=
    QuarticNet.exists_three_homogeneous_quadrics_of_affine_jet_dimension p v hdim
  let W := homogeneousVanishingPolynomialSubmodule (K := K)
    (QuarticNet.homogeneousAffineDualPoint p v ∘ σ.symm) 2
  let q : Fin 3 → W := fun a => ⟨rename σ (Q a), by
    apply (mem_homogeneousVanishingPolynomialSubmodule_iff _ 2 _).mpr
    refine ⟨(hhom a).rename_isHomogeneous, ?_⟩
    change aeval (QuarticNet.homogeneousAffineDualPoint p v ∘ σ.symm)
      (rename σ (Q a)) = 0
    rw [aeval_rename]
    simpa only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using hvan a⟩
  have hq : LinearIndependent K q := by
    apply LinearIndependent.of_comp W.subtype
    exact hQ.map_injOn (renameEquiv K σ).toLinearMap
      (renameEquiv K σ).injective.injOn
  simpa only [Fintype.card_fin] using hq.fintype_card_le_finrank

end PfaffianDescent
