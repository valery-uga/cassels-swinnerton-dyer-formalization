import PfaffianDescent.FourTangentDualRescaleScheme

/-! Compatibility of independently chosen actual dual-number presentations.
Changing a generator of the supplied length-two algebra is exactly a
nonzero epsilon rescaling, not an unrelated geometric jet. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
open MvPolynomial TrivSqZeroExt
universe u
variable {K : Type u} [Field K]

theorem dualNumberAlgEquiv_is_actual_rescaling (e : DualNumber K ≃ₐ[K] DualNumber K) :
    ∃ (c : K) (hc : c ≠ 0), e = dualNumberRescaleEquiv c hc := by
  let c := (e (DualNumber.eps : DualNumber K)).snd
  have hfst : (e (DualNumber.eps : DualNumber K)).fst = 0 := by
    have hsq : (e (DualNumber.eps : DualNumber K)).fst *
        (e (DualNumber.eps : DualNumber K)).fst = 0 := by
      rw [← TrivSqZeroExt.fst_mul, ← map_mul, DualNumber.eps_mul_eps, map_zero]
      rfl
    exact (mul_eq_zero.mp hsq).elim id id
  have hc : c ≠ 0 := by
    intro hc0
    have hz : e (DualNumber.eps : DualNumber K) = 0 := by
      apply TrivSqZeroExt.ext
      · simpa using hfst
      · simpa only [TrivSqZeroExt.snd_zero] using hc0
    have heps : (DualNumber.eps : DualNumber K) = 0 :=
      e.injective (hz.trans (map_zero e).symm)
    exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrArg TrivSqZeroExt.snd heps)
  have hMap : e.toAlgHom = dualNumberRescale c := by
    apply DualNumber.algHom_ext
    change e (DualNumber.eps : DualNumber K) = dualNumberRescale c DualNumber.eps
    apply TrivSqZeroExt.ext <;>
      simp [dualNumberRescale, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map,
        LinearMap.mulLeft_apply, hfst, c]
  refine ⟨c, hc, ?_⟩
  apply AlgEquiv.ext
  intro z
  exact DFunLike.congr_fun hMap z

/-- ANY two actual presentations of the SAME supplied local length-two
algebra differ by a literal nonzero epsilon rescaling on every element. -/
theorem actualLengthTwoDualPresentations_rescale
    {A : Type u} [CommRing A] [Algebra K A]
    (e₁ e₂ : A ≃ₐ[K] DualNumber K) :
    ∃ (c : K) (hc : c ≠ 0), ∀ a : A,
      e₂ a = dualNumberRescaleEquiv c hc (e₁ a) := by
  obtain ⟨c, hc, h⟩ := dualNumberAlgEquiv_is_actual_rescaling (e₁.symm.trans e₂)
  refine ⟨c, hc, ?_⟩
  intro a
  have hApply := congrArg (fun e : DualNumber K ≃ₐ[K] DualNumber K => e (e₁ a)) h
  simpa only [AlgEquiv.trans_apply, e₁.symm_apply_apply] using hApply

end PfaffianDescent.QuarticNet
