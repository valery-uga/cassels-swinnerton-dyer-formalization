import PfaffianDescent.NativeArtinianFormalSmoothCriterion316
import PfaffianDescent.NativeLocalizeChartLift316

/-! The local Artinian criterion needs only actual lifts on the original
coefficient chart: localization and presentation transport are constructed here.
The geometric chart-lifting premise is still explicit, not assumed discharged. -/
noncomputable section
namespace PfaffianDescent
open IsLocalRing KaehlerDifferential

variable {R P A : Type*} [CommRing R] [CommRing P] [CommRing A]
  [Algebra R P] [Algebra R A] [IsLocalRing P] [IsNoetherianRing P]
  [Algebra.FormallySmooth R P] [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]

theorem formallySmooth_localization_of_chart_artinian_lifts316
    (q : Ideal A) [q.IsPrime] (I : Ideal P) (hI : I ≤ maximalIdeal P)
    (e : (P ⧸ I) ≃ₐ[R] Localization.AtPrime q)
    (hlift : ∀ N : ℕ, 0 < N →
      ∃ f : A →ₐ[R] P ⧸ obstructionThickIdeal316 (maximalIdeal P) I N,
        ∀ a : A,
          Ideal.Quotient.factorₐ R
            (obstructionThickIdeal_le_thin316 (maximalIdeal P) I N) (f a) =
          Ideal.Quotient.factorₐ R
            (show I ≤ obstructionThinIdeal316 (maximalIdeal P) I N from le_sup_left)
              (e.symm (algebraMap A (Localization.AtPrime q) a))) :
    Algebra.FormallySmooth R (Localization.AtPrime q) := by
  have hquot : Algebra.FormallySmooth R (P ⧸ I) := by
    apply formallySmooth_quotient_of_artinian_tests316 I hI
    intro N hN
    let B := P ⧸ obstructionThickIdeal316 (maximalIdeal P) I N
    let S := P ⧸ obstructionThinIdeal316 (maximalIdeal P) I N
    letI : IsLocalRing B := (obstructionThickQuotient_local_artinian316 I hI N hN).1
    letI : IsLocalRing S := (obstructionThinQuotient_local_artinian316 I hI N hN).1
    let π : B →ₐ[R] S := Ideal.Quotient.factorₐ R
      (obstructionThickIdeal_le_thin316 (maximalIdeal P) I N)
    let c : P ⧸ I →ₐ[R] S := Ideal.Quotient.factorₐ R
      (show I ≤ obstructionThinIdeal316 (maximalIdeal P) I N from le_sup_left)
    let g : Localization.AtPrime q →ₐ[R] S := c.comp e.symm.toAlgHom
    obtain ⟨f, hf⟩ := hlift N hN
    have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective
      (obstructionThickIdeal_le_thin316 (maximalIdeal P) I N)
    let l := localizeChartLift316 q π hπ g f hf
    refine ⟨l.comp e.toAlgHom, ?_⟩
    have hl : π.comp l = g := localizeChartLift_reduction316 q π hπ g f hf
    apply AlgHom.ext
    intro x
    change π (l (e x)) = c x
    have hv := DFunLike.congr_fun hl (e x)
    change π (l (e x)) = c (e.symm (e x)) at hv
    simpa only [e.symm_apply_apply] using hv
  letI := hquot
  exact Algebra.FormallySmooth.of_equiv e

end PfaffianDescent
end
