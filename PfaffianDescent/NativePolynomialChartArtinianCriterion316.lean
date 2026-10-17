import PfaffianDescent.NativeChartArtinianSmoothCriterion316
import PfaffianDescent.NativeLocalPolynomialPresentation316

/-! Actual local polynomial presentation tests for chart smoothness.
The polynomial presentation map is arbitrary and surjective; its localization,
quotient equivalence and all smooth/free/Noetherian source properties are derived.
The remaining premise is explicitly the chart lifts of these concrete tests. -/
noncomputable section
namespace PfaffianDescent
open IsLocalRing KaehlerDifferential

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] A) (hf : Function.Surjective f)
  (q : Ideal A) [q.IsPrime]
local notation "P" => Localization.AtPrime (q.comap f.toRingHom)
local notation "I" => RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))
local notation "m" => maximalIdeal P

/-- The original chart A maps to the thin Artinian quotient through its
actual localized presentation, retaining the original R algebra structure. -/
def localPolynomialArtinianChartTest316 (N : ℕ) :
    A →ₐ[R] P ⧸ obstructionThinIdeal316 m I N :=
  (Ideal.Quotient.factorₐ R
    (show I ≤ obstructionThinIdeal316 m I N from le_sup_left)).comp
      ((localPolynomialPresentationQuotientEquiv316 f hf q).symm.toAlgHom.comp
        (IsScalarTower.toAlgHom R A (Localization.AtPrime q)))

lemma localPolynomialArtinianChartTest_apply316 (N : ℕ) (a : A) :
    localPolynomialArtinianChartTest316 f hf q N a =
      Ideal.Quotient.factorₐ R
        (show I ≤ obstructionThinIdeal316 m I N from le_sup_left)
        ((localPolynomialPresentationQuotientEquiv316 f hf q).symm
          (algebraMap A (Localization.AtPrime q) a)) := rfl

/-- Concrete chart test lifts; this is the geometric obligation, not a
new smoothness assumption or a quantified arbitrary-fibre lifting axiom. -/
def LocalPolynomialArtinianChartLifts316 : Prop :=
  ∀ N : ℕ, 0 < N →
    ∃ l : A →ₐ[R] P ⧸ obstructionThickIdeal316 m I N,
      (Ideal.Quotient.factorₐ R (obstructionThickIdeal_le_thin316 m I N)).comp l =
        localPolynomialArtinianChartTest316 f hf q N

theorem formallySmooth_atPrime_of_polynomial_chart_lifts316 [IsNoetherianRing R]
    (hlift : LocalPolynomialArtinianChartLifts316 f hf q) :
    Algebra.FormallySmooth R (Localization.AtPrime q) := by
  letI : IsNoetherianRing P := localPolynomial_isNoetherianRing316 R n _
  letI : Algebra.FormallySmooth R P := localPolynomial_formallySmooth316 R n _
  letI : Module.Free P Ω[P⁄R] := localPolynomial_differential_free316 R n _
  letI : Module.Finite P Ω[P⁄R] := localPolynomial_differential_finite316 R n _
  apply formallySmooth_localization_of_chart_artinian_lifts316 q I
    (localPolynomialPresentation_kernel_le_maximal316 f q)
    (localPolynomialPresentationQuotientEquiv316 f hf q)
  intro N hN
  obtain ⟨l, hl⟩ := hlift N hN
  refine ⟨l, ?_⟩
  intro a
  exact DFunLike.congr_fun hl a

end PfaffianDescent
end
