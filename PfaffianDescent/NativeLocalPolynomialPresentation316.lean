import PfaffianDescent.NativeLocalSurjectivePresentation316
import PfaffianDescent.NativeLocalPolynomialProperties316

/-! Actual local polynomial presentations at primes of finite-type algebras. -/
noncomputable section
namespace PfaffianDescent
open IsLocalRing KaehlerDifferential

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

def localPolynomialPresentationQuotientEquiv316 {n : ℕ}
    (f : MvPolynomial (Fin n) R →ₐ[R] A) (hf : Function.Surjective f)
    (q : Ideal A) [q.IsPrime] :
    (Localization.AtPrime (q.comap f.toRingHom) ⧸
      RingHom.ker (localSurjectivePresentationMap316 f q).toRingHom) ≃ₐ[R]
        Localization.AtPrime q :=
  Ideal.quotientKerAlgEquivOfSurjective (localSurjectivePresentationMap_surjective316 f hf q)

theorem localPolynomialPresentation_kernel_le_maximal316 {n : ℕ}
    (f : MvPolynomial (Fin n) R →ₐ[R] A) (q : Ideal A) [q.IsPrime] :
    RingHom.ker (localSurjectivePresentationMap316 f q).toRingHom ≤
      maximalIdeal (Localization.AtPrime (q.comap f.toRingHom)) :=
  le_maximalIdeal (RingHom.ker_ne_top _)

theorem exists_localPolynomialPresentation316 [IsNoetherianRing R]
    [Algebra.FiniteType R A] (q : Ideal A) [q.IsPrime] :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A),
      Function.Surjective f ∧
      Function.Surjective (localSurjectivePresentationMap316 f q) ∧
      IsLocalRing (Localization.AtPrime (q.comap f.toRingHom)) ∧
      IsNoetherianRing (Localization.AtPrime (q.comap f.toRingHom)) ∧
      Algebra.FormallySmooth R (Localization.AtPrime (q.comap f.toRingHom)) ∧
      Module.Free (Localization.AtPrime (q.comap f.toRingHom))
        Ω[Localization.AtPrime (q.comap f.toRingHom)⁄R] ∧
      Module.Finite (Localization.AtPrime (q.comap f.toRingHom))
        Ω[Localization.AtPrime (q.comap f.toRingHom)⁄R] ∧
      Nonempty ((Localization.AtPrime (q.comap f.toRingHom) ⧸
        RingHom.ker (localSurjectivePresentationMap316 f q).toRingHom) ≃ₐ[R]
          Localization.AtPrime q) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  exact ⟨n, f, hf, localSurjectivePresentationMap_surjective316 f hf q,
    localPolynomial_isLocalRing316 R n _, localPolynomial_isNoetherianRing316 R n _,
    localPolynomial_formallySmooth316 R n _, localPolynomial_differential_free316 R n _,
    localPolynomial_differential_finite316 R n _,
    ⟨localPolynomialPresentationQuotientEquiv316 f hf q⟩⟩

end PfaffianDescent
end
