import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Basic

/-! The actual localization of a finite polynomial ring supplies the source
properties used in the Artinian smoothness criterion. -/
namespace PfaffianDescent
open KaehlerDifferential

variable (R : Type*) [CommRing R] (n : ℕ)
  (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime]

theorem localPolynomial_isLocalRing316 : IsLocalRing (Localization.AtPrime q) :=
  inferInstance

theorem localPolynomial_isNoetherianRing316 [IsNoetherianRing R] :
    IsNoetherianRing (Localization.AtPrime q) := inferInstance

theorem localPolynomial_formallySmooth316 :
    Algebra.FormallySmooth R (Localization.AtPrime q) := inferInstance

theorem localPolynomial_differential_free316 :
    Module.Free (Localization.AtPrime q) Ω[Localization.AtPrime q⁄R] := by
  letI : Algebra.FormallyEtale (MvPolynomial (Fin n) R) (Localization.AtPrime q) :=
    Algebra.FormallyEtale.of_isLocalization q.primeCompl
  exact Module.Free.of_equiv
    (tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin n) R) (Localization.AtPrime q))

theorem localPolynomial_differential_finite316 :
    Module.Finite (Localization.AtPrime q) Ω[Localization.AtPrime q⁄R] := inferInstance

end PfaffianDescent
