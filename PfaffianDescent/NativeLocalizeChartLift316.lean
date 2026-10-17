import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! Extend an actual chart lift to its stalk. Surjectivity from a local ring
reflects units, so no extra denominator-lifting premise is introduced. -/
noncomputable section
namespace PfaffianDescent

variable {R A B S : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing S]
  [Algebra R A] [Algebra R B] [Algebra R S] [IsLocalRing B] [Nontrivial S]

theorem localizationLift_denominator_isUnit316
    (q : Ideal A) [q.IsPrime] (π : B →ₐ[R] S) (hπ : Function.Surjective π)
    (g : Localization.AtPrime q →ₐ[R] S) (f : A →ₐ[R] B)
    (h : ∀ a : A, π (f a) = g (algebraMap A (Localization.AtPrime q) a))
    (a : q.primeCompl) : IsUnit (f a) := by
  letI : IsLocalHom π.toRingHom := IsLocalHom.of_surjective π.toRingHom hπ
  apply (isUnit_map_iff π.toRingHom (f a)).mp
  change IsUnit (π (f a))
  rw [h]
  exact (IsLocalization.map_units (Localization.AtPrime q) a).map g

def localizeChartLift316
    (q : Ideal A) [q.IsPrime] (π : B →ₐ[R] S) (hπ : Function.Surjective π)
    (g : Localization.AtPrime q →ₐ[R] S) (f : A →ₐ[R] B)
    (h : ∀ a : A, π (f a) = g (algebraMap A (Localization.AtPrime q) a)) :
    Localization.AtPrime q →ₐ[R] B :=
  IsLocalization.liftAlgHom (localizationLift_denominator_isUnit316 q π hπ g f h)

theorem localizeChartLift_algebraMap316
    (q : Ideal A) [q.IsPrime] (π : B →ₐ[R] S) (hπ : Function.Surjective π)
    (g : Localization.AtPrime q →ₐ[R] S) (f : A →ₐ[R] B)
    (h : ∀ a : A, π (f a) = g (algebraMap A (Localization.AtPrime q) a))
    (a : A) : localizeChartLift316 q π hπ g f h
      (algebraMap A (Localization.AtPrime q) a) = f a :=
  IsLocalization.lift_eq _ _

theorem localizeChartLift_reduction316
    (q : Ideal A) [q.IsPrime] (π : B →ₐ[R] S) (hπ : Function.Surjective π)
    (g : Localization.AtPrime q →ₐ[R] S) (f : A →ₐ[R] B)
    (h : ∀ a : A, π (f a) = g (algebraMap A (Localization.AtPrime q) a)) :
    π.comp (localizeChartLift316 q π hπ g f h) = g := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext q.primeCompl
  apply RingHom.ext
  intro a
  change π (localizeChartLift316 q π hπ g f h
    (algebraMap A (Localization.AtPrime q) a)) = _
  rw [localizeChartLift_algebraMap316]
  exact h a

end PfaffianDescent
end
