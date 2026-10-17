import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Algebra

/-! Localizing a genuine algebra surjection at an actual target prime.
The local map and its surjectivity are constructed, not supplied. -/
noncomputable section
namespace PfaffianDescent

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

def localSurjectivePresentationMap316 (f : A →ₐ[R] B) (q : Ideal B) [q.IsPrime] :
    Localization.AtPrime (q.comap f.toRingHom) →ₐ[R] Localization.AtPrime q :=
  { Localization.localRingHom (q.comap f.toRingHom) q f.toRingHom rfl with
    commutes' := by
      intro r
      change Localization.localRingHom (q.comap f.toRingHom) q f.toRingHom rfl
        (algebraMap A _ (algebraMap R A r)) = algebraMap R _ r
      rw [Localization.localRingHom_to_map]
      change algebraMap B (Localization.AtPrime q) (f (algebraMap R A r)) = _
      rw [f.commutes, ← IsScalarTower.algebraMap_apply] }

theorem localSurjectivePresentationMap_algebraMap316
    (f : A →ₐ[R] B) (q : Ideal B) [q.IsPrime] (a : A) :
    localSurjectivePresentationMap316 f q (algebraMap A _ a) =
      algebraMap B (Localization.AtPrime q) (f a) :=
  Localization.localRingHom_to_map _ _ _ rfl a

theorem localSurjectivePresentationMap_surjective316
    (f : A →ₐ[R] B) (hf : Function.Surjective f) (q : Ideal B) [q.IsPrime] :
    Function.Surjective (localSurjectivePresentationMap316 f q) := by
  intro x
  obtain ⟨a, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨s, rfl⟩ := hf s
  refine ⟨IsLocalization.mk' (M := (q.comap f.toRingHom).primeCompl)
    (Localization.AtPrime (q.comap f.toRingHom)) a ⟨s, hs⟩, ?_⟩
  exact Localization.localRingHom_mk' _ _ _ rfl _ _

theorem localSurjectivePresentationMap_isLocalHom316
    (f : A →ₐ[R] B) (q : Ideal B) [q.IsPrime] :
    IsLocalHom (localSurjectivePresentationMap316 f q).toRingHom :=
  Localization.isLocalHom_localRingHom _ _ _ rfl

end PfaffianDescent
end
