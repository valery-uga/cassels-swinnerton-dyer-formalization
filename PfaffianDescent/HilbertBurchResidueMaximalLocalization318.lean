import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
The actual residue map at every maximal ideal is constructed from the
original surjection with nilpotent kernel. In particular neither a family
of localized quotient maps nor its kernel identities is an input.
-/

noncomputable section

namespace PfaffianDescent

theorem nilpotentIdeal_le_prime019
    {A : Type*} [CommRing A] (K P : Ideal A) [P.IsPrime]
    (hK : IsNilpotent K) : K ≤ P := by
  obtain ⟨n, hn⟩ := hK
  intro x hx
  apply Ideal.IsPrime.mem_of_pow_mem (inferInstance : P.IsPrime) n
  have hxn : x ^ n ∈ K ^ n := Ideal.pow_mem_pow hx n
  rw [hn] at hxn
  rw [Ideal.mem_bot.mp hxn]
  exact P.zero_mem

theorem residueMaximal_comap_map019
    {A A₀ : Type*} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    (P : MaximalSpectrum A) :
    (P.asIdeal.map π).comap π = P.asIdeal := by
  rw [Ideal.comap_map_of_surjective π hπ]
  exact sup_eq_left.mpr
    (nilpotentIdeal_le_prime019 (RingHom.ker π) P.asIdeal hker)

def residueMaximal019
    {A A₀ : Type*} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    (P : MaximalSpectrum A) : MaximalSpectrum A₀ := by
  letI : P.asIdeal.IsMaximal := P.isMaximal
  exact ⟨P.asIdeal.map π,
    Ideal.IsMaximal.map_of_surjective_of_ker_le hπ
      (nilpotentIdeal_le_prime019 (RingHom.ker π) P.asIdeal hker)⟩

def localizedResidueMap019
    {A A₀ : Type*} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    (P : MaximalSpectrum A) :
    Localization.AtPrime P.asIdeal →+*
      Localization.AtPrime (residueMaximal019 π hπ hker P).asIdeal :=
  Localization.localRingHom P.asIdeal
    (residueMaximal019 π hπ hker P).asIdeal π
    (residueMaximal_comap_map019 π hπ hker P).symm

@[simp] theorem localizedResidueMap_algebraMap019
    {A A₀ : Type*} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    (P : MaximalSpectrum A) (a : A) :
    localizedResidueMap019 π hπ hker P
        (algebraMap A (Localization.AtPrime P.asIdeal) a) =
      algebraMap A₀
        (Localization.AtPrime (residueMaximal019 π hπ hker P).asIdeal) (π a) := by
  exact Localization.localRingHom_to_map _ _ _ _ a

theorem residueMaximal_primeCompl_map019
    {A A₀ : Type*} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    (P : MaximalSpectrum A) :
    P.asIdeal.primeCompl.map π =
      (residueMaximal019 π hπ hker P).asIdeal.primeCompl := by
  let Q := residueMaximal019 π hπ hker P
  have hcompl : (Q.asIdeal.comap π).primeCompl = P.asIdeal.primeCompl := by
    ext x
    change x ∉ (P.asIdeal.map π).comap π ↔ x ∉ P.asIdeal
    rw [residueMaximal_comap_map019 π hπ hker P]
  calc
    P.asIdeal.primeCompl.map π = (Q.asIdeal.comap π).primeCompl.map π :=
      congrArg (Submonoid.map π) hcompl.symm
    _ = Q.asIdeal.primeCompl := Ideal.map_primeCompl_comap_of_surjective π hπ _

theorem localizedResidueMap_surjective019
    {A A₀ : Type*} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    (P : MaximalSpectrum A) :
    Function.Surjective (localizedResidueMap019 π hπ hker P) := by
  let Q := residueMaximal019 π hπ hker P
  have hden : P.asIdeal.primeCompl.map π = Q.asIdeal.primeCompl :=
    residueMaximal_primeCompl_map019 π hπ hker P
  letI : IsLocalization (P.asIdeal.primeCompl.map π)
      (Localization.AtPrime Q.asIdeal) := hden.symm ▸ inferInstance
  exact IsLocalization.map_surjective_of_surjective
    (M := P.asIdeal.primeCompl) (S := Localization.AtPrime P.asIdeal)
    (Q := Localization.AtPrime Q.asIdeal) (g := π) hπ

theorem localizedResidueMap_ker019
    {A A₀ : Type*} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    (P : MaximalSpectrum A) :
    RingHom.ker (localizedResidueMap019 π hπ hker P) =
      (RingHom.ker π).map (algebraMap A (Localization.AtPrime P.asIdeal)) := by
  exact IsLocalization.ker_map
    (M := P.asIdeal.primeCompl) (S := Localization.AtPrime P.asIdeal)
    (Localization.AtPrime (residueMaximal019 π hπ hker P).asIdeal) π
    (residueMaximal_primeCompl_map019 π hπ hker P)

theorem localizedResidueMap_coefficient_ker019
    {S A A₀ : Type*} [CommRing S] [CommRing A] [CommRing A₀]
    [Algebra S A]
    (I : Ideal S) (hI : IsNilpotent I)
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = I.map (algebraMap S A))
    (P : MaximalSpectrum A) :
    ∃ (hNil : IsNilpotent (RingHom.ker π)),
      RingHom.ker (localizedResidueMap019 π hπ hNil P) =
        I.map (algebraMap S (Localization.AtPrime P.asIdeal)) := by
  have hNil : IsNilpotent (RingHom.ker π) := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    rw [hker, ← Ideal.map_pow, hn]
    simp only [Ideal.zero_eq_bot, Ideal.map_bot]
  refine ⟨hNil, ?_⟩
  rw [localizedResidueMap_ker019, hker, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

end PfaffianDescent

end
