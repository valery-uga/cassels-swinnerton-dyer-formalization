import PfaffianDescent.HilbertBurchResidueMaximalLocalization318
import PfaffianDescent.ActualArtinianQuotientSupport
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
The finite support and its denominator set are
transported through the actual nilpotent coefficient reduction. The
residual support and denominator equality are constructed, not inputs.
-/
noncomputable section
namespace PfaffianDescent
universe u v

/-- Membership in the actual finite support is exactly containment of the
original whole ideal. No reduced quotient is substituted. -/
theorem mem_actualArtinianQuotientSupport_iff318
    {A : Type u} [CommRing A] (J : Ideal A) [IsArtinianRing (A ⧸ J)]
    (P : MaximalSpectrum A) :
    P ∈ actualArtinianQuotientSupport001 J ↔ J ≤ P.asIdeal := by
  classical
  letI : Fintype (MaximalSpectrum (A ⧸ J)) := Fintype.ofFinite _
  constructor
  · intro hP
    obtain ⟨q, _, heq⟩ := Finset.mem_image.mp hP
    rw [← heq]
    intro x hx
    change Ideal.Quotient.mk J x ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact q.asIdeal.zero_mem
  · intro hJP
    letI : (P.asIdeal.map (Ideal.Quotient.mk J)).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
        (by simpa only [Ideal.mk_ker] using hJP)
    let q : MaximalSpectrum (A ⧸ J) := ⟨P.asIdeal.map (Ideal.Quotient.mk J), inferInstance⟩
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_univ _, ?_⟩
    apply MaximalSpectrum.ext
    exact Ideal.comap_map_mk hJP

/-- Image of the original support under the actual nilpotent reduction. -/
def residueFiniteSupport318
    {A : Type u} {A₀ : Type v} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    (t : Finset (MaximalSpectrum A)) : Finset (MaximalSpectrum A₀) := by
  classical
  exact t.image (residueMaximal019 π hπ hker)

theorem residueFiniteSupport_nonempty318
    {A : Type u} {A₀ : Type v} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    (t : Finset (MaximalSpectrum A)) (ht : t.Nonempty) :
    (residueFiniteSupport318 π hπ hker t).Nonempty := by
  classical
  exact ht.image _

theorem residueFiniteSupport_actualSupport318
    {A : Type u} {A₀ : Type v} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π)) (J : Ideal A)
    [IsArtinianRing (A ⧸ J)] [IsArtinianRing (A₀ ⧸ J.map π)] :
    residueFiniteSupport318 π hπ hker (actualArtinianQuotientSupport001 J) =
      actualArtinianQuotientSupport001 (J.map π) := by
  classical
  ext Q
  constructor
  · intro hQ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    apply (mem_actualArtinianQuotientSupport_iff318 _ _).mpr
    exact Ideal.map_mono ((mem_actualArtinianQuotientSupport_iff318 _ _).mp hP)
  · intro hQ
    let P : MaximalSpectrum A := ⟨Q.asIdeal.comap π,
      Ideal.comap_isMaximal_of_surjective π hπ⟩
    have hP : P ∈ actualArtinianQuotientSupport001 J := by
      apply (mem_actualArtinianQuotientSupport_iff318 _ _).mpr
      exact Ideal.map_le_iff_le_comap.mp
        ((mem_actualArtinianQuotientSupport_iff318 _ _).mp hQ)
    apply Finset.mem_image.mpr
    refine ⟨P, hP, ?_⟩
    apply MaximalSpectrum.ext
    exact Ideal.map_comap_of_surjective π hπ Q.asIdeal

/-- The actual residual denominator submonoid is exactly the image of the
original one. Surjectivity is used to lift each denominator itself. -/
theorem finiteSupportDenominators_map_residue318
    {A : Type u} {A₀ : Type v} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    (t : Finset (MaximalSpectrum A)) :
    (finiteSupportDenominators001 t).map π =
      finiteSupportDenominators001 (residueFiniteSupport318 π hπ hker t) := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ Q hQ hyQ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
    have hxP : x ∈ (P.asIdeal.map π).comap π := hyQ
    rw [residueMaximal_comap_map019 π hπ hker P] at hxP
    exact hx P hP hxP
  · intro hy
    obtain ⟨x, rfl⟩ := hπ y
    refine ⟨x, ?_, rfl⟩
    intro P hP hxP
    have hQ : residueMaximal019 π hπ hker P ∈
        residueFiniteSupport318 π hπ hker t :=
      Finset.mem_image.mpr ⟨P, hP, rfl⟩
    exact hy _ hQ (Ideal.mem_map_of_mem π hxP)

end PfaffianDescent
end
