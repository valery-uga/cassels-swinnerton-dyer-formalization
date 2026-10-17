import AllCharacteristics.RegularPairNeighborhoodStalk177
import Mathlib.AlgebraicGeometry.AffineScheme

/-! Source-only179: transport the WHOLE actual affine ideal germ to the
canonical localization, then construct a principal regular-pair neighborhood.
No neighborhood generation or regularity certificate is supplied. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors
universe u

/-- Ring equivalences preserve the actual NZD predicate, including rings
with zero divisors. This cut is also used for the actual quotient equivalence. -/
lemma ringEquiv_mem_nonZeroDivisors179
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (r : R) (hr : r ∈ R⁰) : e r ∈ S⁰ := by
  apply mem_nonZeroDivisors_iff_right.mpr
  intro s hs
  apply e.symm.injective
  change e.symm s = e.symm 0
  rw [map_zero]
  apply (mem_nonZeroDivisors_iff_right.mp hr) (e.symm s)
  have h := congrArg e.symm hs
  simpa only [map_mul, map_zero, RingEquiv.symm_apply_apply] using h

/-- The same whole ideal and successive NZD pair are transported through
an actual ring equivalence. The second NZD is transported in the quotient
by the image of the SAME first generator. -/
lemma ringEquiv_regular_pair179
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (I : Ideal R) (a b : R)
    (hgen : I = Ideal.span ({a, b} : Set R))
    (ha : a ∈ R⁰)
    (hb : Ideal.Quotient.mk (Ideal.span ({a} : Set R)) b ∈
      (R ⧸ Ideal.span ({a} : Set R))⁰) :
    I.map e.toRingHom = Ideal.span ({e a, e b} : Set S) ∧
      e a ∈ S⁰ ∧
      Ideal.Quotient.mk (Ideal.span ({e a} : Set S)) (e b) ∈
        (S ⧸ Ideal.span ({e a} : Set S))⁰ := by
  have hsingle : Ideal.span ({e a} : Set S) =
      (Ideal.span ({a} : Set R)).map e.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let eqv := Ideal.quotientEquiv (Ideal.span ({a} : Set R))
    (Ideal.span ({e a} : Set S)) e hsingle
  refine ⟨?_, ringEquiv_mem_nonZeroDivisors179 e a ha, ?_⟩
  · rw [hgen, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    rfl
  · exact ringEquiv_mem_nonZeroDivisors179 eqv
      (Ideal.Quotient.mk (Ideal.span ({a} : Set R)) b) hb

/-- From the actual whole ideal germ and actual stalk regular pair,
construct an original affine principal parameter avoiding the actual chart
prime, a neighborhood containing the actual point, and a regular pair
generating the WHOLE original ideal in its literal away localization. -/
lemma exists_affine_principal_regular_pair_of_ideal_germ179
    {X : Scheme.{u}} (U : X.affineOpens)
    [IsNoetherianRing Γ(X, U)] (x : X) (hx : x ∈ U.1)
    (J : Ideal Γ(X, U)) (a b : X.presheaf.stalk x)
    (hgen : J.map (X.presheaf.germ U.1 x hx).hom =
      Ideal.span ({a, b} : Set (X.presheaf.stalk x)))
    (ha : a ∈ (X.presheaf.stalk x)⁰)
    (hb : Ideal.Quotient.mk (Ideal.span ({a} : Set (X.presheaf.stalk x))) b ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span ({a} : Set (X.presheaf.stalk x)))⁰) :
    ∃ f : Γ(X, U), f ∉ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal ∧
      x ∈ X.basicOpen f ∧ ∃ a' b' : Localization.Away f,
        J.map (algebraMap Γ(X, U) (Localization.Away f)) =
          Ideal.span ({a', b'} : Set (Localization.Away f)) ∧
        a' ∈ (Localization.Away f)⁰ ∧
        Ideal.Quotient.mk (Ideal.span ({a'} : Set (Localization.Away f))) b' ∈
          ((Localization.Away f) ⧸ Ideal.span ({a'} : Set (Localization.Away f)))⁰ := by
  let P := (U.2.primeIdealOf ⟨x, hx⟩).asIdeal
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) P :=
    U.2.isLocalization_stalk ⟨x, hx⟩
  let E := IsLocalization.algEquiv P.primeCompl
    (X.presheaf.stalk x) (Localization.AtPrime P)
  have hcomm : E.toRingEquiv.toRingHom.comp (X.presheaf.germ U.1 x hx).hom =
      algebraMap Γ(X, U) (Localization.AtPrime P) := by
    apply RingHom.ext
    intro r
    exact E.commutes r
  obtain ⟨hspan, hA, hB⟩ := ringEquiv_regular_pair179 E.toRingEquiv
    (J.map (X.presheaf.germ U.1 x hx).hom) a b hgen ha hb
  have hspanP : J.map (algebraMap Γ(X, U) (Localization.AtPrime P)) =
      Ideal.span ({E a, E b} : Set (Localization.AtPrime P)) := by
    rw [Ideal.map_map, hcomm] at hspan
    exact hspan
  obtain ⟨f, hf, a', b', hJ, hA', hB'⟩ :=
    AllCharacteristics.exists_principal_neighborhood_regular_pair_of_stalk177
      P J (E a) (E b) hspanP hA hB
  have hxF : x ∈ X.basicOpen f := by
    have hpf : U.2.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen f :=
      (PrimeSpectrum.mem_basicOpen f _).mpr hf
    rw [← U.2.fromSpec_preimage_basicOpen] at hpf
    change U.2.fromSpec (U.2.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f at hpf
    rwa [U.2.fromSpec_primeIdealOf] at hpf
  exact ⟨f, hf, hxF, a', b', hJ, hA', hB'⟩

end PfaffianDescent
