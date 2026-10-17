import AllCharacteristics.RegularPairDimension
import AllCharacteristics.ClosedPolynomialDimension
import Mathlib.AlgebraicGeometry.StructureSheaf

/-!
# Closed-point dimension on affine hypersurfaces

The localized quotient is identified with the quotient of the ambient local
ring. For a nonzero equation in three polynomial variables this proves
that the local ring at every closed point has dimension two.
-/

set_option linter.style.haveILetI false

namespace AllCharacteristics
universe u
set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the ambient localization map is the extended equation ideal. -/
theorem localizationQuotientAtPrimeMap_ker
    {A : Type u} [CommRing A] (I : Ideal A)
    (P : Ideal (A ⧸ I)) [P.IsPrime] :
    RingHom.ker (localizationQuotientAtPrimeMap I P) =
      I.map (algebraMap A (Localization.AtPrime (P.under A))) := by
  let R := Localization.AtPrime (P.under A)
  let S := Localization.AtPrime P
  let φ := localizationQuotientAtPrimeMap I P
  have hφ (a : A) : φ (algebraMap A R a) =
      algebraMap (A ⧸ I) S (Ideal.Quotient.mk I a) := by
    exact IsLocalization.lift_eq _ a
  apply le_antisymm
  · intro z hz
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (P.under A).primeCompl z
    have hnum : algebraMap (A ⧸ I) S (Ideal.Quotient.mk I a) = 0 := by
      have heq := congrArg φ (IsLocalization.mk'_spec R a s)
      rw [map_mul, show φ (IsLocalization.mk' R a s) = 0 from hz,
        zero_mul, hφ] at heq
      exact heq.symm
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl S _).mp hnum
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective t.1
    have hbQ : b ∈ (P.under A).primeCompl := by
      change Ideal.Quotient.mk I b ∉ P
      rw [hb]
      exact t.2
    have hba : b * a ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_mul, hb]
      exact ht
    apply (IsLocalization.mk'_mem_map_algebraMap_iff
      (P.under A).primeCompl R I a s).mpr
    exact ⟨b, hbQ, hba⟩
  · apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change φ (algebraMap A R a) = 0
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

/-- Localization of a quotient is the quotient of the ambient local ring
by the extended ideal. -/
noncomputable def localizationQuotientAtPrimeEquiv
    {A : Type u} [CommRing A] (I : Ideal A)
    (P : Ideal (A ⧸ I)) [P.IsPrime] :
    (Localization.AtPrime (P.under A) ⧸
      I.map (algebraMap A (Localization.AtPrime (P.under A)))) ≃+*
        Localization.AtPrime P := by
  let e := RingHom.quotientKerEquivOfSurjective
    (localizationQuotientAtPrimeMap_surjective I P)
  exact (Ideal.quotientEquiv
    (I.map (algebraMap A (Localization.AtPrime (P.under A))))
    (RingHom.ker (localizationQuotientAtPrimeMap I P)) (RingEquiv.refl _)
    (by simpa using localizationQuotientAtPrimeMap_ker I P)).trans e

/-- The local ring of an affine hypersurface in three variables at a closed
point has dimension two, with no smoothness assumption. -/
theorem ringKrullDim_localizationAtMaximal_polynomial_hypersurface_eq_two
    {K : Type u} [Field K] (f : MvPolynomial (Fin 3) K) (hf : f ≠ 0)
    (P : Ideal (MvPolynomial (Fin 3) K ⧸ Ideal.span {f})) [P.IsMaximal] :
    ringKrullDim (Localization.AtPrime P) = 2 := by
  let I : Ideal (MvPolynomial (Fin 3) K) := Ideal.span {f}
  let Q := P.under (MvPolynomial (Fin 3) K)
  letI : Q.IsMaximal := Ideal.comap_isMaximal_of_surjective
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hfQ : f ∈ Q := by
    change Ideal.Quotient.mk I f ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton f))]
    exact P.zero_mem
  let e := localizationQuotientAtPrimeEquiv I P
  rw [← ringKrullDim_eq_of_ringEquiv e]
  have hI : I.map (algebraMap (MvPolynomial (Fin 3) K) (Localization.AtPrime Q)) =
      Ideal.span {algebraMap (MvPolynomial (Fin 3) K) (Localization.AtPrime Q) f} := by
    rw [Ideal.map_span, Set.image_singleton]
  change ringKrullDim (Localization.AtPrime Q ⧸ I.map
    (algebraMap (MvPolynomial (Fin 3) K) (Localization.AtPrime Q))) = 2
  rw [hI]
  exact ringKrullDim_quotient_localized_polynomial_equation_eq_two Q f hf hfQ

open AlgebraicGeometry
/-- Closed scheme points of an affine hypersurface in three-space have
local dimension two. -/
theorem ringKrullDim_stalk_affine_polynomial_hypersurface_eq_two
    {K : Type u} [Field K] (f : MvPolynomial (Fin 3) K) (hf : f ≠ 0)
    (x : Spec (.of (MvPolynomial (Fin 3) K ⧸ Ideal.span {f})))
    (hx : IsClosed ({x} : Set (Spec (.of (MvPolynomial (Fin 3) K ⧸ Ideal.span {f}))))) :
    ringKrullDim ((Spec (.of (MvPolynomial (Fin 3) K ⧸ Ideal.span {f}))).presheaf.stalk x) = 2 := by
  letI : x.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx
  rw [ringKrullDim_eq_of_ringEquiv
    (Spec.stalkIso (.of (MvPolynomial (Fin 3) K ⧸ Ideal.span {f})) x).commRingCatIsoToRingEquiv]
  exact ringKrullDim_localizationAtMaximal_polynomial_hypersurface_eq_two f hf x.asIdeal
end AllCharacteristics
