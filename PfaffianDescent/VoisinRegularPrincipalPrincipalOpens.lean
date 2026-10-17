import PfaffianDescent.VoisinRegularPrincipalProjectiveCharts
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Principal-open refinements of projective Cartier charts

A regular-principal equation need not exist on an entire standard projective
coordinate chart. This file refines each such chart by ordinary affine
principal opens and assembles their localized quotient maps into the actual
scheme-level `RegularPrincipalImmersion`.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Localization of a ring map at one element is an affine pushout, hence
its dual square of affine schemes is cartesian. -/
theorem isPullback_spec_awayMap
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (s : A) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Localization.awayMap f s)))
      (Spec.map (CommRingCat.ofHom
        (algebraMap B (Localization.Away (f s)))))
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away s))))
      (Spec.map (CommRingCat.ofHom f)) := by
  have hcomm :
      (Localization.awayMap f s).comp
          (algebraMap A (Localization.Away s)) =
        (algebraMap B (Localization.Away (f s))).comp f := by
    exact IsLocalization.map_comp
      (S := Localization.Away s) (Q := Localization.Away (f s))
      (M := Submonoid.powers s) (T := Submonoid.powers (f s))
      (g := f) (hy := by
        rintro x ⟨n, rfl⟩
        exact ⟨n, by simp⟩)
  letI : IsLocalization ((Submonoid.powers s).map f)
      (Localization.Away (f s)) := by
    rw [Submonoid.map_powers]
    infer_instance
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization
      f (Localization.awayMap f s) hcomm (Submonoid.powers s))).flip

/-- A projective quotient immersion is regular principal when each
standard chart admits a principal-open cover whose localized quotient
kernels have regular generators. The only additional premise is affine
ring algebra; open immersions, coverage, and cartesian squares are proved. -/
noncomputable def regularPrincipalImmersion_of_principalOpenCharts
    {R : Type u} {σ : Type} [CommRing R]
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R))
    (hIJ : I.toIdeal ≤ J.toIdeal)
    (ι : σ → Type)
    (s : ∀ j, ι j → ChartRing I j)
    (hcover : ∀ j, Ideal.span (Set.range (s j)) = ⊤)
    (hprincipal : ∀ (j : σ) (k : ι j),
      let q := chartQuotientMap I J hIJ j
      ∃ z : Localization.Away (s j k),
        IsRegular z ∧
          RingHom.ker (Localization.awayMap q (s j k)) =
            Ideal.span ({z} : Set (Localization.Away (s j k)))) :
    RegularPrincipalImmersion (schemeQuotientMap I J hIJ) where
  Index := Σ j, ι j
  A jk := .of (Localization.Away (s jk.1 jk.2))
  B jk := .of (Localization.Away
    (chartQuotientMap I J hIJ jk.1 (s jk.1 jk.2)))
  target jk :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (ChartRing I jk.1) (Localization.Away (s jk.1 jk.2)))) ≫
      chartι I jk.1
  source jk :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (ChartRing J jk.1)
        (Localization.Away
          (chartQuotientMap I J hIJ jk.1 (s jk.1 jk.2))))) ≫
      chartι J jk.1
  ringMap jk := CommRingCat.ofHom
    (Localization.awayMap (chartQuotientMap I J hIJ jk.1) (s jk.1 jk.2))
  ringMap_surjective jk := by
    change Function.Surjective
      (Localization.awayMap (chartQuotientMap I J hIJ jk.1) (s jk.1 jk.2))
    rw [Localization.awayMap_surjective_iff]
    intro x
    obtain ⟨y, hy⟩ := chartQuotientMap_surjective I J hIJ jk.1 x
    exact ⟨y, 0, by simpa using hy⟩
  targetOpen jk := by
    exact IsOpenImmersion.comp
      (Spec.map (CommRingCat.ofHom
        (algebraMap (ChartRing I jk.1)
          (Localization.Away (s jk.1 jk.2)))))
      (chartι I jk.1)
  cover x := by
    obtain ⟨j, y, hy⟩ := exists_coordinate_chart I x
    have hk : ∃ k : ι j, s j k ∉ y.asIdeal := by
      by_contra h
      push_neg at h
      have hle : Ideal.span (Set.range (s j)) ≤ y.asIdeal := by
        apply Ideal.span_le.mpr
        rintro _ ⟨k, rfl⟩
        exact h k
      exact y.2.ne_top (top_unique ((hcover j ▸ hle) : ⊤ ≤ y.asIdeal))
    obtain ⟨k, hk⟩ := hk
    have hyopen : y ∈ PrimeSpectrum.basicOpen (s j k) := hk
    have hyRange : y ∈ Set.range
        (Spec.map (CommRingCat.ofHom
          (algebraMap (ChartRing I j) (Localization.Away (s j k))))) := by
      change y ∈ Set.range (PrimeSpectrum.comap
        (algebraMap (ChartRing I j) (Localization.Away (s j k))))
      rw [PrimeSpectrum.localization_away_comap_range
        (Localization.Away (s j k)) (s j k)]
      exact hyopen
    obtain ⟨z, hz⟩ := hyRange
    refine ⟨⟨j, k⟩, z, ?_⟩
    change chartι I j
      (Spec.map (CommRingCat.ofHom
        (algebraMap (ChartRing I j) (Localization.Away (s j k)))) z) = x
    rw [hz, hy]
  cartesian jk := by
    let q := chartQuotientMap I J hIJ jk.1
    let t := s jk.1 jk.2
    have hlocal := isPullback_spec_awayMap q t
    have hchart := isPullback_schemeQuotientMap_chart I J hIJ jk.1
    exact hlocal.paste_vert hchart
  principal jk := hprincipal jk.1 jk.2

end PfaffianDescent
