import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Graded localization maps with a specified target coordinate

These forms of localization functoriality use an equality of homogeneous
coordinates explicitly. They avoid identifying different localization types
implicitly when comparing projective coefficient changes with affine charts.
-/

open AlgebraicGeometry CategoryTheory HomogeneousLocalization Graded
namespace AllCharacteristics
universe u
variable {A B α β : Type u} [CommRing A] [CommRing B]
  [SetLike α A] [AddSubgroupClass α A] [SetLike β B] [AddSubgroupClass β B]
  {𝒜 : ℕ → α} {ℬ : ℕ → β} [GradedRing 𝒜] [GradedRing ℬ]

/-- A graded homomorphism induces a map of homogeneous localizations at
coordinates related by a specified equality. -/
noncomputable def gradedAwayMapOfEq (g : 𝒜 →+*ᵍ ℬ) (s : A) (t : B) (he : g s = t) :
    Away 𝒜 s →+* Away ℬ t :=
  HomogeneousLocalization.map g (by
    rintro _ ⟨n, rfl⟩
    change g (s ^ n) ∈ Submonoid.powers t
    rw [map_pow, he]
    exact ⟨n, rfl⟩)

/-- The localization map sends a homogeneous fraction to the fraction of
the mapped numerator with the same denominator exponent. -/
theorem gradedAwayMapOfEq_mk (g : 𝒜 →+*ᵍ ℬ) (s : A) (t : B) (he : g s = t)
    {d : ℕ} (hs : s ∈ 𝒜 d) (ht : t ∈ ℬ d) (n : ℕ) (x : A)
    (hx : x ∈ 𝒜 (n • d)) :
    gradedAwayMapOfEq g s t he (Away.mk 𝒜 hs n x hx) =
      Away.mk ℬ ht n (g x) (map_mem g hx) := by
  subst t
  exact Away.map_mk g s hs n x hx

/-- The localization map agrees with the global morphism of projective
schemes on the corresponding affine charts. -/
theorem awayι_comp_map_of_eq (g : 𝒜 →+*ᵍ ℬ)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
    (s : A) (t : B) (he : g s = t)
    {d : ℕ} (hd : 0 < d) (hs : s ∈ 𝒜 d) (ht : t ∈ ℬ d) :
    Proj.awayι ℬ t ht hd ≫ Proj.map g hg =
      Spec.map (CommRingCat.ofHom (gradedAwayMapOfEq g s t he)) ≫
        Proj.awayι 𝒜 s hs hd := by
  subst t
  exact Proj.awayι_comp_map g hg hd s hs

end AllCharacteristics
