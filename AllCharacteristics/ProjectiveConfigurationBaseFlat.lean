import AllCharacteristics.ProjectiveConfigurationAffineCharts
import AllCharacteristics.FreeAffineQuotientBaseFlat
import AllCharacteristics.RelativeFlatConfigurations

/-!
# Flatness of the actual unordered configuration parameter scheme

Flatness descends to each actual free affine quotient chart by the trace
retraction. The chart base identities glue this property on the original
unordered configuration scheme, over the original affine base.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

/-- The unordered distinct configurations of an actual flat projective family
are flat over their original affine base, in every characteristic. -/
instance flat_projectiveConfigurationQuotientToBase [Flat f] :
    Flat (projectiveConfigurationQuotientToBase 𝒜 f n) := by
  let : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ Flat.instHasRingHomPropertyFlat
  apply property_of_source_open_neighborhoods (@Flat : MorphismProperty Scheme.{u})
  intro y
  let q := projectiveConfigurationQuotientMap 𝒜 f n
  let base := projectiveConfigurationQuotientToBase 𝒜 f n
  obtain ⟨x, hxy⟩ := q.surjective y
  obtain ⟨U, hUa, τ, hτ₁, hτcomp, i, hio, hi, p, hp, j, hjo, hx, hs, hib⟩ :=
    exists_projectiveConfigurationQuotient_affineChart 𝒜 f n x
  have : IsAffine U := hUa
  have : IsOpenImmersion i := hio
  have : IsOpenImmersion j := hjo
  let G := Equiv.Perm (Fin n)
  let r := affineSchemeActionQuotientMap G τ hτ₁ hτcomp p hp
  let b := affineSchemeActionQuotientToBase G τ hτ₁ hτcomp p hp
  have hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ U) (g : G),
      g ≠ 1 → a ≫ τ g ≠ a := by
    intro K _ a g hg he
    apply configurationRightAction_no_fixed_field_point f n K (a ≫ i) g hg
    rw [Category.assoc, ← hi, ← Category.assoc, he]
  have : Flat p := hib ▸ (inferInstanceAs (Flat (i ≫ (orderedFamilyConfigurationOver f n).hom)))
  have hb : Flat b := flat_affineSchemeActionQuotientToBase_of_free G τ hτ₁ hτcomp p hp hfree
  have : Etale r := etale_affineSchemeActionQuotientMap_of_free G τ hτ₁ hτcomp p hp hfree
  have : Epi r := Flat.epi_of_flat_of_surjective r
  have hfamily : q ≫ base = (orderedFamilyConfigurationOver f n).hom :=
    projectiveConfigurationQuotientMap_toBase 𝒜 f n
  have hlocal : r ≫ b = p := affineSchemeActionQuotientMap_toBase G τ hτ₁ hτcomp p hp
  have he : j ≫ base = b := by
    apply (cancel_epi r).mp
    rw [← Category.assoc r j base, ← hs, Category.assoc i q base, hfamily, hib, hlocal]
  refine ⟨affineSchemeActionQuotient G τ hτ₁ hτcomp p hp, j, hjo, ?_, he.symm ▸ hb⟩
  obtain ⟨u, hu⟩ := hx
  refine ⟨r u, ?_⟩
  exact (congrArg (fun m : U ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme ↦ m u) hs).symm.trans
    ((congrArg q hu).trans hxy)

end AllCharacteristics
