import AllCharacteristics.ProjectiveConfigurationAffineCharts

/-!
# Integrality of unordered configuration quotients

An integral ordered configuration space has an integral unordered quotient.
The proof is local on the quotient: every point lies in a free affine quotient
chart, whose invariant ring is a domain.  This supplies the integrality input
for generic-point specialization without assuming it separately on the
unordered configuration space.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics

universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

/-- The actual unordered distinct-configuration quotient of an integral
ordered configuration space is integral. -/
instance isIntegral_projectiveConfigurationQuotientOpen
    [IsIntegral (orderedFamilyConfigurationOver f n).left] :
    IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme := by
  let C := (orderedFamilyConfigurationOver f n).left
  let Q := (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme
  let q : C ⟶ Q := projectiveConfigurationQuotientMap 𝒜 f n
  letI : IrreducibleSpace C := inferInstance
  letI : IrreducibleSpace Q := q.surjective.irreducibleSpace q.continuous
  letI : IsReduced Q := by
    letI : ∀ y : Q, _root_.IsReduced (Q.presheaf.stalk y) := fun y ↦ by
      obtain ⟨x, hxy⟩ := q.surjective y
      obtain ⟨U, hUa, τ, hτ₁, hτcomp, i, hio, hi, p, hp, j, hjo, hx, hs, hib⟩ :=
        exists_projectiveConfigurationQuotient_affineChart 𝒜 f n x
      letI : IsAffine U := hUa
      letI : IsOpenImmersion i := hio
      obtain ⟨u, hu⟩ := hx
      letI : Nonempty U := ⟨u⟩
      letI : IsIntegral U := isIntegral_of_isOpenImmersion i
      letI : IsOpenImmersion j := hjo
      let QD := affineSchemeActionQuotient (Equiv.Perm (Fin n)) τ hτ₁ hτcomp p hp
      let r : U ⟶ QD := affineSchemeActionQuotientMap
        (Equiv.Perm (Fin n)) τ hτ₁ hτcomp p hp
      have hQD : IsIntegral QD :=
        isIntegral_affineSchemeActionQuotient_of_globalSections_domain
          (Equiv.Perm (Fin n)) τ hτ₁ hτcomp p hp
      letI : IsIntegral QD := hQD
      have hyj : j (r u) = y := by
        have hcomm := congrArg (fun m : U ⟶ Q => m u) hs
        have hcomm' : q (i u) = j (r u) := by
          simpa [q, r] using hcomm
        exact hcomm'.symm.trans (by rw [hu, hxy])
      rw [← hyj]
      exact isReduced_of_injective (j.stalkMap (r u)).hom
        (asIso <| j.stalkMap (r u)).commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isReduced_stalk Q
  exact isIntegral_of_irreducibleSpace_of_isReduced Q

/-- The unordered quotient is integral under concrete geometric hypotheses on
the original family.  This combines integrality of the nonempty ordered
distinct-configuration space with the invariant-chart quotient argument. -/
theorem isIntegral_projectiveConfigurationQuotientOpen_of_geometricallyIntegral
    [IsSeparated f] [Nonempty (orderedFamilyConfigurationOver f n).left]
    [GeometricallyIntegral f] [Flat f] [UniversallyOpen f] [LocallyOfFiniteType f]
    [IsIntegral S] [IsLocallyNoetherian S] :
    IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme := by
  letI : IsIntegral (orderedFamilyConfigurationOver f n).left :=
    isIntegral_orderedFamilyConfigurationOver_of_geometricallyIntegral f n
  infer_instance

end AllCharacteristics
