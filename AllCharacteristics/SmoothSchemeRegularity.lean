import AllCharacteristics.SmoothRegularity
import AllCharacteristics.RegularAffineStalks
import AllCharacteristics.RegularLocalDomain
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Regular scheme stalks under smooth morphisms

The algebraic regularity theorem is transferred through actual affine charts,
their spectrum isomorphisms, and stalk maps. Pullback open covers handle an
arbitrary locally noetherian base with regular local rings.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u

/-- The domain property transfers across a ring equivalence. -/
lemma isDomain_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (h : IsDomain R) (e : R ≃+* S) : IsDomain S := by
  letI : IsDomain R := h
  letI : Nontrivial S := ⟨⟨0, 1, by
    intro hzero
    have : (0 : R) = 1 := by
      apply e.injective
      simpa using hzero
    exact zero_ne_one this⟩⟩
  letI : NoZeroDivisors S := ⟨by
    intro x y hxy
    have hxy' : e.symm x * e.symm y = 0 := by
      apply e.injective
      simpa using hxy
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hxy' with hx | hy
    · exact Or.inl (by simpa using congrArg e hx)
    · exact Or.inr (by simpa using congrArg e hy)⟩
  exact NoZeroDivisors.to_isDomain S

/-- An open immersion transfers regularity to the corresponding target stalk. -/
lemma isRegularLocalRing_stalk_of_openImmersion_image
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i] (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)] :
    IsRegularLocalRing (Y.presheaf.stalk (i x)) :=
  IsRegularLocalRing.of_ringEquiv (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv.symm

/-- An affine scheme with regular global-section ring has regular local rings. -/
lemma isRegularLocalRing_affine_stalk (X : Scheme.{u}) [IsAffine X]
    [IsRegularRing Γ(X, ⊤)] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
  have := isRegularLocalRing_spec_stalk Γ(X, ⊤) (X.isoSpec.hom x)
  exact isRegularLocalRing_stalk_of_openImmersion X.isoSpec.hom x

/-- A noetherian affine scheme with regular local rings has a regular section ring. -/
lemma isRegularRing_affine_of_regular_stalks (X : Scheme.{u}) [IsAffine X]
    [IsLocallyNoetherian X] (h : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) :
    IsRegularRing Γ(X, ⊤) := by
  have : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  apply isRegularRing_iff.mpr
  intro p hp
  let x : Spec (.of Γ(X, ⊤)) := ⟨p, hp⟩
  have := h (X.isoSpec.inv x)
  have := isRegularLocalRing_stalk_of_openImmersion X.isoSpec.inv x
  exact IsRegularLocalRing.of_ringEquiv (Spec.stalkIso (.of Γ(X, ⊤)) x).commRingCatIsoToRingEquiv

/-- A smooth map of affine schemes preserves regularity of the section rings. -/
lemma isRegularRing_globalSections_of_smooth
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsRegularRing Γ(Y, ⊤)]
    (f : X ⟶ Y) [Smooth f] : IsRegularRing Γ(X, ⊤) := by
  let := f.appTop.hom.toAlgebra
  have : Algebra.Smooth Γ(Y, ⊤) Γ(X, ⊤) :=
    RingHom.smooth_algebraMap.mp (show (algebraMap Γ(Y, ⊤) Γ(X, ⊤)).Smooth from
      (HasRingHomProperty.iff_of_isAffine (P := @Smooth.{u})).mp inferInstance)
  exact isRegularRing_of_smooth Γ(Y, ⊤) Γ(X, ⊤)

/-- A smooth scheme over an affine regular base has regular local rings. -/
lemma isRegularLocalRing_stalk_of_smooth_over_affine
    {X Y : Scheme.{u}} [IsAffine Y] [IsRegularRing Γ(Y, ⊤)]
    (f : X ⟶ Y) [Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  have : IsRegularRing Γ(X.affineCover.X i, ⊤) :=
    isRegularRing_globalSections_of_smooth (X.affineCover.f i ≫ f)
  have := isRegularLocalRing_affine_stalk (X.affineCover.X i) y
  exact isRegularLocalRing_stalk_of_openImmersion_image (X.affineCover.f i) y

/-- A smooth scheme over a locally noetherian base with regular local rings
has regular local rings at every point. -/
theorem isRegularLocalRing_stalk_of_smooth
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Smooth f] (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
  let C : X.OpenCover := Y.affineCover.pullback₁ f
  obtain ⟨i, z, hz⟩ := Scheme.Cover.exists_eq C x
  change Y.affineCover.I₀ at i
  have : IsRegularRing Γ(Y.affineCover.X i, ⊤) :=
    isRegularRing_affine_of_regular_stalks (Y.affineCover.X i) (fun y => by
      have := hY (Y.affineCover.f i y)
      exact isRegularLocalRing_stalk_of_openImmersion (Y.affineCover.f i) y)
  have : IsRegularLocalRing ((C.X i).presheaf.stalk z) :=
    isRegularLocalRing_stalk_of_smooth_over_affine (pullback.snd f (Y.affineCover.f i)) z
  have : IsOpenImmersion (C.f i) :=
    inferInstanceAs (IsOpenImmersion (pullback.fst f (Y.affineCover.f i)))
  have := isRegularLocalRing_stalk_of_openImmersion_image (C.f i) z
  exact hz ▸ this

/-- Every local ring of a scheme smooth over a field is a domain.  This
combines the regular-local consequence of smoothness with the regular-local
domain theorem.  It is the local input needed when a hypothetical
factorization of a smooth projective hypersurface is turned into two
nonzero zero divisors at an intersection point of its factors. -/
theorem isDomain_stalk_of_smooth_toSpec_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  letI : IsRegularRing Γ(Spec (.of K), ⊤) :=
    IsRegularRing.of_ringEquiv
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  letI : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth_over_affine f x
  exact isDomain_of_regularLocalRing _

/-- A scheme smooth over a field is reduced.  Each stalk is a domain by
smooth regularity, and reducedness is detected on stalks. -/
theorem isReduced_of_smooth_toSpec_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] : IsReduced X := by
  letI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    letI : IsDomain (X.presheaf.stalk x) :=
      isDomain_stalk_of_smooth_toSpec_field f x
    infer_instance
  exact isReduced_of_isReduced_stalk X

end AllCharacteristics
