import PfaffianDescent.ActualBundledIsoBaseKaehlerRestrictionLocalization

/- SOURCE ONLY / UNVERIFIED. Primitive coefficient-ring Iso stage only;
no actual Gamma/affine module dictionary is expanded in this proof. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory
universe u

private lemma powersOne_value {R : Type u} [CommRing R]
    (s : Submonoid.powers (1 : R)) : (s : R) = 1 := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : R) (1 : R)).mp s.property
  have h : (1 : R) = (s : R) := by simpa only [one_pow] using hn
  exact h.symm

/-- Localization at powers of one is a bijection, for the actual given
linear map and its original module actions. -/
lemma actualLocalizedModulePowersOne_bijective
    {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (v : M →ₗ[R] N)
    [IsLocalizedModule (Submonoid.powers (1 : R)) v] : Function.Bijective v := by
  constructor
  · intro x y hxy
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq
      (S := Submonoid.powers (1 : R)) (f := v) hxy
    change (s : R) • x = (s : R) • y at hs
    simpa only [powersOne_value s, one_smul] using hs
  · intro y
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj
      (Submonoid.powers (1 : R)) v y
    change (s : R) • y = v x at hs
    have h : y = v x := by simpa only [powersOne_value s, one_smul] using hs
    exact ⟨x, h.symm⟩

/-- The TRUE bundled universal differential map induced by a ring Iso is
bijective. Its commuting scalar square is structural data; the actual
GammaSpec caller derives that square from naturality. -/
lemma actualBundledKaehlerRingIsoMap_bijective
    {k R B : Type u} [CommRing k] [CommRing R] [CommRing B]
    (c : k →+* R) (c' : k →+* B) (e : R ≃+* B)
    (fac : (𝟙 (CommRingCat.of k)) ≫ CommRingCat.ofHom c' =
      CommRingCat.ofHom c ≫ CommRingCat.ofHom e.toRingHom) :
    Function.Bijective (CommRingCat.KaehlerDifferential.map fac) := by
  letI : Algebra R B :=
    (e.toRingHom.comp (RingEquiv.refl R).toRingHom).toAlgebra
  have hbij : Function.Bijective (algebraMap R B) := by
    change Function.Bijective (fun r : R => e r)
    exact e.bijective
  have hunit : Algebra.algebraMapSubmonoid B (Submonoid.powers (1 : R)) ≤
      IsUnit.submonoid B := by
    rintro b ⟨r, hr, rfl⟩
    have hr1 : r = 1 := powersOne_value ⟨r, hr⟩
    rw [hr1, map_one]
    exact isUnit_one
  letI : IsLocalization (Submonoid.powers (1 : R)) B :=
    IsLocalization.of_le_isUnit_of_bijective hunit hbij
  have hl := actualBundledIsoBaseKaehlerRestriction_of_square_localized
    c c' e.toRingHom (RingEquiv.refl R) (1 : R) fac inferInstance
  let v := (ModuleCat.restrictScalars (RingEquiv.refl R).toRingHom).map
    (CommRingCat.KaehlerDifferential.map fac)
  letI : IsLocalizedModule (Submonoid.powers (1 : R)) v.hom := hl
  exact actualLocalizedModulePowersOne_bijective v.hom

end PfaffianDescent
