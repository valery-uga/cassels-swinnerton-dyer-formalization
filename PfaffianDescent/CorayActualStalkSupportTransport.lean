import PfaffianDescent.CorayTildeActualStalkSupport

/-! Actual nonzero-stalk support isomorphism and open-cover transport.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

/-- ACTUAL nonzero-stalk support is preserved by an ACTUAL module sheaf iso. -/
theorem schemeModuleStalkSupport_eq_of_iso {X : Scheme.{u}}
    {M N : X.Modules} (e : M ≅ N) :
    schemeModuleStalkSupport M = schemeModuleStalkSupport N := by
  ext x
  let eStalk := (Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso e
  exact eStalk.addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr

/-- ACTUAL nonzero-stalk support on an actual open immersion pulls back
exactly. The installed ACTUAL restriction-stalk iso proves the equality. -/
theorem schemeModuleStalkSupport_restrict {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules) :
    schemeModuleStalkSupport ((Scheme.Modules.restrictFunctor f).obj M) =
      f ⁻¹' schemeModuleStalkSupport M := by
  ext y
  let eStalk := (Scheme.Modules.restrictStalkNatIso f y).app M
  exact eStalk.addCommGroupIsoToAddEquiv.toEquiv.nontrivial_congr

/-- Actual support is finite once finitely many actual open charts cover
and the actual restricted supports are finite. This ordinary gluing lemma
introduces no comparison of a chart's support: it is used with supports
DERIVED from actual chart modules in the normalization endpoint. -/
theorem schemeModuleStalkSupport_finite_of_finite_open_cover
    {X : Scheme.{u}} (M : X.Modules) {ι : Type u} [Finite ι]
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (f i)]
    (hcover : ∀ x : X, ∃ i, ∃ y : Y i, f i y = x)
    (hfinite : ∀ i, (schemeModuleStalkSupport
      ((Scheme.Modules.restrictFunctor (f i)).obj M)).Finite) :
    (schemeModuleStalkSupport M).Finite := by
  apply (Set.finite_iUnion (fun i => (hfinite i).image (f i))).subset
  intro x hx
  obtain ⟨i, y, hy⟩ := hcover x
  apply Set.mem_iUnion.mpr
  refine ⟨i, y, ?_, hy⟩
  rw [schemeModuleStalkSupport_restrict]
  change f i y ∈ schemeModuleStalkSupport M
  rwa [hy]

/-- Actual linear equivalence preserves actual prime support, directly
through the nonvanishing scalar criterion; no support certificate is assumed. -/
theorem moduleSupport_eq_of_linearEquiv
    {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N) :
    Module.support R M = Module.support R N := by
  ext P
  rw [Module.mem_support_iff', Module.mem_support_iff']
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨e m, fun r hr hz => hm r hr ?_⟩
    apply e.injective
    simpa only [map_smul, map_zero] using hz
  · rintro ⟨n, hn⟩
    refine ⟨e.symm n, fun r hr hz => hn r hr ?_⟩
    apply e.symm.injective
    simpa only [map_smul, map_zero] using hz

end PfaffianDescent.Coray
