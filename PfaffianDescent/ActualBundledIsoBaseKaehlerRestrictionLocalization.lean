import PfaffianDescent.ActualIsoBaseKaehlerRestrictionLocalization

/- SOURCE ONLY / UNVERIFIED. The bundled square is compared with the
native map on genuine universal-D generators BEFORE actual Gamma rings
are substituted. No desired differential/localization square is assumed. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory
universe u

/-- The actual bundled restriction, after forgetting along a coefficient
ring Iso, is a localized module map for the ORIGINAL ring action. -/
lemma actualBundledIsoBaseKaehlerRestriction_localized
    {k R A B : Type u} [CommRing k] [CommRing R] [CommRing A] [CommRing B]
    (c : k →+* A) (beta : A →+* B) (e : R ≃+* A) (f : R)
    (hLoc : letI : Algebra R B := (beta.comp e.toRingHom).toAlgebra
      IsLocalization (Submonoid.powers f) B) :
    IsLocalizedModule (Submonoid.powers f)
      (((ModuleCat.restrictScalars e.toRingHom).map
        (CommRingCat.KaehlerDifferential.map
          (f := CommRingCat.ofHom c)
          (f' := CommRingCat.ofHom (beta.comp c))
          (g := 𝟙 (CommRingCat.of k)) (g' := CommRingCat.ofHom beta)
          (by rfl))).hom) := by
  letI : Algebra k A := c.toAlgebra
  letI : Algebra k B := (beta.comp c).toAlgebra
  letI : Algebra A B := beta.toAlgebra
  letI : Algebra R A := e.toRingHom.toAlgebra
  letI : Algebra R B := (beta.comp e.toRingHom).toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  letI : SMulCommClass k A B := SMulCommClass.of_commMonoid k A B
  -- KEEP the native Kaehler A-action. The raw bundled target instead has
  -- Module.compHom along beta. The identity is linear by the TRUE tower law.
  let M := CommRingCat.KaehlerDifferential (CommRingCat.ofHom c)
  let N := ModuleCat.of A (KaehlerDifferential k B)
  let Nraw := (ModuleCat.restrictScalars beta).obj
    (CommRingCat.KaehlerDifferential (CommRingCat.ofHom (beta.comp c)))
  let eta : N ≅ Nraw := LinearEquiv.toModuleIso
    (X₁ := N) (X₂ := Nraw) (m₁ := N.isModule) (m₂ := Nraw.isModule)
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => by
        change (a • (x : KaehlerDifferential k B)) =
          beta a • (x : KaehlerDifferential k B)
        exact (IsScalarTower.algebraMap_smul B a
          (x : KaehlerDifferential k B)).symm
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let fac : (𝟙 (CommRingCat.of k)) ≫ CommRingCat.ofHom (beta.comp c) =
      CommRingCat.ofHom c ≫ CommRingCat.ofHom beta := rfl
  let w : M ⟶ N := ModuleCat.ofHom (KaehlerDifferential.map k k A B)
  let v : M ⟶ Nraw := CommRingCat.KaehlerDifferential.map fac
  have hw : w ≫ eta.hom = v := by
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    change w (CommRingCat.KaehlerDifferential.d
      (f := CommRingCat.ofHom c) a) =
      v (CommRingCat.KaehlerDifferential.d (f := CommRingCat.ofHom c) a)
    exact (KaehlerDifferential.map_D k k A B a).trans
      (CommRingCat.KaehlerDifferential.map_d fac a).symm
  let Q := ModuleCat.restrictScalars e.toRingHom
  have hmap : Q.map w ≫ (Q.mapIso eta).hom = Q.map v :=
    (Q.map_comp w eta.hom).symm.trans (congrArg (fun t => Q.map t) hw)
  have hnat : IsLocalizedModule (Submonoid.powers f) (Q.map w).hom :=
    actualIsoBaseKaehlerRestriction_localized c beta e f hLoc
  have hcomp : IsLocalizedModule (Submonoid.powers f)
      ((Q.mapIso eta).hom.hom.comp (Q.map w).hom) :=
    (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers f)
      (Q.mapIso eta).hom.hom
      (ConcreteCategory.bijective_of_isIso (Q.mapIso eta).hom)).mpr hnat
  have hlinear := congrArg ModuleCat.Hom.hom hmap
  exact hlinear ▸ hcomp

/-- Arbitrary actual scalar-map squares reduce by equality elimination,
so no literal choice of the bundled composite algebra is a caller premise. -/
lemma actualBundledIsoBaseKaehlerRestriction_of_square_localized
    {k R A B : Type u} [CommRing k] [CommRing R] [CommRing A] [CommRing B]
    (c : k →+* A) (c' : k →+* B) (beta : A →+* B)
    (e : R ≃+* A) (f : R)
    (fac : (𝟙 (CommRingCat.of k)) ≫ CommRingCat.ofHom c' =
      CommRingCat.ofHom c ≫ CommRingCat.ofHom beta)
    (hLoc : letI : Algebra R B := (beta.comp e.toRingHom).toAlgebra
      IsLocalization (Submonoid.powers f) B) :
    IsLocalizedModule (Submonoid.powers f)
      (((ModuleCat.restrictScalars e.toRingHom).map
        (CommRingCat.KaehlerDifferential.map fac)).hom) := by
  have h : c' = beta.comp c := congrArg CommRingCat.Hom.hom fac
  cases h
  exact actualBundledIsoBaseKaehlerRestriction_localized c beta e f hLoc

end PfaffianDescent
