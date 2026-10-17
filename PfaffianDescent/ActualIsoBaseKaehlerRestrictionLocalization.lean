import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic

/- SOURCE ONLY / UNVERIFIED. A one-open algebra primitive. Localization is
an input ONLY for the coefficient R-ring; the localized DIFFERENTIAL map
and every scalar action are derived. The actual affine caller derives the
coefficient-ring localization from its structure sheaf. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory
universe u

/-- Localizing the top coefficient ring after a genuine R-ring Iso also
localizes the native Kaehler map with the EXACT original R-actions. -/
lemma actualIsoBaseKaehlerRestriction_localized
    {k R A B : Type u} [CommRing k] [CommRing R] [CommRing A] [CommRing B]
    (c : k →+* A) (beta : A →+* B) (e : R ≃+* A) (f : R)
    (hLoc : letI : Algebra R B := (beta.comp e.toRingHom).toAlgebra
      IsLocalization (Submonoid.powers f) B) :
    letI : Algebra k A := c.toAlgebra
    letI : Algebra k B := (beta.comp c).toAlgebra
    letI : Algebra A B := beta.toAlgebra
    letI : Algebra R A := e.toRingHom.toAlgebra
    letI : Algebra R B := (beta.comp e.toRingHom).toAlgebra
    letI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
    letI : SMulCommClass k A B := SMulCommClass.of_commMonoid k A B
    let rSource : Module R (KaehlerDifferential k A) :=
      Module.compHom (KaehlerDifferential k A) e.toRingHom
    let rTarget : Module R (KaehlerDifferential k B) :=
      Module.compHom (KaehlerDifferential k B) e.toRingHom
    letI : SMul R (KaehlerDifferential k A) := rSource.toSMul
    letI : SMul R (KaehlerDifferential k B) := rTarget.toSMul
    letI : Module R (KaehlerDifferential k A) := rSource
    letI : Module R (KaehlerDifferential k B) := rTarget
    letI : IsScalarTower R A (KaehlerDifferential k A) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    letI : IsScalarTower R A (KaehlerDifferential k B) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    letI : LinearMap.CompatibleSMul (KaehlerDifferential k A)
        (KaehlerDifferential k B) R A :=
      { map_smul := fun phi r x => phi.map_smul (e r) x }
    IsLocalizedModule (Submonoid.powers f)
      ((KaehlerDifferential.map k k A B).restrictScalars R) := by
  dsimp only
  letI : Algebra k A := c.toAlgebra
  letI : Algebra k B := (beta.comp c).toAlgebra
  letI : Algebra A B := beta.toAlgebra
  letI : Algebra R A := e.toRingHom.toAlgebra
  letI : Algebra R B := (beta.comp e.toRingHom).toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  letI : SMulCommClass k A B := SMulCommClass.of_commMonoid k A B
  let rSource : Module R (KaehlerDifferential k A) :=
    Module.compHom (KaehlerDifferential k A) e.toRingHom
  let rTarget : Module R (KaehlerDifferential k B) :=
    Module.compHom (KaehlerDifferential k B) e.toRingHom
  letI : SMul R (KaehlerDifferential k A) := rSource.toSMul
  letI : SMul R (KaehlerDifferential k B) := rTarget.toSMul
  letI : Module R (KaehlerDifferential k A) := rSource
  letI : Module R (KaehlerDifferential k B) := rTarget
  letI : IsScalarTower R A (KaehlerDifferential k A) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower R A (KaehlerDifferential k B) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : LinearMap.CompatibleSMul (KaehlerDifferential k A)
      (KaehlerDifferential k B) R A :=
    { map_smul := fun phi r x => phi.map_smul (e r) x }
  letI : IsLocalization (Submonoid.powers f) B := hLoc
  have hmem : (Submonoid.powers (e.toRingHom f)).map e.symm.toMonoidHom =
      Submonoid.powers f :=
    (Submonoid.map_powers e.symm.toMonoidHom (e.toRingHom f)).trans
      (congrArg (fun r : R => Submonoid.powers r)
        (e.symm_toRingHom_apply_toRingHom_apply f))
  letI : IsLocalization (Submonoid.powers (e.toRingHom f)) B :=
    IsLocalization.of_ringEquiv_left e.symm hmem (fun a => by
      simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.apply_symm_apply])
  letI : IsLocalizedModule (Submonoid.powers (e.toRingHom f))
      (KaehlerDifferential.map k k A B) :=
    KaehlerDifferential.isLocalizedModule_map k A B
      (Submonoid.powers (e.toRingHom f))
  have hp : Submonoid.powers ((algebraMap R A) f) =
      Submonoid.powers (e.toRingHom f) :=
    congrArg (fun t : R →+* A => Submonoid.powers (t f))
      (RingHom.algebraMap_toAlgebra e.toRingHom)
  letI : IsLocalizedModule (Submonoid.powers ((algebraMap R A) f))
      (KaehlerDifferential.map k k A B) :=
    (congrArg (fun S : Submonoid A =>
      IsLocalizedModule S (KaehlerDifferential.map k k A B)) hp).mpr
        (inferInstance : IsLocalizedModule (Submonoid.powers (e.toRingHom f))
          (KaehlerDifferential.map k k A B))
  exact IsLocalizedModule.restrictScalars_powers f
    (KaehlerDifferential.map k k A B)

end PfaffianDescent
