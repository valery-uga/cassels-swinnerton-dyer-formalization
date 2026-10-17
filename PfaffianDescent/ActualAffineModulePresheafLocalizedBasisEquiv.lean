import PfaffianDescent.ActualLocalizedBasisComparison
import Mathlib.AlgebraicGeometry.Modules.Tilde

/- SOURCE ONLY / UNVERIFIED. Generic module presheaf stage. The actual
relative-differential caller derives all hLoc inputs from one-open202.
The presheaf's actual top module is used directly, not native Omega(k,R). -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u

/-- Resolve the installed tilde localization with an ABSTRACT bundled
module, before any actual presheaf top carrier/dictionaries are substituted. -/
private lemma actualTildeBasicOpenRestriction_localized
    {R : CommRingCat.{u}} (M : ModuleCat R) (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      (tilde.toOpen (R := R) M (PrimeSpectrum.basicOpen f)).hom :=
  tilde.instAwayCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecModuleCatPresheafModulesSheafModulesSpecToSheafOpBasicOpenHomToOpen (R := R) M f

/-- The installed canonical R-actions on an arbitrary genuine module
presheaf on Spec R, including its actual top self-restriction. -/
def actualAffineModulePresheafOverBase
    {R : Type u} [CommRing R]
    (P : (Spec (CommRingCat.of R)).PresheafOfModules) :
    (Spec (CommRingCat.of R)).Opensᵒᵖ ⥤ ModuleCat R :=
  ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
    (CategoryTheory.Limits.initialOpOfTerminal CategoryTheory.Limits.isTerminalTop)).obj P) ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/-- Canonical local comparison to tilde of the SAME actual top module.
Native section actions on both sides are retained and pinned explicitly.
Local coefficient-ring linearity is derived by localization promotion. -/
noncomputable def actualAffineModulePresheafLocalizedBasisEquiv
    {R : Type u} [CommRing R]
    (P : (Spec (CommRingCat.of R)).PresheafOfModules)
    (hLoc : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      (((actualAffineModulePresheafOverBase P).map
        (PrimeSpectrum.basicOpen f).leTop.op).hom)) (f : R) :=
  let X := Spec (CommRingCat.of R)
  let U : X.Opens := PrimeSpectrum.basicOpen f
  let F := actualAffineModulePresheafOverBase P
  let M := F.obj (op ⊤)
  let N := tilde M
  let G := (modulesSpecToSheaf.obj N).obj
  let t : M ⟶
      ((modulesSpecToSheaf (R := CommRingCat.of R)).obj
        (tilde (R := CommRingCat.of R) M)).presheaf.obj (op U) :=
    tilde.toOpen (R := CommRingCat.of R) M U
  let hTilde := actualTildeBasicOpenRestriction_localized
    (R := CommRingCat.of R) M f
  let A := X.presheaf.obj (op U)
  letI : Algebra R A := StructureSheaf.openAlgebra R (op U)
  letI : IsLocalization (Submonoid.powers f) A :=
    StructureSheaf.IsLocalization.to_basicOpen R f
  let aSource : Module A (F.obj (op U)) := (P.obj (op U)).isModule
  let aTarget : Module A (G.obj (op U)) := (N.val.obj (op U)).isModule
  letI : SMul A (F.obj (op U)) := aSource.toSMul
  letI : SMul A (G.obj (op U)) := aTarget.toSMul
  letI : Module A (F.obj (op U)) := aSource
  letI : Module A (G.obj (op U)) := aTarget
  let rSource := (F.obj (op U)).isModule
  let rTarget := (G.obj (op U)).isModule
  letI : SMul R (F.obj (op U)) := rSource.toSMul
  letI : SMul R (G.obj (op U)) := rTarget.toSMul
  letI : Module R (F.obj (op U)) := rSource
  letI : Module R (G.obj (op U)) := rTarget
  letI : IsScalarTower R A (F.obj (op U)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower R A (G.obj (op U)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsLocalizedModule (Submonoid.powers f) (F.map U.leTop.op).hom := hLoc f
  letI : IsLocalizedModule (Submonoid.powers f) t.hom := hTilde
  actualLocalizedBasisLinearEquiv (Submonoid.powers f) A
    (F.map U.leTop.op).hom t.hom

end PfaffianDescent
