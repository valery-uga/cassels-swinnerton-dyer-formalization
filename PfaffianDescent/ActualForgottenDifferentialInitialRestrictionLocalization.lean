import PfaffianDescent.ActualBundledIsoBaseKaehlerRestrictionLocalization
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf

/- SOURCE ONLY / UNVERIFIED. Generic initial-object normalization, with
the actual forgetful action retained. The top self-restriction is removed
by the INSTALLED restrictScalarsId'App Iso, never by action substitution. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory
universe u

lemma actualForgottenDifferentialInitialRestriction_localized
    {k R : Type u} [CommRing k] [CommRing R]
    {C : Type u} [Category C]
    (B : Cᵒᵖ ⥤ CommRingCat.{u})
    (sigma : (Functor.const Cᵒᵖ).obj (CommRingCat.of k) ⟶ B)
    (c₀ : Cᵒᵖ) (h₀ : CategoryTheory.Limits.IsInitial c₀)
    (e : CommRingCat.of R ≅ B.obj c₀) (c : Cᵒᵖ) (f : R)
    (hLoc : letI : Algebra R (B.obj c) :=
        (e.hom ≫ B.map (h₀.to c)).hom.toAlgebra
      IsLocalization (Submonoid.powers f) (B.obj c)) :
    let P := PresheafOfModules.DifferentialsConstruction.relativeDifferentials' sigma
    let F := ((PresheafOfModules.forgetToPresheafModuleCat c₀ h₀).obj P) ⋙
      ModuleCat.restrictScalars e.hom.hom
    IsLocalizedModule (Submonoid.powers f) ((F.map (h₀.to c)).hom) := by
  dsimp only
  let P := PresheafOfModules.DifferentialsConstruction.relativeDifferentials' sigma
  let F := ((PresheafOfModules.forgetToPresheafModuleCat c₀ h₀).obj P) ⋙
    ModuleCat.restrictScalars e.hom.hom
  let i := h₀.to c
  let M := CommRingCat.KaehlerDifferential (sigma.app c₀)
  have hself : h₀.to c₀ = 𝟙 c₀ := h₀.hom_ext _ _
  have hloop : (B.map (h₀.to c₀)).hom = RingHom.id (B.obj c₀) :=
    congrArg CommRingCat.Hom.hom
      ((congrArg (fun a => B.map a) hself).trans (B.map_id c₀))
  let a := (ModuleCat.restrictScalars e.hom.hom).mapIso
    (ModuleCat.restrictScalarsId'App (B.map (h₀.to c₀)).hom hloop M).symm
  have fac : (𝟙 (CommRingCat.of k)) ≫ sigma.app c =
      sigma.app c₀ ≫ B.map i := sigma.naturality i
  let v := (ModuleCat.restrictScalars e.hom.hom).map
    (CommRingCat.KaehlerDifferential.map fac)
  have hfact : (F.map i).hom.comp a.hom.hom = v.hom := by
    apply LinearMap.ext
    intro x
    rfl
  have hraw := actualBundledIsoBaseKaehlerRestriction_of_square_localized
    (sigma.app c₀).hom (sigma.app c).hom (B.map i).hom
    e.commRingCatIsoToRingEquiv f fac hLoc
  have hcomp : IsLocalizedModule (Submonoid.powers f)
      ((F.map i).hom.comp a.hom.hom) := hfact.symm ▸ hraw
  exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers f)
    a.hom.hom (ConcreteCategory.bijective_of_isIso a.hom)).mp hcomp

end PfaffianDescent
