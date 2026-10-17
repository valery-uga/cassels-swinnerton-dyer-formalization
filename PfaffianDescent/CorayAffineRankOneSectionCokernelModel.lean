import PfaffianDescent.CorayAffineOpenSpecSections
import PfaffianDescent.CorayActualStalkSupportTransport
import Mathlib.RingTheory.Spectrum.Prime.Module

/-! The original unit-to-rank-one morphism on an actual affine open has
an ACTUAL finite local module cokernel model. The canonical tilde comparison
preserves the SAME cokernel projection. Finite local sections and closed
actual stalk support are consequences, not premises. No nonzero-section
existence, finite support, local lengths or cycle degree is asserted here.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}}
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal restriction followed by the original affine-open isoSpec
pushforward. Its coefficient ring is the original Gamma(X,U). -/
def affineOpenModuleSpecFunctor (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U) :
    X.Modules ⥤ (Spec Γ(X, U)).Modules :=
  Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pushforward hU.isoSpec.hom

private instance affineOpenModuleSpecFunctor_isLeftAdjoint
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U) :
    (affineOpenModuleSpecFunctor X U hU).IsLeftAdjoint := by
  letI : (Scheme.Modules.pushforward hU.isoSpec.hom).IsEquivalence :=
    (schemeIsoPushforwardEquivalence hU.isoSpec).isEquivalence_functor
  dsimp only [affineOpenModuleSpecFunctor]
  infer_instance

private instance affineOpenModuleSpecFunctor_preservesZeroMorphisms
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U) :
    (affineOpenModuleSpecFunctor X U hU).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

/-- A genuine original over-site rank-one chart yields the actual unit
Iso after restriction and canonical affine Spec transport. Every component
comes from the original ring/sheaf maps, with no supplied comparison. -/
def affineOpenRankOneModuleSpecUnitIso
    (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (affineOpenModuleSpecFunctor X U hU).obj M ≅
      SheafOfModules.unit (Spec Γ(X, U)).ringCatSheaf := by
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let E := Scheme.Modules.overEquiv U
  let S := Scheme.Modules.pushforward hU.isoSpec.hom
  let d : (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
    (Scheme.Modules.overFunctorEquiv U).symm.app M ≪≫ E.functor.mapIso e ≪≫
      (Scheme.Modules.overFunctorEquiv U).app O ≪≫ Scheme.Modules.restrictUnitIso U.ι
  let q := SheafOfModules.unitToPushforwardObjUnit hU.isoSpec.hom.toRingCatSheafHom
  letI : IsIso q := affineSource_unit_isIso_of_isIso hU.isoSpec.hom
  exact S.mapIso d ≪≫ (asIso q).symm

private theorem fromTildeGamma_isIso_of_originalUnitIso
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (e : M ≅ SheafOfModules.unit (Spec R).ringCatSheaf) :
    IsIso (Scheme.Modules.fromTildeΓ (R := R) M) :=
  isIso_fromTildeΓ_iff.mpr ⟨ModuleCat.of R R, ⟨tildeSelf ≪≫ e.symm⟩⟩

/-- The original local SHEAF cokernel is canonically the tilde of the
module cokernel of the original transported map of sections. Actual
cokernel preservation and tilde counit isomorphisms are derived internally. -/
def affineOpenUnitHomCokernel_tildeIso
    (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    (tilde.functor Γ(X, U)).obj
      (cokernel ((moduleSpecΓFunctor (R := Γ(X, U))).map
        ((affineOpenModuleSpecFunctor X U hU).map φ))) ≅
      (affineOpenModuleSpecFunctor X U hU).obj (cokernel φ) := by
  let F := affineOpenModuleSpecFunctor X U hU
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := Γ(X, U)) (F.obj O)) :=
    fromTildeGamma_isIso_of_originalUnitIso _
      (affineOpenRankOneModuleSpecUnitIso O U hU (Iso.refl _))
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := Γ(X, U)) (F.obj M)) :=
    fromTildeGamma_isIso_of_originalUnitIso _ (affineOpenRankOneModuleSpecUnitIso M U hU e)
  exact affineCokernelFromTildeGammaIso (F.map φ) ≪≫ (PreservesCokernel.iso F φ).symm

/-- The actual tilde comparison retains the literal original quotient
projection. No projection compatibility is assumed. -/
theorem affineOpenUnitHomCokernel_tildeIso_π
    (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    (tilde.functor Γ(X, U)).map
        (cokernel.π ((moduleSpecΓFunctor (R := Γ(X, U))).map
          ((affineOpenModuleSpecFunctor X U hU).map φ))) ≫
      (affineOpenUnitHomCokernel_tildeIso M U hU e φ).hom =
      Scheme.Modules.fromTildeΓ (R := Γ(X, U))
        ((affineOpenModuleSpecFunctor X U hU).obj M) ≫
          (affineOpenModuleSpecFunctor X U hU).map (cokernel.π φ) := by
  let F := affineOpenModuleSpecFunctor X U hU
  let G := moduleSpecΓFunctor (R := Γ(X, U))
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := Γ(X, U)) (F.obj O)) :=
    fromTildeGamma_isIso_of_originalUnitIso _
      (affineOpenRankOneModuleSpecUnitIso O U hU (Iso.refl _))
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := Γ(X, U)) (F.obj M)) :=
    fromTildeGamma_isIso_of_originalUnitIso _ (affineOpenRankOneModuleSpecUnitIso M U hU e)
  let E := PreservesCokernel.iso F φ
  have hπ : cokernel.π (F.map φ) ≫ E.inv = F.map (cokernel.π φ) := by
    calc
      _ = (F.map (cokernel.π φ) ≫ E.hom) ≫ E.inv :=
        congrArg (fun t => t ≫ E.inv) (PreservesCokernel.π_iso_hom F φ).symm
      _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (tilde.functor Γ(X, U)).map (cokernel.π (G.map (F.map φ))) ≫
      ((affineCokernelFromTildeGammaIso (F.map φ)).hom ≫ E.inv) = _
  calc
    _ = ((tilde.functor Γ(X, U)).map (cokernel.π (G.map (F.map φ))) ≫
        (affineCokernelFromTildeGammaIso (F.map φ)).hom) ≫ E.inv :=
      (Category.assoc _ _ _).symm
    _ = (Scheme.Modules.fromTildeΓ (R := Γ(X, U)) (F.obj M) ≫
        cokernel.π (F.map φ)) ≫ E.inv :=
      congrArg (fun t => t ≫ E.inv) (affineCokernelFromTildeGammaIso_π (F.map φ))
    _ = _ := (Category.assoc _ _ _).trans
      (congrArg (fun t => Scheme.Modules.fromTildeΓ (R := Γ(X, U)) (F.obj M) ≫ t) hπ)

/-- The ACTUAL local module cokernel is finite over the ORIGINAL affine
coordinate ring. The actual target has rank one; actual quotient
surjectivity proves finiteness. No finite-module certificate is an input. -/
theorem affineOpenUnitHomCokernel_module_finite
    (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    Module.Finite Γ(X, U)
      (show ModuleCat Γ(X, U) from
        cokernel ((moduleSpecΓFunctor (R := Γ(X, U))).map
          ((affineOpenModuleSpecFunctor X U hU).map φ))) := by
  let F := affineOpenModuleSpecFunctor X U hU
  let G := moduleSpecΓFunctor (R := Γ(X, U))
  let f := G.map (F.map φ)
  let E : G.obj (F.obj M) ≅ ModuleCat.of Γ(X, U) Γ(X, U) :=
    G.mapIso (affineOpenRankOneModuleSpecUnitIso M U hU e) ≪≫
      (affineGlobalSectionsUnitLinearEquiv (A := Γ(X, U))).toModuleIso
  letI : Module.Finite Γ(X, U) (G.obj (F.obj M)) := Module.Finite.equiv E.toLinearEquiv.symm
  exact Module.Finite.of_surjective (cokernel.π f).hom
    ((ModuleCat.epi_iff_surjective (cokernel.π f)).mp inferInstance)

/-- Original Gamma(X,U)-sections of the SAME local sheaf cokernel are
finite, and its SAME literal restricted nonzero-stalk support is closed.
This needs only an actual affine unit chart; the zero section and empty
open are included. Finite support still needs the genuine torsion/dimension
argument and is not claimed by this theorem. -/
theorem affineOpenUnitHomCokernel_sections_finite_and_stalkSupport_isClosed
    (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    Module.Finite Γ(X, U) ((schemeOpenModuleFunctor X U).obj (cokernel φ)) ∧
      IsClosed (schemeModuleStalkSupport
        ((Scheme.Modules.restrictFunctor U.ι).obj (cokernel φ))) := by
  let F := affineOpenModuleSpecFunctor X U hU
  let G := moduleSpecΓFunctor (R := Γ(X, U))
  let Q := cokernel φ
  let P := F.obj Q
  let N : ModuleCat Γ(X, U) := cokernel (G.map (F.map φ))
  let E : tilde (R := Γ(X, U)) N ≅ P :=
    affineOpenUnitHomCokernel_tildeIso M U hU e φ
  letI : Module.Finite Γ(X, U) N := affineOpenUnitHomCokernel_module_finite M U hU e φ
  have hfiniteP : Module.Finite Γ(X, U) (G.obj P) :=
    Module.Finite.equiv (G.mapIso E.symm ≪≫ (tilde.isoTop N).symm).toLinearEquiv.symm
  letI : Module.Finite Γ(X, U) (G.obj P) := hfiniteP
  have hP : IsClosed (schemeModuleStalkSupport P) := by
    have hsupport : schemeModuleStalkSupport P = Module.support Γ(X, U) N :=
      (schemeModuleStalkSupport_eq_of_iso E.symm).trans (tilde_actualStalkSupport_eq N)
    have hclosedN : IsClosed (Module.support Γ(X, U) N) := Module.isClosed_support
    exact hsupport.symm ▸ hclosedN
  have hMU : schemeModuleStalkSupport
      ((Scheme.Modules.restrictFunctor hU.isoSpec.hom).obj P) =
      schemeModuleStalkSupport ((Scheme.Modules.restrictFunctor U.ι).obj Q) :=
    schemeModuleStalkSupport_eq_of_iso
      ((Scheme.Modules.restrictFunctorAdjCounitIso hU.isoSpec.hom).app
        ((Scheme.Modules.restrictFunctor U.ι).obj Q))
  have hsections : Module.Finite Γ(X, U) ((schemeOpenModuleFunctor X U).obj Q) :=
    (Module.Finite.equiv_iff
      (affineOpenSpecPushforward_sectionsIso X U hU Q).toLinearEquiv).mp hfiniteP
  refine ⟨hsections, ?_⟩
  rw [← hMU, schemeModuleStalkSupport_restrict]
  exact hP.preimage hU.isoSpec.hom.continuous

end PfaffianDescent.Coray
