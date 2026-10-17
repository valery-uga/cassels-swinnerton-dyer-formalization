import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict
import PfaffianDescent.SchemeModuleTensor
import PfaffianDescent.BundleSectionZeroLocus

/-!
Actual module base change to an open subscheme. Every comparison retains
the original scheme ring homomorphisms and canonical restriction/pullback.
No flatness, comparison Iso or projection-formula conclusion is input.
SOURCE ONLY / UNVERIFIED; root owns compiler and audits.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- On every actual open, the open base-change comparison is linear over
the OWN restricted target ring, from the actual morphismRestrict ring law. -/
def schemeModuleOpenPushforwardBaseChangeSectionIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    (M : Y.Modules) (V : U.toScheme.Opens) :
    ((Scheme.Modules.restrictFunctor U.ι).obj
      ((Scheme.Modules.pushforward f).obj M)).val.obj (op V) ≅
    ((Scheme.Modules.pushforward (f ∣_ U)).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M)).val.obj (op V) := by
  let j := f ∣_ U
  let v := (f ⁻¹ᵁ U).ι
  let h := image_morphismRestrict_preimage f U V
  let e : Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V)) ≅ Γ(M, v ''ᵁ (j ⁻¹ᵁ V)) :=
    M.presheaf.mapIso (eqToIso h).op
  refine ModuleCat.isoMk e ?_
  intro r
  ext s
  change Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V)) at s
  change (v.appIso (j ⁻¹ᵁ V)).inv (j.app V r) •
      M.presheaf.map (eqToHom h).op s =
    M.presheaf.map (eqToHom h).op
      (f.app (U.ι ''ᵁ V) ((U.ι.appIso V).inv r) • s)
  simp only [v, Scheme.Opens.ι_appIso, Iso.refl_inv]
  rw [M.map_smul]
  have hr := congrArg
    (fun a : Γ(U.toScheme, V) ⟶ Γ((f ⁻¹ᵁ U).toScheme, j ⁻¹ᵁ V) => a.hom r)
    (morphismRestrict_app f U V)
  apply congrArg (fun a => a • M.presheaf.map (eqToHom h).op s)
  change (j.app V).hom r =
    (Y.presheaf.map (eqToHom h).op).hom ((f.app (U.ι ''ᵁ V)).hom r)
  dsimp only [j, h] at hr ⊢
  exact hr

/-- Pushforward commutes with actual open restriction for an arbitrary
scheme morphism and arbitrary OWN module, by the genuine section transports. -/
def schemeModuleOpenPushforwardBaseChangeIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).obj
      ((Scheme.Modules.pushforward f).obj M) ≅
    (Scheme.Modules.pushforward (f ∣_ U)).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso ?_
  refine PresheafOfModules.isoMk
    (fun V => schemeModuleOpenPushforwardBaseChangeSectionIso f U M V.unop) ?_
  intro V W a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W.unop)).op
      (M.presheaf.map ((Opens.map f.base).map (U.ι.opensFunctor.map a.unop)).op s) =
    M.presheaf.map
      ((f ⁻¹ᵁ U).ι.opensFunctor.map ((Opens.map (f ∣_ U).base).map a.unop)).op
      (M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V.unop)).op s)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (fun b => M.presheaf.map b s)
  exact Subsingleton.elim _ _

/-- Pullback commutes with the SAME actual open restriction. This is the
canonical composition comparison for the actual Cartesian restriction
square; no base-change equivalence is a hypothesis. -/
def schemeModuleOpenPullbackBaseChangeIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (T : X.Modules) :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj
      ((Scheme.Modules.pullback f).obj T) ≅
    (Scheme.Modules.pullback (f ∣_ U)).obj
      ((Scheme.Modules.restrictFunctor U.ι).obj T) := by
  let j := f ∣_ U
  let v := (f ⁻¹ᵁ U).ι
  exact (Scheme.Modules.restrictFunctorIsoPullback v).app
      ((Scheme.Modules.pullback f).obj T) ≪≫
    (Scheme.Modules.pullbackComp v f).app T ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app T ≪≫
    ((Scheme.Modules.pullbackComp j U.ι).app T).symm ≪≫
    (Scheme.Modules.pullback j).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app T).symm

/-- The OWN structure-module pushforward has the actual local structure
module as its open base change, with the original restricted source scheme. -/
def schemeModuleOpenPushforwardUnitBaseChangeIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).obj
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) ≅
    (Scheme.Modules.pushforward (f ∣_ U)).obj
      (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) :=
  schemeModuleOpenPushforwardBaseChangeIso f U (SheafOfModules.unit Y.ringCatSheaf) ≪≫
    (Scheme.Modules.pushforward (f ∣_ U)).mapIso
      (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι)

/-- A coefficient's actual unit chart trivializes its pullback on the
actual inverse-image open, with no whole-support factorization assumption. -/
def schemeModuleOpenPullbackUnitFrameIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (T : X.Modules)
    (eT : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj
      ((Scheme.Modules.pullback f).obj T) ≅
    SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf := by
  let j := f ∣_ U
  letI : IsIso (BundleSectionZeroLocus.pullbackUnitComparison j) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison j
  exact schemeModuleOpenPullbackBaseChangeIso f U T ≪≫
    (Scheme.Modules.pullback j).mapIso eT ≪≫
    asIso (BundleSectionZeroLocus.pullbackUnitComparison j)

/-- The literal quotient tensor has a genuine local unit frame over each
coefficient unit chart, using the ACTUAL restricted source and ring maps. -/
def schemeModuleOpenQuotientTensorUnitIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (T : X.Modules)
    (eU : T.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (Scheme.Modules.restrictFunctor U.ι).obj
      (schemeModuleTensor ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit Y.ringCatSheaf)) T) ≅
    (Scheme.Modules.pushforward (f ∣_ U)).obj
      (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) :=
  (schemeModuleTensorRestrictNatIsoOfLocalTrivialization U T eU).app
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) ≪≫
    schemeModuleOpenPushforwardUnitBaseChangeIso f U

/-- The actual structure restriction map commutes with the actual open
base-change unit frame. This is precisely the morphismRestrict ring law. -/
theorem schemeModuleOpenPushforwardUnitBaseChange_quotient_square
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f) ≫
      (schemeModuleOpenPushforwardUnitBaseChangeIso f U).hom =
    (Scheme.Modules.restrictUnitIso U.ι).hom ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (f ∣_ U) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change ((f ⁻¹ᵁ U).ι.appIso ((f ∣_ U) ⁻¹ᵁ V.unop)).hom
      (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V.unop)).op
        (f.app (U.ι ''ᵁ V.unop) s)) =
    (f ∣_ U).app V.unop ((U.ι.appIso V.unop).hom s)
  simp only [Scheme.Opens.ι_appIso, Iso.refl_hom]
  symm
  change ((f ∣_ U).app V.unop).hom s =
    (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V.unop)).op).hom
      ((f.app (U.ι ''ᵁ V.unop)).hom s)
  exact congrArg
    (fun a : Γ(U.toScheme, V.unop) ⟶
      Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ V.unop) => a.hom s)
    (morphismRestrict_app f U V.unop)

end PfaffianDescent
end
