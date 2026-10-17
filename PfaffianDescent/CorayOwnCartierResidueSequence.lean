import PfaffianDescent.RegularPrincipalImmersionNativeRankOne
import PfaffianDescent.SchemeModuleRankOneDualKernelAction
import PfaffianDescent.SchemeModuleCohomology

/-!
A genuine Cartier residue extension and its derived boundary. The first
map is literal tensoring of the OWN ideal-dual increment. Canonical kernel
contraction identifies its source with the original coefficient line.
The third object remains the literal tensor of i_*O_C with the coefficient
line and OWN ideal dual; no projection-formula or dualizing identification
is assumed. SOURCE ONLY / UNVERIFIED; root owns compiler and audits.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]

/-- The actual canonical Cartier residue extension, retaining its literal
quotient object. Regular-principal geometry supplies kernel contraction;
no short exactness or adjunction conclusion is input. -/
def RegularPrincipalImmersion.actualCartierResidueSequence
    (H : RegularPrincipalImmersion i) (W : X.Modules) : ShortComplex X.Modules := by
  let M := closedImmersionModule i
  let T := schemeModuleTensor W (SchemeModuleInternalHom.dual M)
  let S := closedImmersionIdealTwistSequence i T
  let hM : schemeModuleLocallyRankOne M := H.inverseCartierTwist_locallyRankOne
  let eK := schemeModuleRankOneDualKernelIso M W hM
  let mu := schemeModuleTensorUnitLeftIso T
  let delta := schemeModuleRankOneTensorDualIncrement (closedImmersionModuleToUnit i) W
  let g := mu.inv ≫ S.g
  have haction : eK.hom ≫ delta = S.f ≫ mu.hom :=
    schemeModuleRankOneDualKernelIso_action (closedImmersionModuleToUnit i) W hM
  have hzero : delta ≫ g = 0 := by
    apply (cancel_epi eK.hom).mp
    change eK.hom ≫ (delta ≫ (mu.inv ≫ S.g)) = eK.hom ≫ 0
    rw [← Category.assoc, haction]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, S.zero, comp_zero]
  exact ShortComplex.mk delta g hzero

/-- Exactness is derived from ordinary coefficient-line neighborhoods and
the OWN regular-principal ideal, via the actual tensor ideal sequence. -/
theorem RegularPrincipalImmersion.actualCartierResidueSequence_shortExact
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    (H.actualCartierResidueSequence W).ShortExact := by
  let M := closedImmersionModule i
  let D := SchemeModuleInternalHom.dual M
  let T := schemeModuleTensor W D
  let S := closedImmersionIdealTwistSequence i T
  let hM : schemeModuleLocallyRankOne M := H.inverseCartierTwist_locallyRankOne
  have hT : schemeModuleLocallyRankOne T :=
    schemeModuleLocallyRankOne_tensor W D hW (schemeModuleLocallyRankOne_dual M hM)
  have hS : S.ShortExact := schemeModuleLocallyRankOne_tensor_shortExact T hT
    (closedImmersionModulePushforwardSequence i)
    (closedImmersionModulePushforwardSequence_shortExact i)
  let eK := schemeModuleRankOneDualKernelIso M W hM
  let mu := schemeModuleTensorUnitLeftIso T
  let A := H.actualCartierResidueSequence W
  have haction : eK.hom ≫ A.f = S.f ≫ mu.hom :=
    schemeModuleRankOneDualKernelIso_action (closedImmersionModuleToUnit i) W hM
  let e : S ≅ A := ShortComplex.isoMk eK mu (Iso.refl _)
    haction
    (by
      change mu.hom ≫ mu.inv ≫ S.g = S.g ≫ 𝟙 S.X₃
      simp only [Iso.hom_inv_id_assoc, Category.comp_id])
  exact ShortComplex.shortExact_of_iso e hS

/-- The literal extension class of the constructed residue sequence. -/
def RegularPrincipalImmersion.actualCartierResidueExtClass
    [HasExt.{u} X.Modules] (H : RegularPrincipalImmersion i)
    (W : X.Modules) (hW : schemeModuleLocallyRankOne W) :
    Ext.{u} (H.actualCartierResidueSequence W).X₃ W 1 :=
  (H.actualCartierResidueSequence_shortExact W hW).extClass

/-- Derived residue boundary from the actual quotient H1 to coefficient H2.
This is Yoneda composition with the actual Cartier extension class. -/
def RegularPrincipalImmersion.actualCartierResidueBoundary
    [HasExt.{u} X.Modules] (H : RegularPrincipalImmersion i)
    (W : X.Modules) (hW : schemeModuleLocallyRankOne W) :
    schemeModuleCohomology X (H.actualCartierResidueSequence W).X₃ 1 →+
      schemeModuleCohomology X W 2 :=
  (H.actualCartierResidueExtClass W hW).postcomp
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) rfl

/-- The boundary kills the actual middle restriction, by the genuine
short-exact extension law, not an assumed residue compatibility. -/
theorem RegularPrincipalImmersion.actualCartierResidueBoundary_restriction_zero
    [HasExt.{u} X.Modules] (H : RegularPrincipalImmersion i)
    (W : X.Modules) (hW : schemeModuleLocallyRankOne W)
    (z : schemeModuleCohomology X (H.actualCartierResidueSequence W).X₂ 1) :
    H.actualCartierResidueBoundary W hW
      (schemeModuleCohomologyMap X (H.actualCartierResidueSequence W).g 1 z) = 0 := by
  let A := H.actualCartierResidueSequence W
  have hA := H.actualCartierResidueSequence_shortExact W hW
  change (z.comp (Ext.mk₀ A.g) (add_zero 1)).comp hA.extClass rfl = 0
  rw [Ext.comp_assoc_of_second_deg_zero, hA.comp_extClass, Ext.comp_zero]

/-- Actual residue trace induced by a coefficient H2 trace. Geometric
callers instantiate the already constructed cubic Laurent trace. -/
def RegularPrincipalImmersion.actualCartierResidueTrace
    [HasExt.{u} X.Modules] (H : RegularPrincipalImmersion i)
    (W : X.Modules) (hW : schemeModuleLocallyRankOne W)
    {B : Type u} [AddCommGroup B]
    (tau : schemeModuleCohomology X W 2 →+ B) :
    schemeModuleCohomology X (H.actualCartierResidueSequence W).X₃ 1 →+ B :=
  tau.comp (H.actualCartierResidueBoundary W hW)

/-- The induced residue trace annihilates the actual middle restriction. -/
theorem RegularPrincipalImmersion.actualCartierResidueTrace_restriction_zero
    [HasExt.{u} X.Modules] (H : RegularPrincipalImmersion i)
    (W : X.Modules) (hW : schemeModuleLocallyRankOne W)
    {B : Type u} [AddCommGroup B]
    (tau : schemeModuleCohomology X W 2 →+ B)
    (z : schemeModuleCohomology X (H.actualCartierResidueSequence W).X₂ 1) :
    H.actualCartierResidueTrace W hW tau
      (schemeModuleCohomologyMap X (H.actualCartierResidueSequence W).g 1 z) = 0 := by
  change tau (H.actualCartierResidueBoundary W hW _) = 0
  rw [H.actualCartierResidueBoundary_restriction_zero W hW z, map_zero]

end PfaffianDescent
end
