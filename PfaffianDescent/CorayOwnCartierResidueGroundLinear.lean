import PfaffianDescent.CorayOwnCartierResidueSequence
import PfaffianDescent.SchemeModuleBaseLinearCategory

/-! Original base-field linearity of the SAME actual Cartier boundary. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
variable {K : Type u} [Field K] {X Z : Scheme.{u}}
variable {i : Z ⟶ X} [IsClosedImmersion i]

/-- Literal Yoneda boundary, enriched using the independently pi-defined action. -/
def RegularPrincipalImmersion.actualCartierResidueBoundaryLinearMap
    (pi : X ⟶ Spec (CommRingCat.of K)) [HasExt.{u} X.Modules]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    letI : Linear K X.Modules := Coray.schemeModulesLinearOver pi
    schemeModuleCohomology X (H.actualCartierResidueSequence W).X₃ 1 →ₗ[K]
      schemeModuleCohomology X W 2 := by
  letI : Linear K X.Modules := Coray.schemeModulesLinearOver pi
  refine
    { toFun := H.actualCartierResidueBoundary W hW
      map_add' := (H.actualCartierResidueBoundary W hW).map_add
      map_smul' := ?_ }
  intro c z
  change (c • z).comp (H.actualCartierResidueExtClass W hW) rfl =
    c • (z.comp (H.actualCartierResidueExtClass W hW) rfl)
  exact Ext.smul_comp z (H.actualCartierResidueExtClass W hW) rfl c

/-- The underlying boundary is exactly the accepted original additive map. -/
theorem RegularPrincipalImmersion.actualCartierResidueBoundaryLinearMap_toAddMonoidHom
    (pi : X ⟶ Spec (CommRingCat.of K)) [HasExt.{u} X.Modules]
    (H : RegularPrincipalImmersion i) (W : X.Modules)
    (hW : schemeModuleLocallyRankOne W) :
    letI : Linear K X.Modules := Coray.schemeModulesLinearOver pi
    (H.actualCartierResidueBoundaryLinearMap pi W hW).toAddMonoidHom =
      H.actualCartierResidueBoundary W hW := rfl

end PfaffianDescent
