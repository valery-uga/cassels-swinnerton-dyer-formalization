import PfaffianDescent.ClosedImmersionCohomologyOneLinearInjection

/-! Actual original closed-immersion cohomology map on original coefficient
connecting classes. This is the canonical right-adjoint Ext map, not a
chosen Cech identification. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u
variable {K : Type u} [Field K] {X Y : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original canonical closed-immersion H1 map carries the original
connecting class to the actual pushed-forward connecting class of the
actual pushforward-unit image of the original global section. -/
theorem closedImmersion_cohomologyOneLinearMap_boundary
    (pi : X ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X) [IsClosedImmersion f]
    [hExtX : HasExt.{u} X.Modules] [hExtY : HasExt.{u} Y.Modules]
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    (q : SheafOfModules.unit Y.ringCatSheaf ⟶ S.X₃) :
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExtX
    letI : HasExt.{u} (SheafOfModules.{u} Y.ringCatSheaf) := hExtY
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
    closedImmersion_cohomologyOneLinearMap pi f S.X₁
      ((Ext.mk₀ (C := Y.Modules) q).comp hS.extClass (zero_add 1)) =
      (Ext.mk₀ (C := X.Modules) (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map q)).comp
        (hS.map_of_exact (Scheme.Modules.pushforward f)).extClass (zero_add 1) := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExtX
  letI : HasExt.{u} (SheafOfModules.{u} Y.ringCatSheaf) := hExtY
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K Y.Modules := schemeModulesLinearOver (f ≫ pi)
  let F := Scheme.Modules.pullback f
  let G := Scheme.Modules.pushforward f
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  letI : PreservesFiniteLimits G := by
    change PreservesFiniteLimits (SheafOfModules.pushforward f.toRingCatSheafHom)
    exact SheafOfModules.pushforward_preservesFiniteLimits _
  letI : G.Additive := Functor.additive_of_preserves_binary_products G
  letI : G.Linear K := schemeModulePushforward_linearOver pi f
  letI : IsIso (BundleSectionZeroLocus.pullbackUnitComparison f) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison f
  let e := asIso (BundleSectionZeroLocus.pullbackUnitComparison f)
  have he : adj.homEquiv (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit Y.ringCatSheaf) e.hom =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hq : adj.homEquiv (SheafOfModules.unit X.ringCatSheaf) S.X₃ (e.hom ≫ q) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫ G.map q :=
    (adj.homEquiv_naturality_right e.hom q).trans
      (congrArg (fun a => a ≫ G.map q) he)
  change rightAdjointExtAddHom F G adj (SheafOfModules.unit X.ringCatSheaf) S.X₁ 1
    ((Ext.mk₀ (C := Y.Modules) e.hom).comp ((Ext.mk₀ (C := Y.Modules) q).comp hS.extClass (zero_add 1)) (zero_add 1)) = _
  rw [Ext.mk₀_comp_mk₀_assoc]
  have hb := rightAdjointExtAddHom_boundary F G adj
    (SheafOfModules.unit X.ringCatSheaf) S hS 0 (Ext.mk₀ (C := Y.Modules) (e.hom ≫ q))
  rw [rightAdjointExtAddHom_mk₀, hq] at hb
  exact hb

end PfaffianDescent.Coray
end
