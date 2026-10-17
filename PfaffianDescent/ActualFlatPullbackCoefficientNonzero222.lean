import PfaffianDescent.ActualDiagonalClassStalkTransport222
import PfaffianDescent.ActualFlatStalkSerreNonzero216

/-! A reusable native flat-stalk cut. Its coefficient identity is an ordinary
input to this generic lemma; the original geometric caller must derive that
identity from SAME218/217/220 data rather than supply a certificate. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open scoped nonZeroDivisors
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A constructed coefficient-one endpoint pullback stays nonzero at an
actual flat geometric stalk. Image regularity/properness are derived by216.
This generic transport lemma is not the final original-geometry endpoint. -/
theorem actualFlatPullbackStalk_nonzero_of_localSerreCoefficient222
    {X Y : Scheme.{u}} (q : X ⟶ Y) [Flat q] (x : X)
    [EnoughInjectives Y.Modules]
    [HasExt.{u} Y.Modules] [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (Y.presheaf.stalk (q x)))]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    {M N : Y.Modules} (z : Ext.{u} M N 2)
    (f g : Y.presheaf.stalk (q x))
    (hf : f ∈ (Y.presheaf.stalk (q x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((Y.presheaf.stalk (q x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ maximalIdeal (Y.presheaf.stalk (q x)))
    (hgm : g ∈ maximalIdeal (Y.presheaf.stalk (q x)))
    (lambda : ModuleCat.of (Y.presheaf.stalk (q x))
      ((Y.presheaf.stalk (q x)) ⧸ Ideal.span ({f, g} : Set (Y.presheaf.stalk (q x)))) ⟶
        (schemeModuleStalkModuleFunctor Y (q x)).obj M)
    (b : (schemeModuleStalkModuleFunctor Y (q x)).obj N ⟶
      ModuleCat.of (Y.presheaf.stalk (q x)) (Y.presheaf.stalk (q x)))
    (hCoefficient : (Ext.mk₀ lambda).comp
      ((z.mapExactFunctor (schemeModuleStalkModuleFunctor Y (q x))).comp
        (Ext.mk₀ b) (add_zero 2)) (zero_add 2) = localSerreExtTwoClass f g 1 hf hg) :
    (cubicPointTraceFieldBaseChangeFlatPullbackExtMap q M N 2 z).mapExactFunctor
      (schemeModuleStalkModuleFunctor X x) ≠ 0 := by
  let T := ModuleCat.extendScalars (q.stalkMap x).hom
  letI : PreservesFiniteLimits T := cubicPointTraceFieldBaseChangeLocalScalarsPreservesFiniteLimits
    (q.stalkMap x).hom (Flat.stalkMap q x)
  have hLocal : (localSerreExtTwoClass f g 1 hf hg).mapExactFunctor T ≠ 0 := by
    change cubicPointTraceFieldBaseChangeLocalExtMap (q.stalkMap x).hom (Flat.stalkMap q x)
      _ _ 2 (localSerreExtTwoClass f g 1 hf hg) ≠ 0
    exact actualFlatStalk_localSerreClass_ne_zero216 q x f g 1 hf hg hfm hgm isUnit_one
  intro hz
  have hNat := cubicPointTraceFieldBaseChangeFlatPullbackStalkExt q x 2 z
  have hTensor : (z.mapExactFunctor (schemeModuleStalkModuleFunctor Y (q x))).mapExactFunctor T = 0 := by
    apply (ext_precomp_isIso_eq_zero_iff222
      ((cubicPointTraceFieldBaseChangeStalkPullbackNatIso q x).app M).hom 2 _).mp
    rw [hz, Ext.zero_comp] at hNat
    exact hNat.symm
  have hMapped := congrArg (fun a => a.mapExactFunctor T) hCoefficient
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    hTensor, Ext.zero_comp, Ext.comp_zero] at hMapped
  exact hLocal hMapped.symm

/-- The same cut with an ordinary proved equality of geometric points.
Dependent source-ring and module types are transported by equality elimination. -/
theorem actualFlatPullbackStalk_nonzero_of_localSerreCoefficient_atPoint222
    {X Y : Scheme.{u}} (q : X ⟶ Y) [Flat q] (x : X) (y : Y) (hxy : q x = y)
    [EnoughInjectives Y.Modules]
    [HasExt.{u} Y.Modules] [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (Y.presheaf.stalk y))]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    {M N : Y.Modules} (z : Ext.{u} M N 2)
    (f g : Y.presheaf.stalk y)
    (hf : f ∈ (Y.presheaf.stalk y)⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((Y.presheaf.stalk y) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ maximalIdeal (Y.presheaf.stalk y))
    (hgm : g ∈ maximalIdeal (Y.presheaf.stalk y))
    (lambda : ModuleCat.of (Y.presheaf.stalk y)
      ((Y.presheaf.stalk y) ⧸ Ideal.span ({f, g} : Set (Y.presheaf.stalk y))) ⟶
        (schemeModuleStalkModuleFunctor Y y).obj M)
    (b : (schemeModuleStalkModuleFunctor Y y).obj N ⟶
      ModuleCat.of (Y.presheaf.stalk y) (Y.presheaf.stalk y))
    (hCoefficient : (Ext.mk₀ lambda).comp
      ((z.mapExactFunctor (schemeModuleStalkModuleFunctor Y y)).comp
        (Ext.mk₀ b) (add_zero 2)) (zero_add 2) = localSerreExtTwoClass f g 1 hf hg) :
    (cubicPointTraceFieldBaseChangeFlatPullbackExtMap q M N 2 z).mapExactFunctor
      (schemeModuleStalkModuleFunctor X x) ≠ 0 := by
  subst y
  exact actualFlatPullbackStalk_nonzero_of_localSerreCoefficient222 q x z f g hf hg
    hfm hgm lambda b hCoefficient

end PfaffianDescent
