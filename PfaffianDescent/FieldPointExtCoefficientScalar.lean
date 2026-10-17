import PfaffianDescent.FieldPointExtCoordinate
import PfaffianDescent.ExtSourceIsoCoefficientNaturality

/-! # Coefficient scalar compatibility of the actual local point Ext coordinate -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open scoped nonZeroDivisors
namespace PfaffianDescent
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Transporting a coefficient morphism to a scalar endomorphism of the actual
free target stalk transports postcomposition of the global Ext class as well. -/
theorem schemeModuleExtLocalClassLarge_postcomp_of_conjugate_eq_smul
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g : X.presheaf.stalk x)
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (phi : N ⟶ N) (a : X.presheaf.stalk x)
    (hphi : qN.inv ≫ (schemeModuleStalkModuleFunctor X x).map phi ≫ qN.hom =
      a • 𝟙 _) (z : Ext.{u} M N 2) :
    schemeModuleExtLocalClassLarge x M N f g qM qN
        (z.comp (Ext.mk₀ phi) (add_zero 2)) =
      (schemeModuleExtLocalClassLarge x M N f g qM qN z).comp
        (Ext.mk₀ (a • 𝟙 _)) (add_zero 2) := by
  have hphi' : (schemeModuleStalkModuleFunctor X x).map phi ≫ qN.hom =
      qN.hom ≫ (a • 𝟙 _) := by
    apply (cancel_epi qN.inv).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hphi
  let w := schemeModuleStalkModuleExtMap X x M N 2 z
  have hc : (w.comp (Ext.mk₀ ((schemeModuleStalkModuleFunctor X x).map phi))
        (add_zero 2)).comp (Ext.mk₀ qN.hom) (add_zero 2) =
      (w.comp (Ext.mk₀ qN.hom) (add_zero 2)).comp
        (Ext.mk₀ (a • 𝟙 _)) (add_zero 2) := by
    rw [Ext.comp_assoc_of_second_deg_zero _ _ _ (add_zero 2),
      Ext.mk₀_comp_mk₀, hphi', ← Ext.mk₀_comp_mk₀,
      ← Ext.comp_assoc_of_second_deg_zero _ _ _ (add_zero 2)]
  unfold schemeModuleExtLocalClassLarge
  rw [schemeModuleStalkModuleExtMap_comp]
  simp only [schemeModuleStalkModuleExtMap, Functor.mapExtAddHom_apply,
    Ext.mapExactFunctor_mk₀]
  change (Ext.mk₀ qM.inv).comp
      ((w.comp (Ext.mk₀ ((schemeModuleStalkModuleFunctor X x).map phi))
        (add_zero 2)).comp (Ext.mk₀ qN.hom) (add_zero 2)) (zero_add 2) = _
  rw [hc]
  exact (extPullback_postcomp qM.inv (w.comp (Ext.mk₀ qN.hom) (add_zero 2))
    (a • 𝟙 _)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual complete-intersection residue coordinate scales under a coefficient
morphism whose transported target stalk is scalar multiplication. -/
theorem schemeModuleExtLocalResidueComponentLarge_postcomp_of_conjugate_eq_smul
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M N : X.Modules) (f g : X.presheaf.stalk x)
    (hf : f ∈ (X.presheaf.stalk x)⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X x).obj N ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (phi : N ⟶ N) (a : X.presheaf.stalk x)
    (hphi : qN.inv ≫ (schemeModuleStalkModuleFunctor X x).map phi ≫ qN.hom =
      a • 𝟙 _) (z : Ext.{u} M N 2) :
    schemeModuleExtLocalResidueComponentLarge x M N f g hf hg hfm hgm qM qN
        (z.comp (Ext.mk₀ phi) (add_zero 2)) =
      a • schemeModuleExtLocalResidueComponentLarge x M N f g hf hg hfm hgm qM qN z := by
  change localExtTwoResidueCoordinate.{u, u + 1} f g hf hg hfm hgm
      (schemeModuleExtLocalClassLarge x M N f g qM qN
        (z.comp (Ext.mk₀ phi) (add_zero 2))) =
      a • localExtTwoResidueCoordinate.{u, u + 1} f g hf hg hfm hgm
        (schemeModuleExtLocalClassLarge x M N f g qM qN z)
  rw [schemeModuleExtLocalClassLarge_postcomp_of_conjugate_eq_smul
    x M N f g qM qN phi a hphi z, ← Ext.smul_eq_comp_mk₀]
  exact localExtTwoResidueCoordinate_smul f g hf hg hfm hgm a _

end PfaffianDescent
