import PfaffianDescent.FieldPointExtCoefficientScalar

/-! # Actual residue-field scaling under target coefficient morphisms -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open scoped nonZeroDivisors
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false in
/-- Transported target scalar multiplication scales the actual field-valued
point coordinate by the residue of that scalar. -/
theorem fieldPointExtTwoResidueCoordinate_postcomp_of_conjugate_eq_smul
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (x : Spec (.of L)) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (M N : X.Modules) (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj M ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X (i x)).obj N ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)))
    (phi : N ⟶ N) (a : X.presheaf.stalk (i x))
    (hphi : qN.inv ≫ (schemeModuleStalkModuleFunctor X (i x)).map phi ≫ qN.hom =
      a • 𝟙 _) (z : Ext.{u} M N 2) :
    fieldPointExtTwoResidueCoordinate i x M N f g hf hg hfm hgm qM qN
        (z.comp (Ext.mk₀ phi) (add_zero 2)) =
      closedFieldPointResidueRingEquivAt i x
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x))) a) *
        fieldPointExtTwoResidueCoordinate i x M N f g hf hg hfm hgm qM qN z := by
  change closedFieldPointResidueRingEquivAt i x
      (schemeModuleExtLocalResidueComponentLarge (i x) M N f g hf hg hfm hgm qM qN
        (z.comp (Ext.mk₀ phi) (add_zero 2))) =
      closedFieldPointResidueRingEquivAt i x
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x))) a) *
        closedFieldPointResidueRingEquivAt i x
          (schemeModuleExtLocalResidueComponentLarge (i x) M N f g hf hg hfm hgm qM qN z)
  have hr := schemeModuleExtLocalResidueComponentLarge_postcomp_of_conjugate_eq_smul
    (i x) M N f g hf hg hfm hgm qM qN phi a hphi z
  refine (congrArg (fun v : (X.presheaf.stalk (i x)) ⧸
    IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)) =>
      closedFieldPointResidueRingEquivAt i x v) hr).trans ?_
  change closedFieldPointResidueRingEquivAt i x
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x))) a *
        schemeModuleExtLocalResidueComponentLarge
          (i x) M N f g hf hg hfm hgm qM qN z) = _
  exact map_mul (closedFieldPointResidueRingEquivAt i x) _ _

end PfaffianDescent
