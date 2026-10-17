import PfaffianDescent.FieldPointExtResidueCoefficientScalar

/-! # Point residue coordinates under a change of coefficient bundle

The source presentation and regular parameters are shared. The two coefficient
stalk coordinates may belong to different locally free rank-one targets.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open scoped nonZeroDivisors
namespace PfaffianDescent
universe u

/-- An endomorphism of a free rank-one module is multiplication by its value
on one. This determines the transported coefficient without a compatibility
hypothesis. -/
theorem moduleCatFreeRankOneHom_eq_scalar {R : Type u} [CommRing R]
    (h : ModuleCat.of R R ⟶ ModuleCat.of R R) :
    h = h (1 : R) • 𝟙 (ModuleCat.of R R) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change h.hom r = h.hom 1 * r
  calc
    h.hom r = h.hom (r • (1 : R)) := by rw [smul_eq_mul, mul_one]
    _ = r • h.hom 1 := h.hom.map_smul r 1
    _ = h.hom 1 * r := by rw [smul_eq_mul, mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposition transports the actual localized Ext class between two
free coefficient stalks by their conjugated scalar. -/
theorem schemeModuleExtLocalClassLarge_postcomp_two_targets
    {X : Scheme.{u}} (x : X) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (M Y Z : X.Modules) (f g : X.presheaf.stalk x)
    (qM : (schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span ({f, g} : Set _)))
    (qY : (schemeModuleStalkModuleFunctor X x).obj Y ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (qZ : (schemeModuleStalkModuleFunctor X x).obj Z ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (phi : Y ⟶ Z) (a : X.presheaf.stalk x)
    (hphi : qY.inv ≫ (schemeModuleStalkModuleFunctor X x).map phi ≫ qZ.hom =
      a • 𝟙 _) (z : Ext.{u} M Y 2) :
    schemeModuleExtLocalClassLarge x M Z f g qM qZ
        (z.comp (Ext.mk₀ phi) (add_zero 2)) =
      (schemeModuleExtLocalClassLarge x M Y f g qM qY z).comp
        (Ext.mk₀ (a • 𝟙 _)) (add_zero 2) := by
  have hphi' : (schemeModuleStalkModuleFunctor X x).map phi ≫ qZ.hom =
      qY.hom ≫ (a • 𝟙 _) := by
    apply (cancel_epi qY.inv).1
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hphi
  let w := schemeModuleStalkModuleExtMap X x M Y 2 z
  have hc : (w.comp (Ext.mk₀ ((schemeModuleStalkModuleFunctor X x).map phi))
        (add_zero 2)).comp (Ext.mk₀ qZ.hom) (add_zero 2) =
      (w.comp (Ext.mk₀ qY.hom) (add_zero 2)).comp
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
        (add_zero 2)).comp (Ext.mk₀ qZ.hom) (add_zero 2)) (zero_add 2) = _
  rw [hc]
  exact (extPullback_postcomp qM.inv (w.comp (Ext.mk₀ qY.hom) (add_zero 2))
    (a • 𝟙 _)).symm

set_option backward.isDefEq.respectTransparency false in
/-- A coefficient map between different rank-one targets multiplies the
actual field-valued residue by the residue of its conjugated stalk scalar. -/
theorem fieldPointExtTwoResidueCoordinate_postcomp_two_targets
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (x : Spec (.of L)) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (M Y Z : X.Modules) (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj M ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qY : (schemeModuleStalkModuleFunctor X (i x)).obj Y ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)))
    (qZ : (schemeModuleStalkModuleFunctor X (i x)).obj Z ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)))
    (phi : Y ⟶ Z) (a : X.presheaf.stalk (i x))
    (hphi : qY.inv ≫ (schemeModuleStalkModuleFunctor X (i x)).map phi ≫ qZ.hom =
      a • 𝟙 _) (z : Ext.{u} M Y 2) :
    fieldPointExtTwoResidueCoordinate i x M Z f g hf hg hfm hgm qM qZ
        (z.comp (Ext.mk₀ phi) (add_zero 2)) =
      closedFieldPointResidueRingEquivAt i x
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x))) a) *
        fieldPointExtTwoResidueCoordinate i x M Y f g hf hg hfm hgm qM qY z := by
  change closedFieldPointResidueRingEquivAt i x
      (localExtTwoResidueCoordinate.{u, u + 1} f g hf hg hfm hgm
        (schemeModuleExtLocalClassLarge (i x) M Z f g qM qZ
          (z.comp (Ext.mk₀ phi) (add_zero 2)))) = _
  rw [schemeModuleExtLocalClassLarge_postcomp_two_targets (i x) M Y Z f g qM qY qZ
    phi a hphi z, ← Ext.smul_eq_comp_mk₀,
    localExtTwoResidueCoordinate_smul f g hf hg hfm hgm a]
  change closedFieldPointResidueRingEquivAt i x
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x))) a *
        schemeModuleExtLocalResidueComponentLarge (i x) M Y f g hf hg hfm hgm qM qY z) = _
  exact map_mul (closedFieldPointResidueRingEquivAt i x) _ _

set_option backward.isDefEq.respectTransparency false in
/-- For any coefficient map, the scalar is computed from its actual stalk
map in the specified free coordinates. No conjugacy equality is an input. -/
theorem fieldPointExtTwoResidueCoordinate_postcomp_two_targets_actual_scalar
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (x : Spec (.of L)) [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (M Y Z : X.Modules) (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj M ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qY : (schemeModuleStalkModuleFunctor X (i x)).obj Y ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)))
    (qZ : (schemeModuleStalkModuleFunctor X (i x)).obj Z ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)))
    (phi : Y ⟶ Z) (z : Ext.{u} M Y 2) :
    fieldPointExtTwoResidueCoordinate i x M Z f g hf hg hfm hgm qM qZ
        (z.comp (Ext.mk₀ phi) (add_zero 2)) =
      closedFieldPointResidueRingEquivAt i x
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
          ((qY.inv ≫ (schemeModuleStalkModuleFunctor X (i x)).map phi ≫ qZ.hom) 1)) *
        fieldPointExtTwoResidueCoordinate i x M Y f g hf hg hfm hgm qM qY z := by
  exact fieldPointExtTwoResidueCoordinate_postcomp_two_targets
    i x M Y Z f g hf hg hfm hgm qM qY qZ phi _
    (moduleCatFreeRankOneHom_eq_scalar _) z

end PfaffianDescent
