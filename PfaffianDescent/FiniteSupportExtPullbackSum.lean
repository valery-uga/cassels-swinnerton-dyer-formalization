import PfaffianDescent.FiniteSupportExtComponents

/-! # Actual Ext pullback across a finite point-sheaf decomposition

The original augmentation decomposes into its actual point components.
Consequently every additive cohomology coordinate evaluates its Ext pullback
as the sum of the point pullbacks, with no sum-naturality hypothesis.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The original map is the sum of its literal finite-support components. -/
theorem finiteSupport_map_eq_sum_components
    {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) {M Q : C} (q : c.pt ≅ Q) (g : M ⟶ Q) :
    g = ∑ i, (g ≫ q.inv ≫ c.π i) ≫ (c.ι i ≫ q.hom) := by
  classical
  symm
  calc
    _ = (g ≫ q.inv) ≫ (∑ i, c.π i ≫ c.ι i) ≫ q.hom := by
      simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
    _ = g := by rw [IsBilimit.total hc]; simp [Category.assoc]

/-- Contravariant Ext pullback along an actual map is the sum of its
point-component pullbacks under an actual finite-biproduct identification. -/
theorem finiteSupport_ext_precomp_eq_sum
    {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) {M Q Y : C} (q : c.pt ≅ Q) (g : M ⟶ Q)
    (n : ℕ) (z : Ext.{w} Q Y n) :
    (Ext.mk₀.{w} g).comp z (zero_add n) =
      ∑ i, (Ext.mk₀.{w} (g ≫ q.inv ≫ c.π i)).comp
        ((Ext.mk₀.{w} (c.ι i ≫ q.hom)).comp z (zero_add n)) (zero_add n) := by
  classical
  calc
    _ = (Ext.mk₀.{w} (∑ i, (g ≫ q.inv ≫ c.π i) ≫ (c.ι i ≫ q.hom))).comp z
        (zero_add n) := by rw [← finiteSupport_map_eq_sum_components hc q g]
    _ = ∑ i, (Ext.mk₀.{w} ((g ≫ q.inv ≫ c.π i) ≫ (c.ι i ≫ q.hom))).comp z
        (zero_add n) := by rw [Ext.mk₀_sum, Ext.sum_comp]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Ext.mk₀_comp_mk₀_assoc]

/-- Every actual additive trace or duality coordinate evaluates the
finite-support pullback as a sum of actual point pullbacks. -/
theorem finiteSupport_ext_coordinate_precomp_eq_sum
    {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) {M Q Y : C} (q : c.pt ≅ Q) (g : M ⟶ Q)
    (n : ℕ) {W : Type*} [AddCommMonoid W]
    (coordinate : Ext.{w} M Y n →+ W) (z : Ext.{w} Q Y n) :
    coordinate ((Ext.mk₀.{w} g).comp z (zero_add n)) =
      ∑ i, coordinate ((Ext.mk₀.{w} (g ≫ q.inv ≫ c.π i)).comp
        ((Ext.mk₀.{w} (c.ι i ≫ q.hom)).comp z (zero_add n)) (zero_add n)) := by
  rw [finiteSupport_ext_precomp_eq_sum hc q g, map_sum]

end PfaffianDescent
