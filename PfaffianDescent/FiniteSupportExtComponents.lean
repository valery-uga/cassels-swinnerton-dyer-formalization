import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Detection of Ext classes on finite biproducts

The global-to-local step in Voisin's finite-support calculation reduces,
after splitting the finite subscheme, to additivity of `Ext` in its first
variable.  This file records the precise joint-detection statements.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt C]

/-- Contravariant transport of Ext along an isomorphism is injective. -/
theorem ext_precomp_iso_injective
    {A B Y : C} (e : A ≅ B) (n : ℕ) :
    Function.Injective (fun z : Ext B Y n ↦
      (Ext.mk₀ e.hom).comp z (zero_add n)) := by
  intro z z' h
  have h' := congrArg
    (fun w : Ext A Y n ↦ (Ext.mk₀ e.inv).comp w (zero_add n)) h
  simpa [Ext.mk₀_comp_mk₀_assoc] using h'

/-- Covariant transport of Ext along an isomorphism is injective. -/
theorem ext_postcomp_iso_injective
    {X A B : C} (e : A ≅ B) (n : ℕ) :
    Function.Injective (fun z : Ext X A n ↦
      z.comp (Ext.mk₀ e.hom) (add_zero n)) := by
  intro z z' h
  have h' := congrArg
    (fun w : Ext X B n ↦ w.comp (Ext.mk₀ e.inv) (add_zero n)) h
  simpa [Ext.comp_assoc_of_second_deg_zero] using h'

/-- The canonical Ext components of a finite biproduct jointly detect every
class. -/
theorem ext_biproduct_components_jointly_detect
    {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) (Y : C) (n : ℕ) (z : Ext c.pt Y n)
    (hz : ∀ i,
      (Ext.mk₀ (c.ι i)).comp z (zero_add n) = 0) :
    z = 0 := by
  apply (Ext.biproductAddEquiv hc Y n).injective
  ext i
  simpa [Ext.biproductAddEquiv] using hz i

/-- Every tuple of Ext classes on the summands of a finite biproduct is
realized by a class on the whole biproduct.  This is the existence direction
complementing `ext_biproduct_components_jointly_detect`. -/
theorem ext_biproduct_components_surjective
    {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) (Y : C) (n : ℕ)
    (components : ∀ i, Ext (X i) Y n) :
    ∃ z : Ext c.pt Y n, ∀ i,
      (Ext.mk₀ (c.ι i)).comp z (zero_add n) = components i := by
  let e := Ext.biproductAddEquiv hc Y n
  refine ⟨e.symm components, ?_⟩
  intro i
  exact congrFun (e.right_inv components) i

/-- Component classes can also be assembled after identifying the global
source with a finite biproduct by an isomorphism. -/
theorem ext_iso_biproduct_components_surjective
    {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) {M Y : C} (q : c.pt ≅ M) (n : ℕ)
    (components : ∀ i, Ext (X i) Y n) :
    ∃ z : Ext M Y n, ∀ i,
      (Ext.mk₀ (c.ι i ≫ q.hom)).comp z (zero_add n) = components i := by
  let e := Ext.biproductAddEquiv hc Y n
  let z' := e.symm components
  refine ⟨(Ext.mk₀ q.inv).comp z' (zero_add n), ?_⟩
  intro i
  have hi : (Ext.mk₀ (c.ι i)).comp (e.symm components) (zero_add n) =
      components i := congrFun (e.right_inv components) i
  calc
    (Ext.mk₀ (c.ι i ≫ q.hom)).comp
        ((Ext.mk₀ q.inv).comp z' (zero_add n)) (zero_add n) =
      (Ext.mk₀ (c.ι i)).comp z' (zero_add n) := by
        rw [Ext.mk₀_comp_mk₀_assoc]
        simp [Category.assoc, q.hom_inv_id]
    _ = components i := by simpa [z'] using hi

/-- Contravariant additivity of `Ext` across a finite biproduct, after the
global source has been identified with that biproduct.  This packages the
joint-detection and assembly statements below as an actual additive
equivalence. -/
noncomputable def extIsoBiproductAddEquiv
    {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) {M Y : C} (q : c.pt ≅ M) (n : ℕ) :
    Ext M Y n ≃+ (∀ i, Ext (X i) Y n) where
  toFun z := Ext.biproductAddEquiv hc Y n
    ((Ext.mk₀ q.hom).comp z (zero_add n))
  invFun z := (Ext.mk₀ q.inv).comp
    ((Ext.biproductAddEquiv hc Y n).symm z) (zero_add n)
  left_inv z := by
    simp [Ext.mk₀_comp_mk₀_assoc]
  right_inv z := by
    simpa [Ext.mk₀_comp_mk₀_assoc] using
      (Ext.biproductAddEquiv hc Y n).apply_symm_apply z
  map_add' z z' := by simp

/-- The coordinates of `extIsoBiproductAddEquiv` are the expected
precompositions with the summand inclusions followed by the chosen global
identification. -/
theorem extIsoBiproductAddEquiv_apply
    {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) {M Y : C} (q : c.pt ≅ M) (n : ℕ)
    (z : Ext M Y n) (i : J) :
    extIsoBiproductAddEquiv hc q n z i =
      (Ext.mk₀ (c.ι i ≫ q.hom)).comp z (zero_add n) := by
  simp [extIsoBiproductAddEquiv, Ext.biproductAddEquiv,
    Ext.mk₀_comp_mk₀_assoc]

/-- Pointwise additive coordinates that are equivalences assemble to an
additive coordinate equivalence on a globally identified finite
biproduct. -/
noncomputable def extIsoBiproductCoordinateAddEquiv
    {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) {M Y : C} (q : c.pt ≅ M) (n : ℕ)
    {W : J → Type*} [∀ i, AddCommMonoid (W i)]
    (coordinate : ∀ i, Ext (X i) Y n ≃+ W i) :
    Ext M Y n ≃+ (∀ i, W i) :=
  (extIsoBiproductAddEquiv hc q n).trans
    (AddEquiv.piCongrRight coordinate)

theorem extIsoBiproductCoordinateAddEquiv_apply
    {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) {M Y : C} (q : c.pt ≅ M) (n : ℕ)
    {W : J → Type*} [∀ i, AddCommMonoid (W i)]
    (coordinate : ∀ i, Ext (X i) Y n ≃+ W i)
    (z : Ext M Y n) (i : J) :
    extIsoBiproductCoordinateAddEquiv hc q n coordinate z i =
      coordinate i
        ((Ext.mk₀ (c.ι i ≫ q.hom)).comp z (zero_add n)) := by
  simp [extIsoBiproductCoordinateAddEquiv,
    extIsoBiproductAddEquiv_apply]

/-- Injective coordinates on each point-supported Ext group still jointly
detect a class on their finite biproduct.  This is the abstract categorical
form of the residue-component step in Voisin's argument. -/
theorem ext_biproduct_injective_coordinates_jointly_detect
    {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) (Y : C) (n : ℕ)
    {W : J → Type*} [∀ i, AddCommMonoid (W i)]
    (coordinate : ∀ i, Ext (X i) Y n →+ W i)
    (hcoordinate : ∀ i, Function.Injective (coordinate i))
    (z : Ext c.pt Y n)
    (hz : ∀ i, coordinate i
      ((Ext.mk₀ (c.ι i)).comp z (zero_add n)) = 0) :
    z = 0 := by
  apply ext_biproduct_components_jointly_detect hc Y n z
  intro i
  apply hcoordinate i
  simpa using hz i

/-- The same joint-detection result when the globally supported source is
identified with a finite biproduct.  Its components are induced by the
actual inclusions `X i ⟶ c.pt` followed by the chosen global isomorphism. -/
theorem ext_iso_biproduct_injective_coordinates_jointly_detect
    {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) {M Y : C} (q : c.pt ≅ M) (n : ℕ)
    {W : J → Type*} [∀ i, AddCommMonoid (W i)]
    (coordinate : ∀ i, Ext (X i) Y n →+ W i)
    (hcoordinate : ∀ i, Function.Injective (coordinate i))
    (z : Ext M Y n)
    (hz : ∀ i, coordinate i
      ((Ext.mk₀ (c.ι i ≫ q.hom)).comp z (zero_add n)) = 0) :
    z = 0 := by
  let z' : Ext c.pt Y n := (Ext.mk₀ q.hom).comp z (zero_add n)
  have hz' : z' = 0 := by
    apply ext_biproduct_injective_coordinates_jointly_detect
      hc Y n coordinate hcoordinate z'
    intro i
    simpa [z', Ext.mk₀_comp_mk₀_assoc] using hz i
  have hrecover := congrArg
    (fun w : Ext c.pt Y n ↦ (Ext.mk₀ q.inv).comp w (zero_add n)) hz'
  simpa [z', Ext.mk₀_comp_mk₀_assoc] using hrecover

end PfaffianDescent
