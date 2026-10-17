import PfaffianDescent.FiniteProductTildeDecomposition
import PfaffianDescent.FiniteSupportExtComponents
import PfaffianDescent.SchemeIsoPushforwardUnit
import PfaffianDescent.FiniteEtaleSchemeFrobenius
import Mathlib.RingTheory.Etale.Field

/-!
# Point decomposition of a finite étale structure sheaf

A finite étale algebra is a finite product of finite separable fields.  This
file transports the product-ring sheaf decomposition through an arbitrary
algebra equivalence and then records the resulting decomposition for every
finite étale algebra.
-/

noncomputable section

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
variable {J : Type u} [Fintype J]
variable (L : J → Type u) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]

/-- The scheme isomorphism contravariantly induced by an algebra
equivalence from `A` to a finite product. -/
noncomputable def productAlgEquivSpecIso
    (e : A ≃ₐ[K] (∀ i, L i)) :
    Spec (.of (∀ i, L i)) ≅ Spec (.of A) :=
  Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op

/-- The coordinate-point summand in the ambient scheme after transporting a
product presentation of the finite algebra. -/
noncomputable abbrev productAlgEquivCoordinatePointPushforwardToAmbient
    {X : Scheme.{u}} (e : A ≃ₐ[K] (∀ i, L i))
    (j : Spec (.of A) ⟶ X) (i : J) : X.Modules :=
  productCoordinatePointPushforwardToAmbient L
    ((productAlgEquivSpecIso L e).hom ≫ j) i

set_option backward.isDefEq.respectTransparency false in
/-- A product presentation of a finite algebra decomposes its pushed-forward
structure sheaf into the biproduct of the field-point pushforwards. -/
noncomputable def productAlgEquivPointPushforwardBiproductIso
    {X : Scheme.{u}} (e : A ≃ₐ[K] (∀ i, L i))
    (j : Spec (.of A) ⟶ X) :
    (⨁ fun i ↦
      productAlgEquivCoordinatePointPushforwardToAmbient L e j i) ≅
      (Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit.{u} (Spec (.of A)).ringCatSheaf) := by
  let s := productAlgEquivSpecIso L e
  let Oprod := SheafOfModules.unit.{u}
    (Spec (.of (∀ i, L i))).ringCatSheaf
  exact
    productCoordinatePointPushforwardToAmbientBiproductIso
        L (s.hom ≫ j) ≪≫
      ((Scheme.Modules.pushforwardComp s.hom j).app Oprod).symm ≪≫
      (Scheme.Modules.pushforward j).mapIso
        (schemeIsoPushforwardUnitIso s)

/-- The same product decomposition after identifying `Spec A` with an
arbitrary scheme `Z`.  This is the form used for the canonical affine
presentation of a finite scheme. -/
noncomputable def productAlgEquivPointPushforwardBiproductIsoOfSpecIso
    {Z X : Scheme.{u}} (s : Spec (.of A) ≅ Z)
    (e : A ≃ₐ[K] (∀ i, L i)) (j : Z ⟶ X) :
    (⨁ fun i ↦
      productAlgEquivCoordinatePointPushforwardToAmbient
        L e (s.hom ≫ j) i) ≅
      (Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit.{u} Z.ringCatSheaf) := by
  let OA := SheafOfModules.unit.{u} (Spec (.of A)).ringCatSheaf
  exact
    productAlgEquivPointPushforwardBiproductIso L e (s.hom ≫ j) ≪≫
      ((Scheme.Modules.pushforwardComp s.hom j).app OA).symm ≪≫
      (Scheme.Modules.pushforward j).mapIso
        (schemeIsoPushforwardUnitIso s)

/-- Pointwise Ext coordinates assemble across the product presentation into
coordinates in the product algebra. -/
noncomputable def productAlgEquivExtCoordinateAddEquivOfSpecIso
    {Z X : Scheme.{u}} (s : Spec (.of A) ≅ Z)
    (e : A ≃ₐ[K] (∀ i, L i)) (j : Z ⟶ X)
    [HasExt.{u} X.Modules] (Y : X.Modules)
    (coordinate : ∀ i,
      CategoryTheory.Abelian.Ext
          (productAlgEquivCoordinatePointPushforwardToAmbient
            L e (s.hom ≫ j) i) Y 2 ≃+
        L i) :
    CategoryTheory.Abelian.Ext
        ((Scheme.Modules.pushforward j).obj
          (SheafOfModules.unit.{u} Z.ringCatSheaf)) Y 2 ≃+
      (∀ i, L i) :=
  extIsoBiproductCoordinateAddEquiv
    (biproduct.isBilimit
      (fun i ↦ productAlgEquivCoordinatePointPushforwardToAmbient
        L e (s.hom ≫ j) i))
    (productAlgEquivPointPushforwardBiproductIsoOfSpecIso L s e j)
    2 coordinate

/-- The assembled pointwise Ext coordinates, transported back from the
chosen product presentation to the original finite algebra. -/
noncomputable def productAlgEquivExtCoordinateAlgebraAddEquivOfSpecIso
    {Z X : Scheme.{u}} (s : Spec (.of A) ≅ Z)
    (e : A ≃ₐ[K] (∀ i, L i)) (j : Z ⟶ X)
    [HasExt.{u} X.Modules] (Y : X.Modules)
    (coordinate : ∀ i,
      CategoryTheory.Abelian.Ext
          (productAlgEquivCoordinatePointPushforwardToAmbient
            L e (s.hom ≫ j) i) Y 2 ≃+
        L i) :
    CategoryTheory.Abelian.Ext
        ((Scheme.Modules.pushforward j).obj
          (SheafOfModules.unit.{u} Z.ringCatSheaf)) Y 2 ≃+ A :=
  (productAlgEquivExtCoordinateAddEquivOfSpecIso
      L s e j Y coordinate).trans e.symm.toLinearEquiv.toAddEquiv

/-- Every finite étale algebra admits a finite field-point decomposition of
its pushed-forward structure sheaf in any ambient scheme.  The factors retain
their finiteness and separability over the ground field for the subsequent
local complete-intersection calculation. -/
theorem finiteEtale_exists_pointPushforwardBiproductIso
    [Algebra.Etale K A] {X : Scheme.{u}} (j : Spec (.of A) ⟶ X) :
    ∃ (I : Type u) (_ : Fintype I) (Ai : I → Type u)
      (_ : ∀ i, Field (Ai i)) (_ : ∀ i, Algebra K (Ai i))
      (_ : ∀ i, FiniteDimensional K (Ai i))
      (_ : ∀ i, Algebra.IsSeparable K (Ai i))
      (e : A ≃ₐ[K] (∀ i, Ai i)),
      Nonempty
        ((⨁ fun i ↦
          productAlgEquivCoordinatePointPushforwardToAmbient Ai e j i) ≅
          (Scheme.Modules.pushforward j).obj
            (SheafOfModules.unit.{u} (Spec (.of A)).ringCatSheaf)) := by
  classical
  obtain ⟨I, hI, Ai, hfield, halgebra, e, hfinite⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  letI : Finite I := hI
  letI : Fintype I := Fintype.ofFinite I
  letI : ∀ i, Field (Ai i) := hfield
  letI : ∀ i, Algebra K (Ai i) := halgebra
  letI : ∀ i, FiniteDimensional K (Ai i) := fun i => (hfinite i).1
  letI : ∀ i, Algebra.IsSeparable K (Ai i) := fun i => (hfinite i).2
  exact ⟨I, inferInstance, Ai, inferInstance, inferInstance,
    inferInstance, inferInstance, e,
    ⟨productAlgEquivPointPushforwardBiproductIso Ai e j⟩⟩

/-- Scheme-facing finite étale decomposition.  An affine presentation of
`Z` by a finite étale coordinate algebra produces a biproduct of finite
separable field-point sheaves whose total object is `j_* O_Z`. -/
theorem finiteEtale_exists_pointPushforwardBiproductIsoOfSpecIso
    [Algebra.Etale K A] {Z X : Scheme.{u}}
    (s : Spec (.of A) ≅ Z) (j : Z ⟶ X) :
    ∃ (I : Type u) (_ : Fintype I) (Ai : I → Type u)
      (_ : ∀ i, Field (Ai i)) (_ : ∀ i, Algebra K (Ai i))
      (_ : ∀ i, FiniteDimensional K (Ai i))
      (_ : ∀ i, Algebra.IsSeparable K (Ai i))
      (e : A ≃ₐ[K] (∀ i, Ai i)),
      Nonempty
        ((⨁ fun i ↦
          productAlgEquivCoordinatePointPushforwardToAmbient
            Ai e (s.hom ≫ j) i) ≅
          (Scheme.Modules.pushforward j).obj
            (SheafOfModules.unit.{u} Z.ringCatSheaf)) := by
  classical
  obtain ⟨I, hI, Ai, hfield, halgebra, e, hfinite⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  letI : Finite I := hI
  letI : Fintype I := Fintype.ofFinite I
  letI : ∀ i, Field (Ai i) := hfield
  letI : ∀ i, Algebra K (Ai i) := halgebra
  letI : ∀ i, FiniteDimensional K (Ai i) := fun i => (hfinite i).1
  letI : ∀ i, Algebra.IsSeparable K (Ai i) := fun i => (hfinite i).2
  exact ⟨I, inferInstance, Ai, inferInstance, inferInstance,
    inferInstance, inferInstance, e,
    ⟨productAlgEquivPointPushforwardBiproductIsoOfSpecIso Ai s e j⟩⟩

/-- The actual structure sheaf of a finite étale scheme, pushed into any
ambient scheme, is a finite biproduct of sheaves pushed from finite separable
field points.  All affine-presentation and algebra-decomposition choices are
returned explicitly. -/
theorem finiteEtaleScheme_exists_pointPushforwardBiproductIso
    {Z X : Scheme.{u}} (f : Z ⟶ Spec (.of K)) [IsFinite f] [Etale f]
    (j : Z ⟶ X) :
    letI := finiteSchemeCoefficientAlgebra f
    ∃ (s : Spec (.of Γ(Z, ⊤)) ≅ Z)
      (I : Type u) (_ : Fintype I) (Ai : I → Type u)
      (_ : ∀ i, Field (Ai i)) (_ : ∀ i, Algebra K (Ai i))
      (_ : ∀ i, FiniteDimensional K (Ai i))
      (_ : ∀ i, Algebra.IsSeparable K (Ai i))
      (e : Γ(Z, ⊤) ≃ₐ[K] (∀ i, Ai i)),
      Nonempty
        ((⨁ fun i ↦
          productAlgEquivCoordinatePointPushforwardToAmbient
            Ai e (s.hom ≫ j) i) ≅
          (Scheme.Modules.pushforward j).obj
            (SheafOfModules.unit.{u} Z.ringCatSheaf)) := by
  letI : IsAffine Z := isAffine_of_isAffineHom f
  letI := finiteSchemeCoefficientAlgebra f
  haveI : Algebra.Etale K Γ(Z, ⊤) :=
    finiteEtaleScheme_coordinateAlgebra_etale f
  let s : Spec (.of Γ(Z, ⊤)) ≅ Z := Z.isoSpec.symm
  refine ⟨s, ?_⟩
  exact finiteEtale_exists_pointPushforwardBiproductIsoOfSpecIso s j

end PfaffianDescent
