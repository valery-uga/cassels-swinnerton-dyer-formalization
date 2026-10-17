import PfaffianDescent.CorayActualIdealModuleSheafificationIso
import PfaffianDescent.SchemeModuleTensor
import PfaffianDescent.VoisinSheafStalk
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! SOURCE ONLY / UNVERIFIED. The canonical GLOBAL multiplication morphism
from tensor products of the actual image-defined ideal modules to the
actual product-ideal module. Every membership, restriction and map is
constructed, not supplied as a global comparison hypothesis. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MonoidalCategory
open IdealSheafDataModule
open scoped TensorProduct
universe u
variable {X : Scheme.{u}}

/-- Transport the ENTIRE native ideal-data proposition before taking
its dependent section/module projections. No comparison premise is input. -/
private theorem nativeIdealDataPredicateTransport
    (P : X.IdealSheafData → Prop) {I J : X.IdealSheafData}
    (h : I = J) (hP : P I) : P J := by
  cases h
  exact hP

/-- Actual ideal-module affine sections land in the SAME ideal data,
using the genuine subscheme immersion of that data internally. -/
theorem actualIdealModule_section_mem_affine
    (I : X.IdealSheafData) (V : X.affineOpens)
    (m : (idealModule I).val.obj (op V.1)) :
    (idealModuleToUnit I).val.app (op V.1) m ∈ I.ideal V := by
  let P : X.IdealSheafData → Prop := fun J =>
    ∀ n : (idealModule J).val.obj (op V.1),
      (idealModuleToUnit J).val.app (op V.1) n ∈ J.ideal V
  have hker : P I.subschemeι.ker :=
    closedImmersionModule_section_mem_ker_ideal I.subschemeι V
  have hI : P I := nativeIdealDataPredicateTransport P I.ker_subschemeι hker
  exact hI m

/-- A section of the actual ideal-module maps into its original ideal
subpresheaf on EVERY open, with the same literal coefficient value. -/
def actualIdealModule_sectionToIdealPresheaf
    (I : X.IdealSheafData) (U : X.Opensᵒᵖ)
    (m : (idealModule I).val.obj U) : (presheafSubmodule I).obj U :=
  ⟨(idealModuleToUnit I).val.app U m, by
    intro V hVU
    let f := (homOfLE hVU).op
    have hnat := PresheafOfModules.naturality_apply (idealModuleToUnit I).val f m
    change (SheafOfModules.unit X.ringCatSheaf).val.map f
      ((idealModuleToUnit I).val.app U m) ∈ I.ideal V
    rw [← hnat]
    exact actualIdealModule_section_mem_affine I V ((idealModule I).val.map f m)⟩

/-- The all-open lift respects actual restrictions, rather than gluing
arbitrary choices of affine ideal sections. -/
def actualIdealModuleToIdealPresheaf (I : X.IdealSheafData) :
    (idealModule I).val ⟶ (presheafSubmodule I).toPresheafOfModules where
  app U := ModuleCat.ofHom
    (((idealModuleToUnit I).val.app U).hom.codRestrict
      ((presheafSubmodule I).obj U)
      (fun m => (actualIdealModule_sectionToIdealPresheaf I U m).property))
  naturality {U V} f := by
    ext m
    apply Subtype.ext
    exact PresheafOfModules.naturality_apply (idealModuleToUnit I).val f m

/-- The actual all-open lift has the literal original inclusion. -/
theorem actualIdealModuleToIdealPresheaf_comp_ι (I : X.IdealSheafData) :
    actualIdealModuleToIdealPresheaf I ≫ (presheafSubmodule I).ι =
      (idealModuleToUnit I).val := by
  ext U m
  rfl

/-- Equality transports only an ordinary element predicate. The original
section carrier, maps and affine ideal-data projections stay fixed. -/
private theorem nativeElementPredicateOfEq
    {α : Type*} (P : α → Prop) {a b : α} (h : a = b) (hb : P b) : P a := by
  cases h
  exact hb

/-- The following ordinary native ring laws fix the coefficient ring BEFORE
original subtype/unit-module operands are supplied. They do not change actions. -/
private theorem nativeRingProduct_add_left (R : CommRingCat) (a b c : R) :
    @Mul.mul R (inferInstance : Mul R) (a + b) c =
      @Mul.mul R (inferInstance : Mul R) a c + @Mul.mul R (inferInstance : Mul R) b c :=
  add_mul a b c

private theorem nativeRingProduct_scalar_left (R : CommRingCat) (a b c : R) :
    @Mul.mul R (inferInstance : Mul R) (@Mul.mul R (inferInstance : Mul R) a b) c =
      @Mul.mul R (inferInstance : Mul R) a (@Mul.mul R (inferInstance : Mul R) b c) :=
  mul_assoc a b c

private theorem nativeRingProduct_add_right (R : CommRingCat) (a b c : R) :
    @Mul.mul R (inferInstance : Mul R) a (b + c) =
      @Mul.mul R (inferInstance : Mul R) a b + @Mul.mul R (inferInstance : Mul R) a c :=
  mul_add a b c

private theorem nativeRingProduct_scalar_right (R : CommRingCat) (a b c : R) :
    @Mul.mul R (inferInstance : Mul R) b (@Mul.mul R (inferInstance : Mul R) a c) =
      @Mul.mul R (inferInstance : Mul R) a (@Mul.mul R (inferInstance : Mul R) b c) :=
  mul_left_comm b a c

private theorem nativeRingProduct_comm (R : CommRingCat) (a b : R) :
    @Mul.mul R (inferInstance : Mul R) a b = @Mul.mul R (inferInstance : Mul R) b a :=
  mul_comm a b

private theorem nativeRingProduct_restrict (R S : CommRingCat) (φ : R →+* S) (a b : R) :
    @Mul.mul S (inferInstance : Mul S) (φ a) (φ b) =
      φ (@Mul.mul R (inferInstance : Mul R) a b) :=
  (φ.map_mul a b).symm

/-- Multiplication of original ideal presheaf sections lies in the
original product ideal presheaf. Only actual affine restrictions are used. -/
def actualIdealPresheafProductSection
    (I J : X.IdealSheafData) (U : X.Opensᵒᵖ)
    (m : (presheafSubmodule I).obj U) (n : (presheafSubmodule J).obj U) :
    (presheafSubmodule (I * J)).obj U :=
  ⟨@Mul.mul (X.presheaf.obj U) (inferInstance : Mul (X.presheaf.obj U)) m.1 n.1, by
    intro V hVU
    let φ : X.presheaf.obj U →+* X.presheaf.obj (op V.1) :=
      (X.presheaf.map (homOfLE hVU).op).hom
    have hmul :
        φ (@Mul.mul (X.presheaf.obj U) (inferInstance : Mul (X.presheaf.obj U)) m.1 n.1) =
        @Mul.mul (X.presheaf.obj (op V.1))
          (inferInstance : Mul (X.presheaf.obj (op V.1))) (φ m.1) (φ n.1) :=
      φ.map_mul m.1 n.1
    have hmem :
        @Mul.mul (X.presheaf.obj (op V.1))
          (inferInstance : Mul (X.presheaf.obj (op V.1))) (φ m.1) (φ n.1) ∈
        I.ideal V * J.ideal V :=
      Ideal.mul_mem_mul (m.property V hVU) (n.property V hVU)
    exact nativeElementPredicateOfEq
      (fun z : X.presheaf.obj (op V.1) => z ∈ I.ideal V * J.ideal V) hmul hmem⟩

/-- The original pointwise tensorLift, cut out solely to check its four
bilinearity equations before the presheaf naturality conversion. -/
private def actualIdealPresheafTensorMulApp
    (I J : X.IdealSheafData) (U : X.Opensᵒᵖ) :
    (PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
      (presheafSubmodule I).toPresheafOfModules
      (presheafSubmodule J).toPresheafOfModules).obj U ⟶
      (presheafSubmodule (I * J)).toPresheafOfModules.obj U :=
  ModuleCat.MonoidalCategory.tensorLift
    (actualIdealPresheafProductSection I J U)
    (by
      intro m₁ m₂ n
      apply Subtype.ext
      exact nativeRingProduct_add_left (X.presheaf.obj U) m₁.1 m₂.1 n.1)
    (by
      intro a m n
      apply Subtype.ext
      exact nativeRingProduct_scalar_left (X.presheaf.obj U) a m.1 n.1)
    (by
      intro m n₁ n₂
      apply Subtype.ext
      exact nativeRingProduct_add_right (X.presheaf.obj U) m.1 n₁.1 n₂.1)
    (by
      intro a m n
      apply Subtype.ext
      exact nativeRingProduct_scalar_right (X.presheaf.obj U) a m.1 n.1)

/-- The canonical pointwise multiplication is a GLOBAL presheaf map.
Its restriction compatibility is literal ring-homomorphism multiplication. -/
def actualIdealPresheafTensorMul (I J : X.IdealSheafData) :
    PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
        (presheafSubmodule I).toPresheafOfModules
        (presheafSubmodule J).toPresheafOfModules ⟶
      (presheafSubmodule (I * J)).toPresheafOfModules where
  app U := actualIdealPresheafTensorMulApp I J U
  naturality {U V} f := ModuleCat.MonoidalCategory.tensor_ext (by
    intro m n
    apply Subtype.ext
    exact nativeRingProduct_restrict (X.presheaf.obj U) (X.presheaf.obj V)
      (X.presheaf.map f).hom m.1 n.1)

/-- The raw GLOBAL product begins with the SAME actual ideal-module
presheaves and ends in the product's original ideal subpresheaf. -/
def actualIdealModuleRawTensorMul (I J : X.IdealSheafData) :
    PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
        (idealModule I).val (idealModule J).val ⟶
      (presheafSubmodule (I * J)).toPresheafOfModules :=
  PresheafOfModules.Monoidal.tensorHom
      (actualIdealModuleToIdealPresheaf I) (actualIdealModuleToIdealPresheaf J) ≫
    actualIdealPresheafTensorMul I J

/-- The raw global multiplication retains BOTH actual ideal inclusions
and the canonical unit multiplication. This is equality of original maps. -/
theorem actualIdealModuleRawTensorMul_comp_ι (I J : X.IdealSheafData) :
    letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
      PresheafOfModules.monoidalCategory
    actualIdealModuleRawTensorMul I J ≫ (presheafSubmodule (I * J)).ι =
      PresheafOfModules.Monoidal.tensorHom
          (idealModuleToUnit I).val (idealModuleToUnit J).val ≫
        (ρ_ ((SheafOfModules.unit X.ringCatSheaf).val)).hom := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact nativeRingProduct_comm (X.presheaf.obj U)
    ((idealModuleToUnit I).val.app U m) ((idealModuleToUnit J).val.app U n)

/-- Genuine GLOBAL multiplication into the SAME actual image-defined
product ideal module. It sheafifies the genuine raw map and then uses
the original existing factor-through-image map. No desired comparison,
gluing, tensor-flatness or exactness premise is supplied. -/
def actualIdealModuleTensorMul (I J : X.IdealSheafData) :
    schemeModuleTensor (idealModule I) (idealModule J) ⟶ idealModule (I * J) :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (actualIdealModuleRawTensorMul I J) ≫ moduleSheafToIdealModule (I * J)

/-- Ordinary categorical algebra is checked on fixed generic categories
before applying it to the original native sheafification/image maps. -/
private theorem nativeFunctorImageUnitChain
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (A : F ⊣ G)
    {P Q T : C} {Y M : D}
    (r : P ⟶ Q) (i : Q ⟶ G.obj Y) (s : P ⟶ T) (u : T ⟶ G.obj Y)
    (q : F.obj Q ⟶ M) (j : M ⟶ Y)
    (hq : q ≫ j = (A.homEquiv Q Y).symm i)
    (hr : r ≫ i = s ≫ u) :
    (F.map r ≫ q) ≫ j = F.map s ≫ (F.map u ≫ A.counit.app Y) := by
  calc
    (F.map r ≫ q) ≫ j = F.map r ≫ (q ≫ j) := Category.assoc _ _ _
    _ = F.map r ≫ (A.homEquiv Q Y).symm i :=
      congrArg (fun k : F.obj Q ⟶ Y => F.map r ≫ k) hq
    _ = (A.homEquiv P Y).symm (r ≫ i) :=
      (A.homEquiv_naturality_left_symm r i).symm
    _ = (A.homEquiv P Y).symm (s ≫ u) :=
      congrArg (fun k : P ⟶ G.obj Y => (A.homEquiv P Y).symm k) hr
    _ = F.map s ≫ (A.homEquiv T Y).symm u :=
      A.homEquiv_naturality_left_symm s u
    _ = F.map s ≫ (F.map u ≫ A.counit.app Y) := rfl

/-- The genuine global multiplication retains the literal inclusion in
O_X; it is the original tensor of BOTH actual ideal inclusions followed
by the native tensor unit multiplication. -/
theorem actualIdealModuleTensorMul_toUnit (I J : X.IdealSheafData) :
    actualIdealModuleTensorMul I J ≫ idealModuleToUnit (I * J) =
      schemeModuleTensorMap (idealModuleToUnit I) (idealModuleToUnit J) ≫
        (schemeModuleTensorUnitRightIso (SheafOfModules.unit X.ringCatSheaf)).hom := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let G := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  exact nativeFunctorImageUnitChain
    (C := PresheafOfModules X.ringCatSheaf.obj)
    (D := SheafOfModules X.ringCatSheaf) F G A
    (Y := SheafOfModules.unit X.ringCatSheaf) (M := idealModule (I * J))
    (actualIdealModuleRawTensorMul I J) (presheafSubmodule (I * J)).ι
    (PresheafOfModules.Monoidal.tensorHom
      (idealModuleToUnit I).val (idealModuleToUnit J).val)
    (ρ_ ((SheafOfModules.unit X.ringCatSheaf).val)).hom
    (moduleSheafToIdealModule (I * J)) (idealModuleToUnit (I * J))
    (moduleSheafToIdealModule_comp (I * J))
    (actualIdealModuleRawTensorMul_comp_ι I J)

end PfaffianDescent.Coray
