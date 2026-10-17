import PfaffianDescent.FlatAffineIdealModuleSheaf
import PfaffianDescent.AffineQuotientPushforwardTilde

/-! The flat affine quotient-kernel map as a map to the actual ideal module. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

/-- The flat base-change equivalence identifies its composite with the
kernel inclusion with the canonical multiplication map from the tensor
product of the original ideal. -/
theorem flatBaseChangeQuotientKernelLinearEquiv_subtype
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    (RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom).subtype.comp
      (flatBaseChangeQuotientKernelLinearEquiv g hg I).toLinearMap =
        idealBaseChangeLinearMap g I := by
  letI : Algebra A B := g.toAlgebra
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b y =>
      exact flatBaseChangeQuotientKernelLinearEquiv_tmul g hg I b y |>.trans
        (idealBaseChangeLinearMap_tmul g I b y).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The sheafified flat base-change comparison respects inclusion into
the ambient affine structure sheaf. -/
theorem flatBaseChangeQuotientKernelTildeIso_hom_subtype
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (flatBaseChangeQuotientKernelTildeIso g hg I).hom ≫
      (tilde.functor (CommRingCat.of B)).map (ModuleCat.ofHom K.subtype) =
        (tilde.functor (CommRingCat.of B)).map
          (ModuleCat.ofHom (idealBaseChangeLinearMap g I)) := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let F := tilde.functor (CommRingCat.of B)
  let e := flatBaseChangeQuotientKernelLinearEquiv g hg I
  let m := ModuleCat.ofHom e.toLinearMap
  have hm : m ≫ ModuleCat.ofHom K.subtype =
      ModuleCat.ofHom (idealBaseChangeLinearMap g I) := by
    apply ModuleCat.hom_ext
    exact flatBaseChangeQuotientKernelLinearEquiv_subtype g hg I
  change F.map m ≫ F.map (ModuleCat.ofHom K.subtype) =
    F.map (ModuleCat.ofHom (idealBaseChangeLinearMap g I))
  rw [← F.map_comp, hm]

/-- On the base-changed affine scheme, the tensor extension of the original
ideal is the actual ideal module of the quotient by the base-changed kernel. -/
noncomputable def flatBaseChangeTensorActualIdealModuleIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (tilde.functor (CommRingCat.of B)).obj (ModuleCat.of B (B ⊗[A] I)) ≅
      IdealSheafDataModule.closedImmersionModule
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  exact flatBaseChangeQuotientKernelTildeIso g hg I ≪≫
    affineQuotientIdealTildeClosedImmersionModuleIso K

/-- The tensor-extended ideal maps into the base-changed structure sheaf
by the canonical multiplication map under the actual ideal-module
comparison. -/
theorem flatBaseChangeTensorActualIdealModuleIso_hom_toUnit
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    let φ := CommRingCat.ofHom (Ideal.Quotient.mk K)
    (flatBaseChangeTensorActualIdealModuleIso g hg I).hom ≫
      IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ) =
        (tilde.functor (CommRingCat.of B)).map
          (ModuleCat.ofHom (idealBaseChangeLinearMap g I)) ≫
            (affineGlobalSectionsUnitTildeIso (A := B)).hom := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let φ := CommRingCat.ofHom (Ideal.Quotient.mk K)
  let F := tilde.functor (CommRingCat.of B)
  let e₁ := flatBaseChangeQuotientKernelTildeIso g hg I
  let e₂ := affineQuotientIdealTildeClosedImmersionModuleIso K
  let u := (affineGlobalSectionsUnitTildeIso (A := B)).hom
  let i := IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ)
  have h₂ : e₂.hom ≫ i = F.map (ModuleCat.ofHom K.subtype) ≫ u :=
    affineQuotientIdealTildeClosedImmersionModuleIso_hom_toUnit K
  have h₁ : e₁.hom ≫ F.map (ModuleCat.ofHom K.subtype) =
      F.map (ModuleCat.ofHom (idealBaseChangeLinearMap g I)) :=
    flatBaseChangeQuotientKernelTildeIso_hom_subtype g hg I
  change (e₁.hom ≫ e₂.hom) ≫ i =
    F.map (ModuleCat.ofHom (idealBaseChangeLinearMap g I)) ≫ u
  calc
    (e₁.hom ≫ e₂.hom) ≫ i = e₁.hom ≫ (e₂.hom ≫ i) :=
      Category.assoc _ _ _
    _ = e₁.hom ≫ (F.map (ModuleCat.ofHom K.subtype) ≫ u) :=
      congrArg (fun h => e₁.hom ≫ h) h₂
    _ = (e₁.hom ≫ F.map (ModuleCat.ofHom K.subtype)) ≫ u :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun h => h ≫ u) h₁

end PfaffianDescent
