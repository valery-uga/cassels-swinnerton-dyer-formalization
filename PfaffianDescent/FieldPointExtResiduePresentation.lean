import PfaffianDescent.FieldPointExtCoordinate

/-! # Residue data for constructed field-point Ext coordinates

This records the actual local complete-intersection presentation used by an
Ext coordinate. Existence of the record is proved for the coordinate constructors;
it is not an additional geometric hypothesis.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open scoped nonZeroDivisors
namespace PfaffianDescent
universe u

/-- Actual local data realizing the forward map of a field-point Ext coordinate. -/
structure FieldPointExtResiduePresentation
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i] (x : Spec (.of L))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (M N : X.Modules) (e : Ext.{u} M N 2 ≃+ L) where
  f : X.presheaf.stalk (i x)
  g : X.presheaf.stalk (i x)
  hf : f ∈ (X.presheaf.stalk (i x))⁰
  hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
    ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰
  hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x))
  hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x))
  qM : (schemeModuleStalkModuleFunctor X (i x)).obj M ≅
    ModuleCat.of (X.presheaf.stalk (i x))
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _))
  qN : (schemeModuleStalkModuleFunctor X (i x)).obj N ≅
    ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x))
  coordinate_eq : ∀ z, e z =
    fieldPointExtTwoResidueCoordinate i x M N f g hf hg hfm hgm qM qN z

set_option backward.isDefEq.respectTransparency false in
theorem fieldPointExtTwoCoordinateAddEquivOfLocalTrivialization_residuePresentation
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (x : Spec (.of L)) (T : X.Modules) (U : X.Opens) (hxU : i x ∈ U)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i x)))]
    (N : X.Modules) (f g : X.presheaf.stalk (i x))
    (hf : f ∈ (X.presheaf.stalk (i x))⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈
      ((X.presheaf.stalk (i x)) ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (qM : (schemeModuleStalkModuleFunctor X (i x)).obj (schemeModuleTensor ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T) ≅
      ModuleCat.of (X.presheaf.stalk (i x))
        ((X.presheaf.stalk (i x)) ⧸ Ideal.span ({f, g} : Set _)))
    (qN : (schemeModuleStalkModuleFunctor X (i x)).obj N ≅
      ModuleCat.of (X.presheaf.stalk (i x)) (X.presheaf.stalk (i x)))
    (hspan : Ideal.span ({f, g} : Set (X.presheaf.stalk (i x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i x)))
    (hstalk : Function.Injective
      (schemeModuleStalkModuleExtMap X (i x) (schemeModuleTensor ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T) N 2))
    (z : Ext.{u} (schemeModuleTensor ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T) N 2)
    (hz : z ≠ 0) :
    Nonempty (FieldPointExtResiduePresentation i x
      (schemeModuleTensor ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) T) N
      (fieldPointExtTwoCoordinateAddEquivOfLocalTrivialization
        i x T U hxU eT N f g hf hg hfm hgm qM qN hspan hstalk z hz)) := by
  refine ⟨{
    f := f
    g := g
    hf := hf
    hg := hg
    hfm := hfm
    hgm := hgm
    qM := qM
    qN := qN
    coordinate_eq := ?_ }⟩
  intro w
  rfl

end PfaffianDescent
