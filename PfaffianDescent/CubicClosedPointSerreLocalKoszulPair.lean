import PfaffianDescent.CubicClosedPointSerreLocalKoszulRepresenter
import PfaffianDescent.SheafModulePushforwardExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Actual two-unit coordinates for the restricted Koszul middle term -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
universe u

def cubicClosedPointSerreLocalKoszulFinPairIso
    {C : Type u} [Category C] [Preadditive C] [HasFiniteBiproducts C]
    [HasBinaryBiproducts C] (A : C) :
    (⨁ fun _ : Fin 2 => A) ≅ (A ⊞ A) where
  hom := biprod.lift (biproduct.π (fun _ : Fin 2 => A) 0)
    (biproduct.π (fun _ : Fin 2 => A) 1)
  inv := biprod.desc (biproduct.ι (fun _ : Fin 2 => A) 0)
    (biproduct.ι (fun _ : Fin 2 => A) 1)
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro j
    fin_cases j <;> simp
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext <;> simp
    · apply biprod.hom_ext <;> simp

def cubicClosedPointSerreLocalKoszulPairUnitIso
    {X : Scheme.{u}} (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).obj
      (show X.Modules from ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U) ≅
      (SheafOfModules.unit (U : Scheme).ringCatSheaf ⊞
        SheafOfModules.unit (U : Scheme).ringCatSheaf) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  letI : F.Additive := { map_add := by intro A B f g; ext V m; rfl }
  letI : PreservesFiniteLimits F := restrictFunctor_preservesFiniteLimits U.ι
  exact F.mapBiproduct (sectionRepresenterKoszulPair X.ringCatSheaf U) ≪≫
    biproduct.mapIso (fun _ => cubicClosedPointSerreLocalKoszulRepresenterUnitIso U) ≪≫
    cubicClosedPointSerreLocalKoszulFinPairIso _

@[reassoc]
theorem cubicClosedPointSerreLocalKoszulPairUnitIso_hom_fst
    {X : Scheme.{u}} (U : X.Opens) :
    (cubicClosedPointSerreLocalKoszulPairUnitIso U).hom ≫ biprod.fst =
      (Scheme.Modules.restrictFunctor U.ι).map
        (biproduct.π (sectionRepresenterKoszulPair X.ringCatSheaf U) 0) ≫
        (cubicClosedPointSerreLocalKoszulRepresenterUnitIso U).hom := by
  simp [cubicClosedPointSerreLocalKoszulPairUnitIso,
    cubicClosedPointSerreLocalKoszulFinPairIso, Functor.mapBiproduct_hom,
    Functor.biproductComparison_π]

@[reassoc]
theorem cubicClosedPointSerreLocalKoszulPairUnitIso_hom_snd
    {X : Scheme.{u}} (U : X.Opens) :
    (cubicClosedPointSerreLocalKoszulPairUnitIso U).hom ≫ biprod.snd =
      (Scheme.Modules.restrictFunctor U.ι).map
        (biproduct.π (sectionRepresenterKoszulPair X.ringCatSheaf U) 1) ≫
        (cubicClosedPointSerreLocalKoszulRepresenterUnitIso U).hom := by
  simp [cubicClosedPointSerreLocalKoszulPairUnitIso,
    cubicClosedPointSerreLocalKoszulFinPairIso, Functor.mapBiproduct_hom,
    Functor.biproductComparison_π]

@[reassoc]
theorem cubicClosedPointSerreLocalKoszulPairUnitIso_inl_inv
    {X : Scheme.{u}} (U : X.Opens) :
    biprod.inl ≫ (cubicClosedPointSerreLocalKoszulPairUnitIso U).inv =
      (cubicClosedPointSerreLocalKoszulRepresenterUnitIso U).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map
          (biproduct.ι (sectionRepresenterKoszulPair X.ringCatSheaf U) 0) := by
  simp [cubicClosedPointSerreLocalKoszulPairUnitIso,
    cubicClosedPointSerreLocalKoszulFinPairIso, Functor.mapBiproduct_inv]

@[reassoc]
theorem cubicClosedPointSerreLocalKoszulPairUnitIso_inr_inv
    {X : Scheme.{u}} (U : X.Opens) :
    biprod.inr ≫ (cubicClosedPointSerreLocalKoszulPairUnitIso U).inv =
      (cubicClosedPointSerreLocalKoszulRepresenterUnitIso U).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map
          (biproduct.ι (sectionRepresenterKoszulPair X.ringCatSheaf U) 1) := by
  simp [cubicClosedPointSerreLocalKoszulPairUnitIso,
    cubicClosedPointSerreLocalKoszulFinPairIso, Functor.mapBiproduct_inv]

/-- The actual restricted scalar map in the canonical unit coordinate. -/
def cubicClosedPointSerreLocalKoszulScalar
    {X : Scheme.{u}} (U : X.Opens) (a : Γ(X, U)) :
    SheafOfModules.unit (U : Scheme).ringCatSheaf ⟶
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
  (cubicClosedPointSerreLocalKoszulRepresenterUnitIso U).inv ≫
    (Scheme.Modules.restrictFunctor U.ι).map
      (sectionRepresenterScalarEndomorphism X.ringCatSheaf U a) ≫
    (cubicClosedPointSerreLocalKoszulRepresenterUnitIso U).hom

/-- The actual restricted first Koszul map on two copies of the unit. -/
def cubicClosedPointSerreLocalKoszulFirst
    {X : Scheme.{u}} (U : X.Opens) (q f : Γ(X, U)) :
    SheafOfModules.unit (U : Scheme).ringCatSheaf ⟶
      (SheafOfModules.unit (U : Scheme).ringCatSheaf ⊞
        SheafOfModules.unit (U : Scheme).ringCatSheaf) :=
  (cubicClosedPointSerreLocalKoszulRepresenterUnitIso U).inv ≫
    (Scheme.Modules.restrictFunctor U.ι).map
      (sectionRepresenterKoszulFirst X.ringCatSheaf U q f) ≫
    (cubicClosedPointSerreLocalKoszulPairUnitIso U).hom

theorem cubicClosedPointSerreLocalKoszulFirst_eq_lift
    {X : Scheme.{u}} (U : X.Opens) (q f : Γ(X, U)) :
    cubicClosedPointSerreLocalKoszulFirst U q f =
      biprod.lift (cubicClosedPointSerreLocalKoszulScalar U (-f))
        (cubicClosedPointSerreLocalKoszulScalar U q) := by
  apply biprod.hom_ext
  · rw [cubicClosedPointSerreLocalKoszulFirst, Category.assoc, Category.assoc,
      cubicClosedPointSerreLocalKoszulPairUnitIso_hom_fst]
    simp only [← Functor.map_comp_assoc, sectionRepresenterKoszulFirst,
      biproduct.lift_π, Matrix.cons_val_zero, biprod.lift_fst,
      cubicClosedPointSerreLocalKoszulScalar]
  · rw [cubicClosedPointSerreLocalKoszulFirst, Category.assoc, Category.assoc,
      cubicClosedPointSerreLocalKoszulPairUnitIso_hom_snd]
    simp only [← Functor.map_comp_assoc, sectionRepresenterKoszulFirst,
      biproduct.lift_π, Matrix.cons_val_one, Matrix.cons_val_zero, biprod.lift_snd,
      cubicClosedPointSerreLocalKoszulScalar]

end PfaffianDescent
