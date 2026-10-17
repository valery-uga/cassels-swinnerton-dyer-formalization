import PfaffianDescent.SectionRepresenterOver
import PfaffianDescent.SectionRepresenterCech
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Base change of formal-coproduct Cech nerves to an over-category

The right adjoint `Over.star X` preserves finite products.  Consequently,
applying it componentwise to a formal-coproduct Cech nerve agrees with first
applying it to the covering family and then forming the Cech nerve.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace PfaffianDescent

universe u

namespace FormalCoproduct

variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- Apply a functor componentwise to a formal coproduct. -/
@[simps]
def mapFunctor (F : C ⥤ D) :
    CategoryTheory.Limits.FormalCoproduct.{u} C ⥤
      CategoryTheory.Limits.FormalCoproduct.{u} D where
  obj A := ⟨A.I, fun i ↦ F.obj (A.obj i)⟩
  map q := ⟨q.f, fun i ↦ F.map (q.φ i)⟩
  map_id A := by ext <;> simp
  map_comp f g := by ext <;> simp

end FormalCoproduct

variable {C : Type u} [SmallCategory C] [HasFiniteLimits C]

/-- Degreewise product comparison between the componentwise image of a Cech
nerve under `Over.star X` and the Cech nerve of the componentwise image. -/
noncomputable def formalCoproductStarCechIsoApp
    (X : C) (U : CategoryTheory.Limits.FormalCoproduct.{u} C)
    (n : SimplexCategoryᵒᵖ) :
    letI : HasFiniteProducts (Over X) :=
      CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
    ((FormalCoproduct.mapFunctor (Over.star X)).obj (U.cech.obj n)) ≅
      (((FormalCoproduct.mapFunctor (Over.star X)).obj U).cech.obj n) := by
  letI : HasFiniteProducts (Over X) :=
    CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
  exact CategoryTheory.Limits.FormalCoproduct.isoOfComponents (Equiv.refl _)
    (fun f ↦ PreservesProduct.iso (Over.star X) (U.obj ∘ f))

set_option backward.isDefEq.respectTransparency false in
/-- Applying `Over.star X` componentwise commutes with the entire Cech
simplicial object. -/
noncomputable def formalCoproductStarCechIso
    (X : C) (U : CategoryTheory.Limits.FormalCoproduct.{u} C) :
    letI : HasFiniteProducts (Over X) :=
      CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
    U.cech ⋙ FormalCoproduct.mapFunctor (Over.star X) ≅
      ((FormalCoproduct.mapFunctor (Over.star X)).obj U).cech := by
  letI : HasFiniteProducts (Over X) :=
    CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
  exact NatIso.ofComponents (formalCoproductStarCechIsoApp X U) (fun {a b} f ↦ by
    refine CategoryTheory.Limits.FormalCoproduct.hom_ext rfl ?_
    intro g
    apply Pi.hom_ext
    intro j
    simp [formalCoproductStarCechIsoApp, FormalCoproduct.mapFunctor,
      PreservesProduct.iso_hom,
      CategoryTheory.Limits.FormalCoproduct.isoOfComponents,
      CategoryTheory.Limits.FormalCoproduct.cech,
      CategoryTheory.Limits.FormalCoproduct.mapPower,
      CategoryTheory.Limits.FormalCoproduct.power, Category.assoc]
    let q := (SimplexCategory.Hom.toOrderHom f.unop).toFun
    have hL := Pi.lift_π
      (fun k : ToType b.unop ↦
        (Over.star X).map (Pi.π (U.obj ∘ g) (q k))) j
    have hR := piComparison_comp_π (Over.star X) (U.obj ∘ g) (q j)
    exact hL.trans hR.symm)

end PfaffianDescent
