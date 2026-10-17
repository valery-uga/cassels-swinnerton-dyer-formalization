import PfaffianDescent.ActualP3ThreeQuadricCubicGlobalIso

/-! SOURCE ONLY / UNVERIFIED. The actual sheaf multiplication on genuine
morphism-valued H0 is literal homogeneous polynomial multiplication. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => homogeneousSubmodule (Fin 4) K
local notation "base" => ambientToBase (R := K) (σ := Fin 4)

/-- Reading a composed genuine global section on the top open gives the
actual component map, without an externally chosen global-section model. -/
lemma actualGlobalSectionsTop_comp {X : Scheme.{u}} (a : X ⟶ Spec (.of K))
    {M N : X.Modules} (s : SchemeModuleGlobalSectionsOver a M) (φ : M ⟶ N) :
    schemeModuleGlobalSectionsLinearEquivOpenTop a N (s ≫ φ) =
      φ.val.app (op ⊤) (schemeModuleGlobalSectionsLinearEquivOpenTop a M s) := rfl

/-- Actual positive multiplication O(1)→O(3) on genuine H0 is q*p. -/
theorem p3ActualHomogeneousGlobal_quadric_mul (q : PS 2) (p : PS 1) :
    p3HomogeneousGlobalSectionLinearMap K 1 p ≫ positiveMulHomogeneous PS q 1 =
      p3HomogeneousGlobalSectionLinearMap K 3
        (⟨q.val * p.val, q.property.mul p.property⟩ : PS 3) := by
  let e1 := schemeModuleGlobalSectionsLinearEquivOpenTop base (positiveSheafOfModules PS 1)
  let e3 := schemeModuleGlobalSectionsLinearEquivOpenTop base (positiveSheafOfModules PS 3)
  apply e3.injective
  rw [actualGlobalSectionsTop_comp]
  change (positiveMulHomogeneous PS q 1).val.app (op ⊤)
    (e1 (e1.symm (p3HomogeneousTopSectionLinearMap K 1 p))) =
    e3 (e3.symm (p3HomogeneousTopSectionLinearMap K 3
      (⟨q.val * p.val, q.property.mul p.property⟩ : PS 3)))
  rw [e1.apply_symm_apply, e3.apply_symm_apply]
  apply Subtype.ext
  funext x
  change algebraMap (MvPolynomial (Fin 4) K) (PositiveFiber PS x.1) q.val *
    Localization.mk p.val (1 : (positivePointIdeal PS x.1).primeCompl) =
    Localization.mk (q.val * p.val) (1 : (positivePointIdeal PS x.1).primeCompl)
  rw [Localization.mk_one_eq_algebraMap, Localization.mk_one_eq_algebraMap]
  exact (map_mul (algebraMap (MvPolynomial (Fin 4) K) (PositiveFiber PS x.1))
    q.val p.val).symm

/-- Actual positive-one triple coordinates are the three actual projected
sections. -/
theorem p3ActualPositiveOneTripleHomogeneousEquiv_component
    (s : SchemeModuleGlobalSectionsOver base (⨁ (p3ActualPositiveOneTriple (K := K))))
    (r : Fin 3) :
    p3HomogeneousGlobalSectionLinearMap K 1
      (![ (p3ActualPositiveOneTripleHomogeneousEquiv s).1,
        (p3ActualPositiveOneTripleHomogeneousEquiv s).2.1,
        (p3ActualPositiveOneTripleHomogeneousEquiv s).2.2 ] r) =
      s ≫ biproduct.π (p3ActualPositiveOneTriple (K := K)) r := by
  fin_cases r <;>
    change (p3HomogeneousGlobalSectionsLinearEquiv K 1 (by decide))
      ((p3HomogeneousGlobalSectionsLinearEquiv K 1 (by decide)).symm _) = _ <;>
    exact (p3HomogeneousGlobalSectionsLinearEquiv K 1 (by decide)).apply_symm_apply _

universe v w

private lemma compose_three_rows
    {D : Type v} [Category.{w} D] [Preadditive D]
    {U V W N : D} (s : U ⟶ V)
    (a0 a1 a2 : V ⟶ W) (b0 b1 b2 : W ⟶ N) :
    s ≫ (a0 ≫ b0 + a1 ≫ b1 + a2 ≫ b2) =
      (s ≫ a0) ≫ b0 + (s ≫ a1) ≫ b1 + (s ≫ a2) ≫ b2 := by
  simp only [Preadditive.comp_add, Category.assoc]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual last sheaf row induces exactly the literal cubic sum map
on genuine H0, with the actual triple coordinates. -/
theorem p3ActualThreeQuadricPositiveSum_global (f g h : PS 2)
    (s : SchemeModuleGlobalSectionsOver base (⨁ (p3ActualPositiveOneTriple (K := K)))) :
    s ≫ biproduct.desc ![positiveMulHomogeneous PS f 1,
      positiveMulHomogeneous PS g 1, positiveMulHomogeneous PS h 1] =
    p3HomogeneousGlobalSectionLinearMap K 3
      (threeQuadricCubicIdealLinearMap f g h
        (p3ActualPositiveOneTripleHomogeneousEquiv s)).val := by
  let x := p3ActualPositiveOneTripleHomogeneousEquiv s
  have h0 : p3HomogeneousGlobalSectionLinearMap K 1 x.1 =
      s ≫ biproduct.π (p3ActualPositiveOneTriple (K := K)) 0 :=
    p3ActualPositiveOneTripleHomogeneousEquiv_component s 0
  have h1 : p3HomogeneousGlobalSectionLinearMap K 1 x.2.1 =
      s ≫ biproduct.π (p3ActualPositiveOneTriple (K := K)) 1 :=
    p3ActualPositiveOneTripleHomogeneousEquiv_component s 1
  have h2 : p3HomogeneousGlobalSectionLinearMap K 1 x.2.2 =
      s ≫ biproduct.π (p3ActualPositiveOneTriple (K := K)) 2 :=
    p3ActualPositiveOneTripleHomogeneousEquiv_component s 2
  have hp : (threeQuadricCubicIdealLinearMap f g h x).val =
      (⟨f.val * x.1.val, f.property.mul x.1.property⟩ : PS 3) +
      (⟨g.val * x.2.1.val, g.property.mul x.2.1.property⟩ : PS 3) +
      (⟨h.val * x.2.2.val, h.property.mul x.2.2.property⟩ : PS 3) := rfl
  change _ = p3HomogeneousGlobalSectionLinearMap K 3
    (threeQuadricCubicIdealLinearMap f g h x).val
  rw [hp, map_add, map_add, ← p3ActualHomogeneousGlobal_quadric_mul,
    ← p3ActualHomogeneousGlobal_quadric_mul, ← p3ActualHomogeneousGlobal_quadric_mul,
    h0, h1, h2]
  simp only [biproduct.desc_eq, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  exact compose_three_rows s
    (biproduct.π (p3ActualPositiveOneTriple (K := K)) 0)
    (biproduct.π (p3ActualPositiveOneTriple (K := K)) 1)
    (biproduct.π (p3ActualPositiveOneTriple (K := K)) 2)
    (positiveMulHomogeneous PS f 1)
    (positiveMulHomogeneous PS g 1)
    (positiveMulHomogeneous PS h 1)

end PfaffianDescent
