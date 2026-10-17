import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSplitLocalKernel
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.RingHom.Etale

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_markedStalkBaseMap
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (j : Y ⟶ Z)
    (hj : j ≫ g = 𝟙 Y) (y : Y) :
    Y.presheaf.stalk y →+* Z.presheaf.stalk (j y) :=
  ((Y.presheaf.stalkCongr (.of_eq (show g (j y) = y from
    congrArg (fun f : Y ⟶ Y => f y) hj))).inv ≫ g.stalkMap (j y)).hom

theorem cubicClosedPointSerreFiniteZeroResidual_markedStalk_retraction
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (j : Y ⟶ Z)
    (hj : j ≫ g = 𝟙 Y) (y : Y) :
    (j.stalkMap y).hom.comp
      (cubicClosedPointSerreFiniteZeroResidual_markedStalkBaseMap g j hj y) =
        RingHom.id (Y.presheaf.stalk y) := by
  have h := Scheme.Hom.stalkMap_congr_hom (j ≫ g) (𝟙 Y) hj y
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_id] at h
  change g.stalkMap (j y) ≫ j.stalkMap y =
    (Y.presheaf.stalkCongr (.of_eq (show g (j y) = y from
      congrArg (fun f : Y ⟶ Y => f y) hj))).hom ≫ 𝟙 _ at h
  simp only [Category.comp_id] at h
  unfold cubicClosedPointSerreFiniteZeroResidual_markedStalkBaseMap
  rw [← CommRingCat.hom_comp, Category.assoc, h]
  simp

theorem cubicClosedPointSerreFiniteZeroResidual_markedStalk_kernel_of_field_fiber
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (j : Y ⟶ Z)
    (hj : j ≫ g = 𝟙 Y) (y : Y)
    [IsNoetherianRing (Z.presheaf.stalk (j y))]
    (hf : IsField (Z.presheaf.stalk (j y) ⧸
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).map
        (cubicClosedPointSerreFiniteZeroResidual_markedStalkBaseMap g j hj y))) :
    RingHom.ker (j.stalkMap y).hom = ⊥ := by
  let b := cubicClosedPointSerreFiniteZeroResidual_markedStalkBaseMap g j hj y
  letI : Algebra (Y.presheaf.stalk y) (Z.presheaf.stalk (j y)) := b.toAlgebra
  let q : Z.presheaf.stalk (j y) →ₐ[Y.presheaf.stalk y] Y.presheaf.stalk y :=
    { __ := (j.stalkMap y).hom
      commutes' := fun r => RingHom.congr_fun
        (cubicClosedPointSerreFiniteZeroResidual_markedStalk_retraction g j hj y) r }
  letI : IsLocalHom q.toRingHom := by
    change IsLocalHom (j.stalkMap y).hom
    infer_instance
  have hm : (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).map
      (algebraMap (Y.presheaf.stalk y) (Z.presheaf.stalk (j y))) =
        IsLocalRing.maximalIdeal (Z.presheaf.stalk (j y)) := by
    apply IsLocalRing.eq_maximalIdeal
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hf
  exact cubicClosedPointSerreFiniteZeroResidual_splitLocal_kernel_eq_bot q hm

theorem cubicClosedPointSerreFiniteZeroResidual_markedStalk_etale_of_field_fiber
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) (j : Y ⟶ Z)
    (hj : j ≫ g = 𝟙 Y) (y : Y)
    [IsNoetherianRing (Z.presheaf.stalk (j y))]
    (hf : IsField (Z.presheaf.stalk (j y) ⧸
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).map
        (cubicClosedPointSerreFiniteZeroResidual_markedStalkBaseMap g j hj y))) :
    (g.stalkMap (j y)).hom.Etale := by
  let b := cubicClosedPointSerreFiniteZeroResidual_markedStalkBaseMap g j hj y
  let q := (j.stalkMap y).hom
  have hq : Function.Injective q := (RingHom.injective_iff_ker_eq_bot q).mpr
    (cubicClosedPointSerreFiniteZeroResidual_markedStalk_kernel_of_field_fiber g j hj y hf)
  have hqb : Function.LeftInverse q b := fun r => RingHom.congr_fun
    (cubicClosedPointSerreFiniteZeroResidual_markedStalk_retraction g j hj y) r
  have hb : b.Etale := RingHom.Etale.of_bijective
    ⟨hqb.injective, fun a => ⟨q a, hq (hqb (q a))⟩⟩
  let c := Y.presheaf.stalkCongr (.of_eq (show g (j y) = y from
    congrArg (fun f : Y ⟶ Y => f y) hj))
  have hc : c.hom.hom.Etale := RingHom.Etale.of_bijective
    (ConcreteCategory.bijective_of_isIso c.hom)
  have he : (g.stalkMap (j y)).hom = b.comp c.hom.hom := by
    change (g.stalkMap (j y)).hom = (c.hom ≫ (c.inv ≫ g.stalkMap (j y))).hom
    simp only [← Category.assoc, c.hom_inv_id, Category.id_comp]
  rw [he]
  exact RingHom.Etale.stableUnderComposition c.hom.hom b hc hb

end PfaffianDescent
