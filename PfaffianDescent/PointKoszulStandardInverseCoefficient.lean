import PfaffianDescent.SectionRepresenterKoszulOverlapMaps
import PfaffianDescent.PointAdaptedCechAugmentation
import PfaffianDescent.SectionRepresenterKoszulStalk
import PfaffianDescent.KoszulCechTransgression

/-!
# The standard inverse coefficient as an actual sheaf morphism

On an overlap where the two parameters are invertible, the signed first
lifts produce multiplication by the positive product of their inverses.
The calculation is in the actual point Koszul sheaf resolution.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped nonZeroDivisors

namespace PfaffianDescent

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Overlap-scalar augmentation has the expected coefficient section. -/
theorem sectionRepresenterOverlapScalar_comp_augmentation
    {X : Scheme.{u}} {W U : X.Opens} (j : W ⟶ U)
    (c : Γ(X, W)) (Y : X.Modules) (y : Y.val.obj (op U)) :
    sectionRepresenterOverlapScalar X.ringCatSheaf j c ≫
        sectionRepresenterAugmentation X.ringCatSheaf U Y y =
      sectionRepresenterAugmentation X.ringCatSheaf W Y (c • Y.val.map j.op y) := by
  rw [sectionRepresenterOverlapScalar, Category.assoc,
    sectionRepresenterAugmentation_restrict, sectionRepresenterScalarEndomorphism_comp_augmentation]

set_option backward.isDefEq.respectTransparency false in
private theorem overlapLift_signed_decomposition
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {W U : C} (j : W ⟶ U) (a b : R.val.obj (op W)) :
    sectionRepresenterKoszulOverlapLift R j a b =
      0 - sectionRepresenterKoszulOverlapLift R j 0 (-b) +
        sectionRepresenterKoszulOverlapLift R j a 0 := by
  apply biproduct.hom_ext
  intro k
  fin_cases k <;>
    simp [sectionRepresenterKoszulOverlapLift, sectionRepresenterOverlapScalar,
      Preadditive.sub_comp, Preadditive.add_comp,
      sectionRepresenterScalarEndomorphism_zero, sectionRepresenterScalarEndomorphism_neg,
      Preadditive.neg_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The standard signed triple-boundary is the first Koszul differential
of the actual inverse-product overlap morphism. -/
theorem sectionRepresenterKoszul_standard_inverse_boundary
    {X : Scheme.{u}} {W U : X.Opens} (j : W ⟶ U) (q f : Γ(X, U))
    (uq uf : Γ(X, W))
    (hq : X.presheaf.map j.op q * uq = 1)
    (hf : X.presheaf.map j.op f * uf = 1) :
    sectionRepresenterOverlapScalar X.ringCatSheaf j (uq * uf) ≫
        sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
      0 - sectionRepresenterKoszulOverlapLift X.ringCatSheaf j 0 (-uf) +
        sectionRepresenterKoszulOverlapLift X.ringCatSheaf j (-uq) 0 := by
  have hfst : (uq * uf) * X.presheaf.map j.op (-f) = -uq := by
    rw [map_neg]
    linear_combination -uq * hf
  have hsnd : (uq * uf) * X.presheaf.map j.op q = uf := by
    linear_combination uf * hq
  rw [sectionRepresenterOverlapScalar_comp_first]
  change sectionRepresenterKoszulOverlapLift X.ringCatSheaf j
    ((uq * uf) * X.presheaf.map j.op (-f)) ((uq * uf) * X.presheaf.map j.op q) = _
  rw [hfst, hsnd]
  exact overlapLift_signed_decomposition X.ringCatSheaf j (-uq) uf

set_option backward.isDefEq.respectTransparency false in
/-- Any actual comparison coefficient with the standard triple-boundary
equals the inverse-product overlap morphism, by the proved Koszul monicity. -/
theorem pointKoszul_standard_inverse_coefficient
    {X : Scheme.{u}} {W U : X.Opens} (j : W ⟶ U) (x : X) (hx : x ∈ U)
    (q f : Γ(X, U))
    (hqreg : X.presheaf.germ U x hx q ∈ (X.presheaf.stalk x)⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {X.presheaf.germ U x hx q})
        (X.presheaf.germ U x hx f) ∈
      ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hx q})⁰)
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (uq uf : Γ(X, W)) (hq : X.presheaf.map j.op q * uq = 1)
    (hf : X.presheaf.map j.op f * uf = 1)
    (k : sectionRepresenter X.ringCatSheaf W ⟶ sectionRepresenter X.ringCatSheaf U)
    (hk : k ≫ sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
      0 - sectionRepresenterKoszulOverlapLift X.ringCatSheaf j 0 (-uf) +
        sectionRepresenterKoszulOverlapLift X.ringCatSheaf j (-uq) 0) :
    k = sectionRepresenterOverlapScalar X.ringCatSheaf j (uq * uf) := by
  letI : Mono (sectionRepresenterKoszulFirst X.ringCatSheaf U q f) :=
    sectionRepresenterKoszulFirst_mono_of_regularPairAtPoint X U q f x hx hqreg hfreg haway
  apply (cancel_mono (sectionRepresenterKoszulFirst X.ringCatSheaf U q f)).1
  exact hk.trans (sectionRepresenterKoszul_standard_inverse_boundary j q f uq uf hq hf).symm

end PfaffianDescent
