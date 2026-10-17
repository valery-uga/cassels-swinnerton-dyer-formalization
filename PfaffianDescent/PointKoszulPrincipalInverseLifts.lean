import PfaffianDescent.PointKoszulStandardInverseCoefficient
import PfaffianDescent.PointPrincipalAffineCover

/-!
# Prescribed first lifts on principal-open overlaps

Every subopen of a parameter principal open has the actual inverse section.
The negative inverse in the appropriate coordinate lifts the negative
inclusion, as required by the ordered Cech boundary from the point vertex.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace PfaffianDescent
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
universe u

section Site
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.isDefEq.respectTransparency false in
/-- The negative first-coordinate inverse lifts the negative inclusion. -/
theorem sectionRepresenterKoszul_inverse_q_lift
    {W U : C} (j : W ⟶ U) (q f : R.obj.obj (op U))
    (uq : R.obj.obj (op W)) (hq : uq * R.obj.map j.op q = 1) :
    sectionRepresenterKoszulOverlapLift R j (-uq) 0 ≫
        sectionRepresenterKoszulLast R U q f =
      -(sectionRepresenterFunctor R).map j := by
  rw [sectionRepresenterKoszulOverlapLift_comp_last]
  have hc : (-uq) * R.obj.map j.op q + 0 * R.obj.map j.op f = -1 := by
    simp [neg_mul, hq]
  rw [hc]
  simp [sectionRepresenterOverlapScalar, Preadditive.neg_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The negative second-coordinate inverse lifts the negative inclusion. -/
theorem sectionRepresenterKoszul_inverse_f_lift
    {W U : C} (j : W ⟶ U) (q f : R.obj.obj (op U))
    (uf : R.obj.obj (op W)) (hf : uf * R.obj.map j.op f = 1) :
    sectionRepresenterKoszulOverlapLift R j 0 (-uf) ≫
        sectionRepresenterKoszulLast R U q f =
      -(sectionRepresenterFunctor R).map j := by
  rw [sectionRepresenterKoszulOverlapLift_comp_last]
  have hc : 0 * R.obj.map j.op q + (-uf) * R.obj.map j.op f = -1 := by
    simp [neg_mul, hf]
  rw [hc]
  simp [sectionRepresenterOverlapScalar, Preadditive.neg_comp]
end Site

set_option backward.isDefEq.respectTransparency false in
/-- Inverse sections exist on every actual subopen of the parameter basic open. -/
theorem exists_inverse_on_parameter_basicOpen_subopen
    {X : Scheme.{u}} {U W : X.Opens} (q : Γ(X, U))
    (hW : W ≤ X.basicOpen q) :
    ∃ uq : Γ(X, W),
      X.presheaf.map (homOfLE (hW.trans (X.basicOpen_le q))).op q * uq = 1 := by
  let k : W ⟶ X.basicOpen q := homOfLE hW
  let j : X.basicOpen q ⟶ U := homOfLE (X.basicOpen_le q)
  have hu := RingHom.isUnit_map (X.presheaf.map k.op).hom
    (X.toRingedSpace.isUnit_res_basicOpen q)
  change IsUnit (X.presheaf.map k.op (X.presheaf.map j.op q)) at hu
  have he : k ≫ j = homOfLE (hW.trans (X.basicOpen_le q)) := Subsingleton.elim _ _
  have hres : X.presheaf.map k.op (X.presheaf.map j.op q) =
      X.presheaf.map (homOfLE (hW.trans (X.basicOpen_le q))).op q := by
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    exact congrArg (fun t => X.presheaf.map t.op q) he
  rw [hres] at hu
  exact hu.exists_right_inv

set_option backward.isDefEq.respectTransparency false in
/-- The actual q-principal geometry supplies the prescribed first lift. -/
theorem exists_pointKoszul_q_principal_signed_lift
    {X : Scheme.{u}} {U W : X.Opens} (q f : Γ(X, U))
    (hW : W ≤ X.basicOpen q) :
    ∃ uq : Γ(X, W),
      X.presheaf.map (homOfLE (hW.trans (X.basicOpen_le q))).op q * uq = 1 ∧
      sectionRepresenterKoszulOverlapLift X.ringCatSheaf
          (homOfLE (hW.trans (X.basicOpen_le q))) (-uq) 0 ≫
        sectionRepresenterKoszulLast X.ringCatSheaf U q f =
      -(sectionRepresenterFunctor X.ringCatSheaf).map
        (homOfLE (hW.trans (X.basicOpen_le q))) := by
  obtain ⟨uq, huq⟩ := exists_inverse_on_parameter_basicOpen_subopen q hW
  exact ⟨uq, huq, sectionRepresenterKoszul_inverse_q_lift X.ringCatSheaf _ q f uq (by
    change uq * X.presheaf.map (homOfLE (hW.trans (X.basicOpen_le q))).op q = 1
    simpa only [mul_comm] using huq)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual f-principal geometry supplies the prescribed first lift. -/
theorem exists_pointKoszul_f_principal_signed_lift
    {X : Scheme.{u}} {U W : X.Opens} (q f : Γ(X, U))
    (hW : W ≤ X.basicOpen f) :
    ∃ uf : Γ(X, W),
      X.presheaf.map (homOfLE (hW.trans (X.basicOpen_le f))).op f * uf = 1 ∧
      sectionRepresenterKoszulOverlapLift X.ringCatSheaf
          (homOfLE (hW.trans (X.basicOpen_le f))) 0 (-uf) ≫
        sectionRepresenterKoszulLast X.ringCatSheaf U q f =
      -(sectionRepresenterFunctor X.ringCatSheaf).map
        (homOfLE (hW.trans (X.basicOpen_le f))) := by
  obtain ⟨uf, huf⟩ := exists_inverse_on_parameter_basicOpen_subopen f hW
  exact ⟨uf, huf, sectionRepresenterKoszul_inverse_f_lift X.ringCatSheaf _ q f uf (by
    change uf * X.presheaf.map (homOfLE (hW.trans (X.basicOpen_le f))).op f = 1
    simpa only [mul_comm] using huf)⟩
end PfaffianDescent
