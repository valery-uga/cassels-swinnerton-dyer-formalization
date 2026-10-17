import PfaffianDescent.PointKoszulPrincipalInverseLifts

/-!
# Restriction of prescribed inverse lifts

Inverse sections chosen on a parameter principal open stay inverses on every
smaller overlap. Thus the positive inverse-product calculation applies to
the restrictions of the actual first-lift sections, not just to fresh choices.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace PfaffianDescent
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a first Koszul lift restricts both coefficient sections. -/
theorem sectionRepresenterKoszulOverlapLift_precomp
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {W V U : C} (k : W ⟶ V) (j : V ⟶ U) (a b : R.obj.obj (op V)) :
    (sectionRepresenterFunctor R).map k ≫ sectionRepresenterKoszulOverlapLift R j a b =
      sectionRepresenterKoszulOverlapLift R (k ≫ j) (R.obj.map k.op a) (R.obj.map k.op b) := by
  apply biproduct.hom_ext
  intro i
  fin_cases i <;>
    simp [sectionRepresenterKoszulOverlapLift, Category.assoc,
      sectionRepresenterOverlapScalar_precomp]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting an actual inverse section preserves its inverse equation. -/
theorem pointKoszul_inverse_restrict
    {X : Scheme.{u}} {W V U : X.Opens} (k : W ⟶ V) (j : V ⟶ U)
    (q : Γ(X, U)) (uq : Γ(X, V)) (hq : X.presheaf.map j.op q * uq = 1) :
    X.presheaf.map (k ≫ j).op q * X.presheaf.map k.op uq = 1 := by
  have h := congrArg (fun a => X.presheaf.map k.op a) hq
  rw [map_mul, map_one] at h
  have hres : X.presheaf.map k.op (X.presheaf.map j.op q) =
      X.presheaf.map (k ≫ j).op q := by
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    rfl
  rw [hres] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The inverse product on a shared overlap is computed from the inverse
sections on the two larger parameter opens. -/
theorem pointKoszul_restricted_inverse_boundary
    {X : Scheme.{u}} {W Vq Vf U : X.Opens}
    (kq : W ⟶ Vq) (kf : W ⟶ Vf) (jq : Vq ⟶ U) (jf : Vf ⟶ U)
    (q f : Γ(X, U)) (uq : Γ(X, Vq)) (uf : Γ(X, Vf))
    (hq : X.presheaf.map jq.op q * uq = 1)
    (hf : X.presheaf.map jf.op f * uf = 1) :
    sectionRepresenterOverlapScalar X.ringCatSheaf (kq ≫ jq)
        (X.presheaf.map kq.op uq * X.presheaf.map kf.op uf) ≫
      sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
    0 - sectionRepresenterKoszulOverlapLift X.ringCatSheaf (kq ≫ jq)
        0 (-X.presheaf.map kf.op uf) +
      sectionRepresenterKoszulOverlapLift X.ringCatSheaf (kq ≫ jq)
        (-X.presheaf.map kq.op uq) 0 := by
  have hq' := pointKoszul_inverse_restrict kq jq q uq hq
  have hf' := pointKoszul_inverse_restrict kf jf f uf hf
  have he : kf ≫ jf = kq ≫ jq := Subsingleton.elim _ _
  rw [he] at hf'
  exact sectionRepresenterKoszul_standard_inverse_boundary (kq ≫ jq) q f
    (X.presheaf.map kq.op uq) (X.presheaf.map kf.op uf) hq' hf'

set_option backward.isDefEq.respectTransparency false in
/-- The positive coefficient is the boundary of the actual restricted
first-lift morphisms from the two parameter opens. -/
theorem pointKoszul_restricted_first_lifts_boundary
    {X : Scheme.{u}} {W Vq Vf U : X.Opens}
    (kq : W ⟶ Vq) (kf : W ⟶ Vf) (jq : Vq ⟶ U) (jf : Vf ⟶ U)
    (q f : Γ(X, U)) (uq : Γ(X, Vq)) (uf : Γ(X, Vf))
    (hq : X.presheaf.map jq.op q * uq = 1)
    (hf : X.presheaf.map jf.op f * uf = 1) :
    sectionRepresenterOverlapScalar X.ringCatSheaf (kq ≫ jq)
        (X.presheaf.map kq.op uq * X.presheaf.map kf.op uf) ≫
      sectionRepresenterKoszulFirst X.ringCatSheaf U q f =
    0 - ((sectionRepresenterFunctor X.ringCatSheaf).map kf ≫
        sectionRepresenterKoszulOverlapLift X.ringCatSheaf jf 0 (-uf) :
        sectionRepresenter X.ringCatSheaf W ⟶ ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U) +
      ((sectionRepresenterFunctor X.ringCatSheaf).map kq ≫
        sectionRepresenterKoszulOverlapLift X.ringCatSheaf jq (-uq) 0 :
        sectionRepresenter X.ringCatSheaf W ⟶ ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U) := by
  rw [sectionRepresenterKoszulOverlapLift_precomp,
    sectionRepresenterKoszulOverlapLift_precomp]
  have he : kf ≫ jf = kq ≫ jq := Subsingleton.elim _ _
  rw [he]
  change _ = 0 - sectionRepresenterKoszulOverlapLift X.ringCatSheaf (kq ≫ jq)
      (X.presheaf.map kf.op 0) (X.presheaf.map kf.op (-uf)) +
    sectionRepresenterKoszulOverlapLift X.ringCatSheaf (kq ≫ jq)
      (X.presheaf.map kq.op (-uq)) (X.presheaf.map kq.op 0)
  simp only [map_zero, map_neg]
  exact pointKoszul_restricted_inverse_boundary kq kf jq jf q f uq uf hq hf

end PfaffianDescent
