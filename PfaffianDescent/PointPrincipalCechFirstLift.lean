import PfaffianDescent.PointKoszulInverseRestriction

/-! # Actual first comparison lifts on the labeled principal cover -/
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
private theorem positive_q_lift {W U : C} (j : W ⟶ U)
    (q f : R.obj.obj (op U)) (uq : R.obj.obj (op W))
    (hq : uq * R.obj.map j.op q = 1) :
    sectionRepresenterKoszulOverlapLift R j uq 0 ≫
      sectionRepresenterKoszulLast R U q f = (sectionRepresenterFunctor R).map j := by
  rw [sectionRepresenterKoszulOverlapLift_comp_last]
  simp [hq, sectionRepresenterOverlapScalar]
set_option backward.isDefEq.respectTransparency false in
private theorem positive_f_lift {W U : C} (j : W ⟶ U)
    (q f : R.obj.obj (op U)) (uf : R.obj.obj (op W))
    (hf : uf * R.obj.map j.op f = 1) :
    sectionRepresenterKoszulOverlapLift R j 0 uf ≫
      sectionRepresenterKoszulLast R U q f = (sectionRepresenterFunctor R).map j := by
  rw [sectionRepresenterKoszulOverlapLift_comp_last]
  simp [hf, sectionRepresenterOverlapScalar]
end Site

namespace PointAdaptedAffineCover
variable {X : Scheme.{u}}

def principalVertexMap (U : X.Opens) (x : X) (q f : Γ(X, U)) :
    ∀ i : PrincipalIndex X x,
      sectionRepresenter X.ringCatSheaf (principalOpens U x q f i) ⟶
        sectionRepresenter X.ringCatSheaf U
  | Sum.inl _ => 0
  | Sum.inr i => vertexMap U x i

abbrev principalPairOpen (U : X.Opens) (x : X) (q f : Γ(X, U))
    (i j : PrincipalIndex X x) : X.Opens :=
  ∏ᶜ ![principalOpens U x q f i, principalOpens U x q f j]

def principalPairBoundary (U : X.Opens) (x : X) (q f : Γ(X, U))
    (i j : PrincipalIndex X x) :
    sectionRepresenter X.ringCatSheaf (principalPairOpen U x q f i j) ⟶
      sectionRepresenter X.ringCatSheaf U :=
  (sectionRepresenterFunctor X.ringCatSheaf).map
      (Pi.π ![principalOpens U x q f i, principalOpens U x q f j] 1) ≫
        principalVertexMap U x q f j -
    (sectionRepresenterFunctor X.ringCatSheaf).map
      (Pi.π ![principalOpens U x q f i, principalOpens U x q f j] 0) ≫
        principalVertexMap U x q f i

set_option backward.isDefEq.respectTransparency false in
/-- Actual geometric lifts on every ordered principal-cover overlap. -/
theorem exists_principalPairBoundary_lift
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (q f : Γ(X, U))
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (i j : PrincipalIndex X x) :
    ∃ v : sectionRepresenter X.ringCatSheaf (principalPairOpen U x q f i j) ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U,
      v ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
        principalPairBoundary U x q f i j := by
  cases i with
  | inl a =>
    cases j with
    | inl b =>
      refine ⟨0, ?_⟩
      simp [principalPairBoundary, principalVertexMap]
    | inr j =>
      cases j with
      | some V =>
        refine ⟨0, ?_⟩
        simp [principalPairBoundary, principalVertexMap, vertexMap]
      | none =>
        fin_cases a
        · let W : X.Opens := ∏ᶜ ![X.basicOpen q, U]
          let jU : W ⟶ U := Pi.π ![X.basicOpen q, U] 1
          obtain ⟨uq, huq⟩ := exists_inverse_on_parameter_basicOpen_subopen q
            (Pi.π ![X.basicOpen q, U] 0).le
          have he : homOfLE ((Pi.π ![X.basicOpen q, U] 0).le.trans
              (X.basicOpen_le q)) = jU := Subsingleton.elim _ _
          rw [he] at huq
          refine ⟨sectionRepresenterKoszulOverlapLift X.ringCatSheaf jU uq 0, ?_⟩
          have h := positive_q_lift X.ringCatSheaf jU q f uq (by
            change uq * X.presheaf.map jU.op q = 1
            simpa only [mul_comm] using huq)
          rw [h]
          simp only [principalPairBoundary, principalVertexMap, vertexMap,
            principalOpens, opens_none, Matrix.cons_val_zero, Matrix.cons_val_one,
            comp_zero, sub_zero]
          let k : sectionRepresenter X.ringCatSheaf W ⟶ sectionRepresenter X.ringCatSheaf U :=
            (sectionRepresenterFunctor X.ringCatSheaf).map jU
          change k = k ≫ 𝟙 _
          exact (Category.comp_id k).symm
        · let W : X.Opens := ∏ᶜ ![X.basicOpen f, U]
          let jU : W ⟶ U := Pi.π ![X.basicOpen f, U] 1
          obtain ⟨uf, huf⟩ := exists_inverse_on_parameter_basicOpen_subopen f
            (Pi.π ![X.basicOpen f, U] 0).le
          have he : homOfLE ((Pi.π ![X.basicOpen f, U] 0).le.trans
              (X.basicOpen_le f)) = jU := Subsingleton.elim _ _
          rw [he] at huf
          refine ⟨sectionRepresenterKoszulOverlapLift X.ringCatSheaf jU 0 uf, ?_⟩
          have h := positive_f_lift X.ringCatSheaf jU q f uf (by
            change uf * X.presheaf.map jU.op f = 1
            simpa only [mul_comm] using huf)
          rw [h]
          simp only [principalPairBoundary, principalVertexMap, vertexMap,
            principalOpens, opens_none, Matrix.cons_val_zero, Matrix.cons_val_one,
            comp_zero, sub_zero]
          let k : sectionRepresenter X.ringCatSheaf W ⟶ sectionRepresenter X.ringCatSheaf U :=
            (sectionRepresenterFunctor X.ringCatSheaf).map jU
          change k = k ≫ 𝟙 _
          exact (Category.comp_id k).symm
  | inr i =>
    cases j with
    | inr j => exact exists_pairBoundary_lift U hU x q f haway i j
    | inl a =>
      cases i with
      | some V =>
        refine ⟨0, ?_⟩
        simp [principalPairBoundary, principalVertexMap, vertexMap]
      | none =>
        fin_cases a
        · let W : X.Opens := ∏ᶜ ![U, X.basicOpen q]
          let jU : W ⟶ U := Pi.π ![U, X.basicOpen q] 0
          obtain ⟨uq, huq, h⟩ := exists_pointKoszul_q_principal_signed_lift q f
            (Pi.π ![U, X.basicOpen q] 1).le
          have he : homOfLE ((Pi.π ![U, X.basicOpen q] 1).le.trans
              (X.basicOpen_le q)) = jU := Subsingleton.elim _ _
          rw [he] at h
          refine ⟨sectionRepresenterKoszulOverlapLift X.ringCatSheaf jU (-uq) 0, ?_⟩
          rw [h]
          simp only [principalPairBoundary, principalVertexMap, vertexMap,
            principalOpens, opens_none, Matrix.cons_val_zero, Matrix.cons_val_one,
            comp_zero, zero_sub]
          let k : sectionRepresenter X.ringCatSheaf W ⟶ sectionRepresenter X.ringCatSheaf U :=
            (sectionRepresenterFunctor X.ringCatSheaf).map jU
          change -k = -(k ≫ 𝟙 _)
          exact congrArg Neg.neg (Category.comp_id k).symm
        · let W : X.Opens := ∏ᶜ ![U, X.basicOpen f]
          let jU : W ⟶ U := Pi.π ![U, X.basicOpen f] 0
          obtain ⟨uf, huf, h⟩ := exists_pointKoszul_f_principal_signed_lift q f
            (Pi.π ![U, X.basicOpen f] 1).le
          have he : homOfLE ((Pi.π ![U, X.basicOpen f] 1).le.trans
              (X.basicOpen_le f)) = jU := Subsingleton.elim _ _
          rw [he] at h
          refine ⟨sectionRepresenterKoszulOverlapLift X.ringCatSheaf jU 0 (-uf), ?_⟩
          rw [h]
          simp only [principalPairBoundary, principalVertexMap, vertexMap,
            principalOpens, opens_none, Matrix.cons_val_zero, Matrix.cons_val_one,
            comp_zero, zero_sub]
          let k : sectionRepresenter X.ringCatSheaf W ⟶ sectionRepresenter X.ringCatSheaf U :=
            (sectionRepresenterFunctor X.ringCatSheaf).map jU
          change -k = -(k ≫ 𝟙 _)
          exact congrArg Neg.neg (Category.comp_id k).symm
end PointAdaptedAffineCover
end PfaffianDescent
