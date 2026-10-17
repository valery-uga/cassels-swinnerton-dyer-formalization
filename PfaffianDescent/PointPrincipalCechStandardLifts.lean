import PfaffianDescent.PointPrincipalCechFirstLift

/-! # A family of actual first lifts with prescribed residue components -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace PfaffianDescent.PointAdaptedAffineCover
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Choose all ordered overlap lifts together, prescribing the two negative
inverse lifts and the zero lift on the principal/principal overlap. -/
theorem exists_principal_standard_pair_lifts
    {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (q f : Γ(X, U))
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤) :
    let D : PrincipalIndex X x := Sum.inr none
    let Q : PrincipalIndex X x := Sum.inl 0
    let F : PrincipalIndex X x := Sum.inl 1
    let Vq := principalPairOpen U x q f D Q
    let Vf := principalPairOpen U x q f D F
    let jq : Vq ⟶ U := Pi.π ![U, X.basicOpen q] 0
    let jf : Vf ⟶ U := Pi.π ![U, X.basicOpen f] 0
    ∃ (uq : Γ(X, Vq)) (uf : Γ(X, Vf))
      (L : ∀ i j : PrincipalIndex X x,
        sectionRepresenter X.ringCatSheaf (principalPairOpen U x q f i j) ⟶
          ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U),
      X.presheaf.map jq.op q * uq = 1 ∧
      X.presheaf.map jf.op f * uf = 1 ∧
      (∀ i j, L i j ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
        principalPairBoundary U x q f i j) ∧
      L D Q = sectionRepresenterKoszulOverlapLift X.ringCatSheaf jq (-uq) 0 ∧
      L D F = sectionRepresenterKoszulOverlapLift X.ringCatSheaf jf 0 (-uf) ∧
      L Q F = 0 := by
  classical
  dsimp only
  let D : PrincipalIndex X x := Sum.inr none
  let Q : PrincipalIndex X x := Sum.inl 0
  let F : PrincipalIndex X x := Sum.inl 1
  let Vq := principalPairOpen U x q f D Q
  let Vf := principalPairOpen U x q f D F
  let jq : Vq ⟶ U := Pi.π ![U, X.basicOpen q] 0
  let jf : Vf ⟶ U := Pi.π ![U, X.basicOpen f] 0
  obtain ⟨uq, huq, hq⟩ := exists_pointKoszul_q_principal_signed_lift q f
    (Pi.π ![U, X.basicOpen q] 1).le
  obtain ⟨uf, huf, hf⟩ := exists_pointKoszul_f_principal_signed_lift q f
    (Pi.π ![U, X.basicOpen f] 1).le
  have heq : homOfLE ((Pi.π ![U, X.basicOpen q] 1).le.trans
      (X.basicOpen_le q)) = jq := Subsingleton.elim _ _
  have hef : homOfLE ((Pi.π ![U, X.basicOpen f] 1).le.trans
      (X.basicOpen_le f)) = jf := Subsingleton.elim _ _
  rw [heq] at huq hq
  rw [hef] at huf hf
  let vq : sectionRepresenter X.ringCatSheaf Vq ⟶
      ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U :=
    sectionRepresenterKoszulOverlapLift X.ringCatSheaf jq (-uq) 0
  let vf : sectionRepresenter X.ringCatSheaf Vf ⟶
      ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U :=
    sectionRepresenterKoszulOverlapLift X.ringCatSheaf jf 0 (-uf)
  have hbq : vq ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
      principalPairBoundary U x q f D Q := by
    rw [hq]
    simp only [D, Q, principalPairBoundary, principalVertexMap, vertexMap,
      principalOpens, opens_none, Matrix.cons_val_zero, comp_zero, zero_sub]
    let k : sectionRepresenter X.ringCatSheaf Vq ⟶ sectionRepresenter X.ringCatSheaf U :=
      (sectionRepresenterFunctor X.ringCatSheaf).map jq
    change -k = -(k ≫ 𝟙 _)
    exact congrArg Neg.neg (Category.comp_id k).symm
  have hbf : vf ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
      principalPairBoundary U x q f D F := by
    rw [hf]
    simp only [D, F, principalPairBoundary, principalVertexMap, vertexMap,
      principalOpens, opens_none, Matrix.cons_val_one, comp_zero, zero_sub]
    let k : sectionRepresenter X.ringCatSheaf Vf ⟶ sectionRepresenter X.ringCatSheaf U :=
      (sectionRepresenterFunctor X.ringCatSheaf).map jf
    change -k = -(k ≫ 𝟙 _)
    exact congrArg Neg.neg (Category.comp_id k).symm
  choose v hv using (fun i j => exists_principalPairBoundary_lift U hU x q f haway i j)
  let rowD := Function.update (Function.update (v D) Q vq) F vf
  let rowQ := Function.update (v Q) F 0
  let L := Function.update (Function.update v D rowD) Q rowQ
  refine ⟨uq, uf, L, huq, huf, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases hiQ : i = Q
    · subst i
      by_cases hjF : j = F
      · subst j
        simp [L, rowQ, Q, F, principalPairBoundary, principalVertexMap]
      · simpa only [L, Function.update_self, rowQ, Function.update_of_ne hjF] using hv Q j
    · by_cases hiD : i = D
      · subst i
        by_cases hjF : j = F
        · subst j
          simpa [L, rowD, D, Q, F] using hbf
        · by_cases hjQ : j = Q
          · subst j
            simpa [L, rowD, D, Q, F] using hbq
          · simpa only [L, Function.update_of_ne hiQ, Function.update_self,
              rowD, Function.update_of_ne hjF, Function.update_of_ne hjQ] using hv D j
      · simpa only [L, Function.update_of_ne hiQ, Function.update_of_ne hiD] using hv i j
  · simp [L, rowD, D, Q, F, vq, jq]
  · simp [L, rowD, D, Q, F, vf, jf]
  · simp [L, rowQ, Q, F]
end PfaffianDescent.PointAdaptedAffineCover
