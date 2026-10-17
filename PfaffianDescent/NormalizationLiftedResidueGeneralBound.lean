import PfaffianDescent.NormalizationResidueGlobalTransport
import AllCharacteristics.ProperCyclePushforward

/-! Source-only general actual lifted residue degree / global defect bounds.
No regularity or equal-residue lift; original K and full constants are retained. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual canonical normalization has a closed point above original
P whose residue degree is divisible by BOTH original point degree and FULL
normalization constants rank. It is not required to preserve residue fields. -/
theorem integralProper_genericNormalization_exists_closedPoint_above_with_both_degree_divisibilities
    {K : Type u} [Field K] [CharZero K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [IsProper pi] (P : closedPoints X) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    ∃ Q : closedPoints N, ν Q.1 = P.1 ∧
      Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
        (SheafOfModules.unit N.ringCatSheaf) ⊤) ∣ (ν ≫ pi).residueDegree Q.1 ∧
      pi.residueDegree P.1 ∣ (ν ≫ pi).residueDegree Q.1 := by
  classical
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : IsFinite ν := integralScheme_genericNormalization_isFinite X pi
  letI : IsProper (ν ≫ pi) := inferInstance
  have hsurj : Function.Surjective ν :=
    (integralGenericNormalization_fromNormalization_surjective X).surj
  obtain ⟨q, hq⟩ := hsurj P.1
  let Q : closedPoints N := ⟨q, locallyQuasiFinite_closedPoint_above_closedPoint ν P q hq⟩
  have ha := integralProper_originalUnitSections_finrank_dvd_residueDegree (ν ≫ pi) Q
  have hd : pi.residueDegree P.1 ∣ (ν ≫ pi).residueDegree Q.1 := by
    rw [residueDegree_comp, hq]
    exact dvd_mul_right _ _
  exact ⟨Q, hq, ha, hd⟩

/-- Actual closed normalization residue degree is at most original point
residue degree plus literal original-K affine defect rank. Every evaluation
and square input is constructed; finiteness is the reusable local cut. -/
theorem genericNormalization_originalAffineDefect_add_pointDegree_ge_liftedDegree
    {K : Type u} [Field K] [CharZero K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [LocallyOfFiniteType pi]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hfinite : Module.Finite K
      ((ModuleCat.restrictScalars (schemeOpenBaseRingHom pi U)).obj
        (ModuleCat.of Γ(X, U) (localNormalizationDefect Γ(X, U) X.functionField)))) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    ∀ (Q : closedPoints (X.fromSpecStalk (genericPoint X)).normalization)
      (hQ : (X.fromSpecStalk (genericPoint X)).fromNormalization Q.1 ∈ U)
      (hclosed : IsClosed ({(X.fromSpecStalk (genericPoint X)).fromNormalization Q.1} : Set X)),
    (((X.fromSpecStalk (genericPoint X)).fromNormalization ≫ pi).residueDegree Q.1) ≤
      pi.residueDegree ((X.fromSpecStalk (genericPoint X)).fromNormalization Q.1) +
      Module.finrank K
        ((ModuleCat.restrictScalars (schemeOpenBaseRingHom pi U)).obj
          (ModuleCat.of Γ(X, U) (localNormalizationDefect Γ(X, U) X.functionField))) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : IsFinite ν := integralScheme_genericNormalization_isFinite X pi
  letI : LocallyOfFiniteType (ν ≫ pi) := inferInstance
  let R := Γ(X, U)
  let B := integralClosure R X.functionField
  letI : Algebra K R := (schemeOpenBaseRingHom pi U).toAlgebra
  letI : Algebra K B := Algebra.compHom B (schemeOpenBaseRingHom pi U)
  letI : IsScalarTower K R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let S : Submodule R B := LinearMap.range (Algebra.linearMap R B)
  let D := (ModuleCat.restrictScalars (schemeOpenBaseRingHom pi U)).obj
    (ModuleCat.of R (localNormalizationDefect R X.functionField))
  let eD : (B ⧸ S) ≃ₗ[K] D := originalBaseQuotientRestrictionLinearEquiv K R B S
  letI : Module.Finite K D := hfinite
  letI : Module.Finite K (B ⧸ S) := Module.Finite.equiv eD.symm
  dsimp only
  intro Q hQ hclosed
  let P : closedPoints X := ⟨ν Q.1, hclosed⟩
  letI := pointAlgebra pi (ν Q.1)
  letI := pointAlgebra (ν ≫ pi) Q.1
  letI : Module.Finite K (X.residueField (ν Q.1)) := closedPoint_moduleFinite pi P
  letI : Module.Finite K (N.residueField Q.1) := closedPoint_moduleFinite (ν ≫ pi) Q
  let a := originalOpenResidueEvaluationAlgHom pi U (ν Q.1) hQ
  let j := originalBaseResidueFieldMapAlgHom ν pi Q.1
  let beta := genericNormalization_originalClosureResidueEvaluationAlgHom X pi U hU Q.1 hQ
  have hbeta : Function.Surjective beta :=
    genericNormalization_originalClosureResidueEvaluation_surjective X pi U hU Q hQ
  have hcomm : ∀ r : R, beta (algebraMap R B r) = j (a r) :=
    genericNormalization_originalClosureResidueEvaluation_commutes X pi U hU Q.1 hQ
  have hquotient := affineInclusionResidueDiagram_quotient_ground_rank_bound a j beta hbeta hcomm
  change Module.finrank K (N.residueField Q.1) ≤ Module.finrank K (B ⧸ S) +
    Module.finrank K (X.residueField (ν Q.1)) at hquotient
  have hPL : Module.finrank K (X.residueField (ν Q.1)) = pi.residueDegree (ν Q.1) :=
    closedPoint_finrank_eq_residueDegree pi P
  have hQE : Module.finrank K (N.residueField Q.1) = (ν ≫ pi).residueDegree Q.1 :=
    closedPoint_finrank_eq_residueDegree (ν ≫ pi) Q
  have hdefect : Module.finrank K (B ⧸ S) = Module.finrank K D := eD.finrank_eq
  change (ν ≫ pi).residueDegree Q.1 ≤ pi.residueDegree (ν Q.1) + Module.finrank K D
  omega

/-- Actual integral whole projective intersection: construct an ACTUAL
closed normalized lift whose positive full ground degree is divisible by
both original degree and full constants rank, and bounded by original degree
plus ACTUAL GLOBAL defect. The full-support affine choice, finite defect and
original-K global equivalence are constructed internally. -/
theorem projectiveIntersection_genericNormalization_exists_liftedResidueDegree_divisibilities_and_globalDefect_bound
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq))) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    ∃ Q : closedPoints N, ν Q.1 = P.1 ∧
      Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ toBase I)
        (SheafOfModules.unit N.ringCatSheaf) ⊤) ∣ (ν ≫ toBase I).residueDegree Q.1 ∧
      (toBase I).residueDegree P.1 ∣ (ν ≫ toBase I).residueDegree Q.1 ∧
      0 < (ν ≫ toBase I).residueDegree Q.1 ∧
      (ν ≫ toBase I).residueDegree Q.1 ≤ (toBase I).residueDegree P.1 +
        Module.finrank K (SchemeModuleGlobalSectionsOver (toBase I)
          (genericNormalizationQuotientSheaf X)) := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : IsFinite ν := integralScheme_genericNormalization_isFinite X pi
  letI : IsProper (ν ≫ pi) := inferInstance
  let G := SchemeModuleGlobalSectionsOver pi (genericNormalizationQuotientSheaf X)
  letI : Module.Finite K G :=
    projectiveIntersection_genericNormalizationQuotient_globalSections_finite p q hp hp0 n hq hnot
  obtain ⟨Q, hQP, ha, hd⟩ :=
    integralProper_genericNormalization_exists_closedPoint_above_with_both_degree_divisibilities X pi P
  obtain ⟨U, hnonempty, hPU, ⟨eGlobal⟩⟩ :=
    projectiveIntersection_genericNormalizationQuotient_exists_globalSectionsEquiv_affineDefect
      p q hp hp0 n hq hnot P.1
  letI : Nonempty U.1 := hnonempty
  let D := (ModuleCat.restrictScalars (schemeOpenBaseRingHom pi U.1)).obj
    (ModuleCat.of Γ(X, U.1) (localNormalizationDefect Γ(X, U.1) X.functionField))
  have eGlobalNative : G ≃ₗ[K] D := eGlobal
  have hfinite : Module.Finite K D := Module.Finite.equiv eGlobalNative
  have hQU : ν Q.1 ∈ U.1 := hQP.symm ▸ hPU
  have hclosed : IsClosed ({ν Q.1} : Set X) := hQP.symm ▸ P.2
  have hbound : (ν ≫ pi).residueDegree Q.1 ≤ pi.residueDegree (ν Q.1) + Module.finrank K D :=
    genericNormalization_originalAffineDefect_add_pointDegree_ge_liftedDegree
      X pi U.1 U.2 hfinite Q hQU hclosed
  have hglobal : Module.finrank K G = Module.finrank K D := eGlobalNative.finrank_eq
  rw [hQP, ← hglobal] at hbound
  letI := pointAlgebra (ν ≫ pi) Q.1
  letI : Module.Finite K (N.residueField Q.1) := closedPoint_moduleFinite (ν ≫ pi) Q
  have hpositive : 0 < (ν ≫ pi).residueDegree Q.1 := by
    rw [← closedPoint_finrank_eq_residueDegree (ν ≫ pi) Q]
    exact Module.finrank_pos
  exact ⟨Q, hQP, ha, hd, hpositive, hbound⟩

end PfaffianDescent.Coray
