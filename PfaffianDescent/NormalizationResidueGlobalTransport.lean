import PfaffianDescent.NativeNormalizationResidueMaps
import PfaffianDescent.NormalizationAffineEvaluation
import PfaffianDescent.CorayAffineNormalizationResidueDefectRank
import PfaffianDescent.CorayGlobalSectionsChosenAffineDefect
import PfaffianDescent.CorayGlobalOriginalSectionsFinite

/-! Source only. Actual normalization-chart evaluation and original-base
global defect transport. Every map is constructed from the native maps. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The existing actual normalization-chart equivalence also preserves
the independently native original K constants on normalized sections.
On the integral closure the K action is restriction along the ORIGINAL
K-to-original-chart map. No alternative constants field is substituted. -/
def genericNormalization_preimageSectionsOriginalBaseAlgEquiv
    {K : Type u} [Field K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
    letI : Algebra K Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) :=
      (schemeOpenBaseRingHom ((X.fromSpecStalk (genericPoint X)).fromNormalization ≫ pi)
        ((X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U)).toAlgebra
    letI : Algebra K (integralClosure Γ(X, U) X.functionField) :=
      Algebra.compHom _ (schemeOpenBaseRingHom pi U)
    Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) ≃ₐ[K]
      integralClosure Γ(X, U) X.functionField := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
  letI : Algebra K Γ((X.fromSpecStalk (genericPoint X)).normalization, ν ⁻¹ᵁ U) :=
    (schemeOpenBaseRingHom (ν ≫ pi) (ν ⁻¹ᵁ U)).toAlgebra
  letI : Algebra Γ(X, U) Γ((X.fromSpecStalk (genericPoint X)).normalization, ν ⁻¹ᵁ U) :=
    (ν.app U).hom.toAlgebra
  letI : IsScalarTower K Γ(X, U)
      Γ((X.fromSpecStalk (genericPoint X)).normalization, ν ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq
      (fun c => (originalOpenBaseRingHom_section_naturality ν pi U c).symm)
  letI : Algebra K (integralClosure Γ(X, U) X.functionField) :=
    Algebra.compHom _ (schemeOpenBaseRingHom pi U)
  letI : IsScalarTower K Γ(X, U) (integralClosure Γ(X, U) X.functionField) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (genericNormalization_preimageSectionsAlgEquiv X U hU).restrictScalars K

/-- The actual normalization closed-point evaluation, transported to the
literal integral closure of the original affine chart in K(X). -/
def genericNormalization_originalClosureResidueEvaluationAlgHom
    {K : Type u} [Field K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Algebra K (integralClosure Γ(X, U) X.functionField) :=
      Algebra.compHom _ (schemeOpenBaseRingHom pi U)
    ∀ (q : (X.fromSpecStalk (genericPoint X)).normalization)
      (hq : (X.fromSpecStalk (genericPoint X)).fromNormalization q ∈ U),
      letI := pointAlgebra ((X.fromSpecStalk (genericPoint X)).fromNormalization ≫ pi) q
      integralClosure Γ(X, U) X.functionField →ₐ[K]
        (X.fromSpecStalk (genericPoint X)).normalization.residueField q := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : Algebra K (integralClosure Γ(X, U) X.functionField) :=
    Algebra.compHom _ (schemeOpenBaseRingHom pi U)
  dsimp only
  intro q hq
  letI := pointAlgebra (ν ≫ pi) q
  letI : Algebra K Γ((X.fromSpecStalk (genericPoint X)).normalization, ν ⁻¹ᵁ U) :=
    (schemeOpenBaseRingHom (ν ≫ pi) (ν ⁻¹ᵁ U)).toAlgebra
  exact (originalOpenResidueEvaluationAlgHom (ν ≫ pi) (ν ⁻¹ᵁ U) q hq).comp
    (genericNormalization_preimageSectionsOriginalBaseAlgEquiv X pi U hU).symm.toAlgHom

/-- Actual normalization-chart beta is onto at every actual closed Q.
Affineness of the normalized preimage and closed-point evaluation are proved,
and no evaluation-surjectivity certificate occurs among the hypotheses. -/
theorem genericNormalization_originalClosureResidueEvaluation_surjective
    {K : Type u} [Field K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Algebra K (integralClosure Γ(X, U) X.functionField) :=
      Algebra.compHom _ (schemeOpenBaseRingHom pi U)
    ∀ (Q : closedPoints (X.fromSpecStalk (genericPoint X)).normalization)
      (hQ : (X.fromSpecStalk (genericPoint X)).fromNormalization Q.1 ∈ U),
      letI := pointAlgebra ((X.fromSpecStalk (genericPoint X)).fromNormalization ≫ pi) Q.1
      Function.Surjective (genericNormalization_originalClosureResidueEvaluationAlgHom
        X pi U hU Q.1 hQ) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  letI : Algebra K (integralClosure Γ(X, U) X.functionField) :=
    Algebra.compHom _ (schemeOpenBaseRingHom pi U)
  dsimp only
  intro Q hQ
  letI := pointAlgebra (ν ≫ pi) Q.1
  letI : Algebra K Γ(N, ν ⁻¹ᵁ U) :=
    (schemeOpenBaseRingHom (ν ≫ pi) (ν ⁻¹ᵁ U)).toAlgebra
  have hV : IsAffineOpen (ν ⁻¹ᵁ U) := genericNormalization_affinePreimage_isAffine X U hU
  have heval : Function.Surjective (N.evaluation (ν ⁻¹ᵁ U) Q.1 hQ) :=
    affineOpen_evaluation_surjective_at_closedPoint N (ν ⁻¹ᵁ U) hV Q.1 hQ Q.2
  exact heval.comp
    (genericNormalization_preimageSectionsOriginalBaseAlgEquiv X pi U hU).symm.surjective

/-- The literal closure evaluation square commutes with the actual original
point evaluation and actual native residue extension, over the SAME K. -/
theorem genericNormalization_originalClosureResidueEvaluation_commutes
    {K : Type u} [Field K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
    letI : Algebra K (integralClosure Γ(X, U) X.functionField) :=
      Algebra.compHom _ (schemeOpenBaseRingHom pi U)
    ∀ (q : (X.fromSpecStalk (genericPoint X)).normalization)
      (hq : (X.fromSpecStalk (genericPoint X)).fromNormalization q ∈ U),
      letI := pointAlgebra pi ((X.fromSpecStalk (genericPoint X)).fromNormalization q)
      letI := pointAlgebra ((X.fromSpecStalk (genericPoint X)).fromNormalization ≫ pi) q
      ∀ r : Γ(X, U),
      genericNormalization_originalClosureResidueEvaluationAlgHom X pi U hU q hq
          (algebraMap Γ(X, U) (integralClosure Γ(X, U) X.functionField) r) =
        originalBaseResidueFieldMapAlgHom (X.fromSpecStalk (genericPoint X)).fromNormalization pi q
          (originalOpenResidueEvaluationAlgHom pi U
            ((X.fromSpecStalk (genericPoint X)).fromNormalization q) hq r) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : Algebra K Γ(X, U) := (schemeOpenBaseRingHom pi U).toAlgebra
  letI : Algebra K (integralClosure Γ(X, U) X.functionField) :=
    Algebra.compHom _ (schemeOpenBaseRingHom pi U)
  dsimp only
  intro q hq
  letI := pointAlgebra pi (ν q)
  letI := pointAlgebra (ν ≫ pi) q
  intro r
  letI : Algebra Γ(X, U) Γ((X.fromSpecStalk (genericPoint X)).normalization, ν ⁻¹ᵁ U) :=
    (ν.app U).hom.toAlgebra
  have hc : (genericNormalization_preimageSectionsAlgEquiv X U hU).symm
      (algebraMap Γ(X, U) (integralClosure Γ(X, U) X.functionField) r) = ν.app U r :=
    (genericNormalization_preimageSectionsAlgEquiv X U hU).symm.commutes r
  change (X.fromSpecStalk (genericPoint X)).normalization.evaluation (ν ⁻¹ᵁ U) q hq
    ((genericNormalization_preimageSectionsAlgEquiv X U hU).symm
      (algebraMap Γ(X, U) (integralClosure Γ(X, U) X.functionField) r)) = _
  rw [hc]
  exact (Scheme.evaluation_naturality_apply ν q hq r).symm

/-- Restricting the native R quotient action along K→R agrees with the
quotient's original K action. This genuine scalar transport is constructed
from the scalar-tower law; equality of module structures is not assumed. -/
def originalBaseQuotientRestrictionLinearEquiv
    (K R B : Type u) [Field K] [CommRing R] [CommRing B]
    [Algebra K R] [Algebra K B] [Algebra R B] [IsScalarTower K R B]
    (S : Submodule R B) :
    (B ⧸ S) ≃ₗ[K]
      (ModuleCat.restrictScalars (algebraMap K R)).obj
        (ModuleCat.of R (B ⧸ S)) :=
  { toFun := id
    invFun := id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun c d => (algebraMap_smul R c d).symm }

/-- At an actual closed point Q above an actual closed original point,
the literal original-K affine normalization defect has rank at least twice
the original residue degree when the upper degree is divisible by three.
This local cut accepts finiteness only; the projective endpoint below proves
it internally from actual global sections and their actual equivalence. -/
theorem genericNormalization_originalAffineDefect_ge_twice_residueDegree
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
    Nat.Coprime (pi.residueDegree ((X.fromSpecStalk (genericPoint X)).fromNormalization Q.1)) 3 →
    3 ∣ (((X.fromSpecStalk (genericPoint X)).fromNormalization ≫ pi).residueDegree Q.1) →
    2 * pi.residueDegree ((X.fromSpecStalk (genericPoint X)).fromNormalization Q.1) ≤
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
  intro Q hQ hclosed hcop hthree
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
  have hcopRank : Nat.Coprime (Module.finrank K (X.residueField (ν Q.1))) 3 :=
    hPL.symm ▸ hcop
  have hthreeRank : 3 ∣ Module.finrank K (N.residueField Q.1) := hQE.symm ▸ hthree
  have hresidue : 3 * Module.finrank K (X.residueField (ν Q.1)) ≤
      Module.finrank K (N.residueField Q.1) :=
    actualResidueExtension_ground_rank_ge_three_mul j hcopRank hthreeRank
  have hdefect : Module.finrank K (B ⧸ S) = Module.finrank K D := eD.finrank_eq
  change 2 * pi.residueDegree (ν Q.1) ≤ Module.finrank K D
  omega

/-- For the ACTUAL integral selected projective complete intersection,
three dividing the FULL normalization constants forces the ACTUAL original-K
GLOBAL normalization-defect rank to be at least twice an original point
degree prime to three. The actual lift, normalized evaluation surjectivity,
closed/full-support affine choice, finite quotient and global comparison are
all constructed internally. No geometric integrality, residue-preserving
lift, desired rank bound, diagram or defect-finiteness premise remains. -/
theorem projectiveIntersection_three_constants_globalDefect_ge_twice_point_degree
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hcop : Nat.Coprime ((toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1) 3) :
    letI : QuasiCompact ((scheme (projectiveIntersectionIdeal p q hp hq)).fromSpecStalk
      (genericPoint (scheme (projectiveIntersectionIdeal p q hp hq)))) :=
      integralGenericPointMap_quasiCompact (scheme (projectiveIntersectionIdeal p q hp hq))
    let N := ((scheme (projectiveIntersectionIdeal p q hp hq)).fromSpecStalk
      (genericPoint (scheme (projectiveIntersectionIdeal p q hp hq)))).normalization
    let ν := ((scheme (projectiveIntersectionIdeal p q hp hq)).fromSpecStalk
      (genericPoint (scheme (projectiveIntersectionIdeal p q hp hq)))).fromNormalization
    3 ∣ Module.finrank K (SchemeModuleOpenSectionsOver
      (ν ≫ toBase (projectiveIntersectionIdeal p q hp hq)) (SheafOfModules.unit N.ringCatSheaf) ⊤) →
    2 * (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 ≤
      Module.finrank K (SchemeModuleGlobalSectionsOver (toBase (projectiveIntersectionIdeal p q hp hq))
        (genericNormalizationQuotientSheaf (scheme (projectiveIntersectionIdeal p q hp hq)))) := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let G := SchemeModuleGlobalSectionsOver pi (genericNormalizationQuotientSheaf X)
  letI : Module.Finite K G :=
    projectiveIntersection_genericNormalizationQuotient_globalSections_finite p q hp hp0 n hq hnot
  change (3 ∣ Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
    (SheafOfModules.unit N.ringCatSheaf) ⊤)) → 2 * pi.residueDegree P.1 ≤ Module.finrank K G
  intro hthree
  obtain ⟨Q, hQP, hQthree⟩ :=
    integralProper_genericNormalization_exists_closedPoint_above_with_three_degree X pi P hthree
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
  have hcopQ : Nat.Coprime (pi.residueDegree (ν Q.1)) 3 := hQP.symm ▸ hcop
  have hbound := genericNormalization_originalAffineDefect_ge_twice_residueDegree
    X pi U.1 U.2 hfinite Q hQU hclosed hcopQ hQthree
  have hglobal := eGlobalNative.finrank_eq
  change 2 * pi.residueDegree (ν Q.1) ≤ Module.finrank K D at hbound
  rw [hQP] at hbound
  exact hbound.trans_eq hglobal.symm

end PfaffianDescent.Coray
