import PfaffianDescent.CorayOwnComponentProperConstants
import PfaffianDescent.CorayOriginalRegularClosedPointNormalizationLift

/-! Source-only follow-on: actual normalization constants divide original
point degree after the internally constructed degree-preserving regular-point
lift. No GI or constants-rank-one conclusion. Integer control explicitly
shows why the previous full-constants inequalities do not settle singular P. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original primitive integral p/q curve: WHEN the original P is regular,
the accepted canonical lift preserves its FULL original residue degree.
Applying the actual normalization constants field to that actual lift proves
rank divisibility and coprimality. Regularity remains a condition of this
additive lemma; it is not an external assumption added to the Coray endpoint. -/
theorem projectiveIntersection_genericNormalization_originalCoprimeClosedPoint_regular_implies_constantsRank_dvd_and_coprime
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hPcop : Nat.Coprime ((toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1) 3) :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    IsRegularLocalRing (X.presheaf.stalk P.1) →
      Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ toBase I)
        (SheafOfModules.unit N.ringCatSheaf) ⊤) ∣ (toBase I).residueDegree P.1 ∧
      Nat.Coprime (Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ toBase I)
        (SheafOfModules.unit N.ringCatSheaf) ⊤)) 3 := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  change IsRegularLocalRing (X.presheaf.stalk P.1) →
    Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) ∣ pi.residueDegree P.1 ∧
    Nat.Coprime (Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
      (SheafOfModules.unit N.ringCatSheaf) ⊤)) 3
  intro hregular
  letI : IsIntegral N := inferInstance
  letI : IsFinite ν := integralScheme_genericNormalization_isFinite X pi
  letI : IsProper (ν ≫ pi) := inferInstance
  have hLift := projectiveIntersection_genericNormalization_regularClosedPoint_exists_degree_preserving_lift
    p q hp hp0 n hq hnot P hregular
  let Q : closedPoints N := Classical.choose hLift
  have hDegree : (ν ≫ pi).residueDegree Q.1 = pi.residueDegree P.1 :=
    (Classical.choose_spec hLift).2.2.2
  have hdiv := integralProper_originalUnitSections_finrank_dvd_residueDegree (ν ≫ pi) Q
  have hdivP : Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ pi)
      (SheafOfModules.unit N.ringCatSheaf) ⊤) ∣ pi.residueDegree P.1 := by
    rw [← hDegree]
    exact hdiv
  exact ⟨hdivP, hPcop.coprime_dvd_left hdivP⟩

end PfaffianDescent.Coray
