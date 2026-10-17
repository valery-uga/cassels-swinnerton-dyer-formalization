import PfaffianDescent.CorayProjectiveNormalizationBaseEuler
import PfaffianDescent.CorayProjectiveIntersectionCohomologyOneBound
import PfaffianDescent.CorayNormalizationFiniteSignedPointTensorIteration

/-! Actual original-K normalization base Euler and signed-word positivity.
The full sigma image is retained in the imported actual H0/H1 identities and
cancels there algebraically. The full quotient defect and all signed residue
degrees are retained here. No H0(N)=K, nonzero section or pole identification
is assumed; the weight window derives an existential nonzero actual section. SOURCE ONLY / UNVERIFIED; root owns compilation and acceptance.
All three direct imports are pending, including the unregistered BaseEuler. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pure arithmetic cut: scheme/module dictionaries never enter omega. -/
private theorem integer_euler_and_h0_pos_of_lower_bound
    (B w : ℤ) (delta a b : ℕ)
    (hw : B ≤ w + (delta : ℤ))
    (hlower : 1 - B + (delta : ℤ) + w ≤ (a : ℤ) - (b : ℤ)) :
    0 < (a : ℤ) - (b : ℤ) ∧ 0 < a := by
  omega

/-- Pure arithmetic cut for the weaker numerical window. -/
private theorem integer_weight_add_nat_ge_of_weight_ge
    (B w : ℤ) (delta : ℕ) (hw : B ≤ w) :
    B ≤ w + (delta : ℤ) := by
  omega

/-- The actual base H0-minus-H1 plus ANY integer weight has the numerical
lower bound from the SAME original-curve H1 bound, with the actual quotient
defect retained. There is no premise about normalization constants. -/
theorem projectiveIntersection_genericNormalization_unit_baseEuler_add_weight_lowerBound
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (w : ℤ)
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let piX := toBase I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver piX
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ piX)
    1 - ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ) +
        (Module.finrank K (SchemeModuleGlobalSectionsOver piX
          (genericNormalizationQuotientSheaf X)) : ℤ) + w ≤
      (Module.finrank K (SchemeModuleOpenSectionsOver (ν ≫ piX)
          (SheafOfModules.unit N.ringCatSheaf) ⊤) : ℤ) -
        (Module.finrank K (schemeModuleCohomology N
          (SheafOfModules.unit N.ringCatSheaf) 1) : ℤ) + w := by
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let piX := toBase I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver piX
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ piX)
  have hbase := projectiveIntersection_genericNormalization_unit_baseEuler_eq_curveH1_and_quotient
    p q hp hp0 n hn hq hnot
  have hcurve := projectiveIntersection_unit_cohomology_one_finrank_le_native
    p q hp hp0 n hn hq hnot
  dsimp only [I, X, piX, N, ν] at hbase hcurve ⊢
  omega

/-- The actual finite signed tensor word has its exact Euler number over
the original K and the numerical lower bound with FULL quotient defect.
Rank-one geometry and finite H0/H1 are produced by the actual iteration;
there is no final-finiteness, Euler-change or section certificate premise. -/
theorem projectiveIntersection_genericNormalization_signedPointTensorIteration_finite_euler_eq_and_lowerBound
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let piX := toBase I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := ν ≫ piX
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver piX
    letI : Linear K N.Modules := schemeModulesLinearOver pi
    let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
    ∀ ops : List (closedPoints N × Bool),
      let T := schemeModuleIteratedSignedClosedPointTensor O ops
      schemeModuleLocallyRankOne T ∧
        Module.Finite K (SchemeModuleOpenSectionsOver pi T ⊤) ∧
        Module.Finite K (schemeModuleCohomology N T 1) ∧
        ((Module.finrank K (SchemeModuleOpenSectionsOver pi T ⊤) : ℤ) -
          (Module.finrank K (schemeModuleCohomology N T 1) : ℤ) =
            1 - (Module.finrank K (schemeModuleCohomology X
              (SheafOfModules.unit X.ringCatSheaf) 1) : ℤ) +
              (Module.finrank K (SchemeModuleGlobalSectionsOver piX
                (genericNormalizationQuotientSheaf X)) : ℤ) +
              schemeModuleSignedClosedPointTensorWeightSum pi ops) ∧
        (1 - ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ) +
          (Module.finrank K (SchemeModuleGlobalSectionsOver piX
            (genericNormalizationQuotientSheaf X)) : ℤ) +
          schemeModuleSignedClosedPointTensorWeightSum pi ops ≤
            (Module.finrank K (SchemeModuleOpenSectionsOver pi T ⊤) : ℤ) -
              (Module.finrank K (schemeModuleCohomology N T 1) : ℤ)) := by
  intro I X piX N ν pi O ops T
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver piX
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  obtain ⟨hrank, h0, h1, hchange⟩ :=
    projectiveIntersection_genericNormalization_signedPointTensorIteration_finite_and_h0_h1_change
      p q hp hp0 n hn hq hnot ops
  have hbase :
      (Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) : ℤ) -
          (Module.finrank K (schemeModuleCohomology N O 1) : ℤ) =
        1 - (Module.finrank K (schemeModuleCohomology X
          (SheafOfModules.unit X.ringCatSheaf) 1) : ℤ) +
          (Module.finrank K (SchemeModuleGlobalSectionsOver piX
            (genericNormalizationQuotientSheaf X)) : ℤ) :=
    projectiveIntersection_genericNormalization_unit_baseEuler_eq_curveH1_and_quotient
      p q hp hp0 n hn hq hnot
  have hlower :
      1 - ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ) +
          (Module.finrank K (SchemeModuleGlobalSectionsOver piX
            (genericNormalizationQuotientSheaf X)) : ℤ) +
          schemeModuleSignedClosedPointTensorWeightSum pi ops ≤
        (Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) : ℤ) -
          (Module.finrank K (schemeModuleCohomology N O 1) : ℤ) +
          schemeModuleSignedClosedPointTensorWeightSum pi ops :=
    projectiveIntersection_genericNormalization_unit_baseEuler_add_weight_lowerBound
      p q hp hp0 n hn hq hnot (schemeModuleSignedClosedPointTensorWeightSum pi ops)
  refine ⟨hrank, h0, h1, ?_, ?_⟩
  · exact hchange.trans
      (congrArg (fun t : ℤ => t + schemeModuleSignedClosedPointTensorWeightSum pi ops) hbase)
  · exact hlower.trans_eq hchange.symm

/-- A sufficient SHARPER weight window includes the actual quotient defect.
It proves positive Euler number and positive dimension of actual sections;
it neither assumes nor constructs a nonzero section, meromorphic function,
pole image or divisor. No constant-field simplification is used. -/
theorem projectiveIntersection_genericNormalization_signedPointTensorIteration_euler_and_h0_pos_of_weight_add_quotient_ge_bound
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let piX := toBase I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := ν ≫ piX
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K N.Modules := schemeModulesLinearOver pi
    let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
    ∀ ops : List (closedPoints N × Bool),
      let T := schemeModuleIteratedSignedClosedPointTensor O ops
      ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ) ≤
          schemeModuleSignedClosedPointTensorWeightSum pi ops +
          (Module.finrank K (SchemeModuleGlobalSectionsOver piX
            (genericNormalizationQuotientSheaf X)) : ℤ) →
        0 < (Module.finrank K (SchemeModuleOpenSectionsOver pi T ⊤) : ℤ) -
          (Module.finrank K (schemeModuleCohomology N T 1) : ℤ) ∧
        0 < Module.finrank K (SchemeModuleOpenSectionsOver pi T ⊤) := by
  intro I X piX N ν pi O ops T hw
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver piX
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  have h := projectiveIntersection_genericNormalization_signedPointTensorIteration_finite_euler_eq_and_lowerBound
    p q hp hp0 n hn hq hnot ops
  exact integer_euler_and_h0_pos_of_lower_bound
    ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ)
    (schemeModuleSignedClosedPointTensorWeightSum pi ops)
    (Module.finrank K (SchemeModuleGlobalSectionsOver piX (genericNormalizationQuotientSheaf X)))
    (Module.finrank K (SchemeModuleOpenSectionsOver pi T ⊤))
    (Module.finrank K (schemeModuleCohomology N T 1)) hw h.2.2.2.2

/-- The simpler original-curve numerical window drops only the nonnegative
quotient gain, and proves the SAME actual word's Euler/H0 positivity. -/
theorem projectiveIntersection_genericNormalization_signedPointTensorIteration_euler_and_h0_pos_of_weight_ge_bound
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let piX := toBase I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := ν ≫ piX
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K N.Modules := schemeModulesLinearOver pi
    let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
    ∀ ops : List (closedPoints N × Bool),
      let T := schemeModuleIteratedSignedClosedPointTensor O ops
      ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ) ≤
          schemeModuleSignedClosedPointTensorWeightSum pi ops →
        0 < (Module.finrank K (SchemeModuleOpenSectionsOver pi T ⊤) : ℤ) -
          (Module.finrank K (schemeModuleCohomology N T 1) : ℤ) ∧
        0 < Module.finrank K (SchemeModuleOpenSectionsOver pi T ⊤) := by
  intro I X piX N ν pi O ops T hw
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  apply projectiveIntersection_genericNormalization_signedPointTensorIteration_euler_and_h0_pos_of_weight_add_quotient_ge_bound
    p q hp hp0 n hn hq hnot ops
  exact integer_weight_add_nat_ge_of_weight_ge
    ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ)
    (schemeModuleSignedClosedPointTensorWeightSum pi ops)
    (Module.finrank K (SchemeModuleGlobalSectionsOver piX (genericNormalizationQuotientSheaf X))) hw

/-- The SAME numerical weight window DERIVES a nonzero actual word section
from proved positive H0 dimension. This is a section of the original literal
fold, so no word equivalence, transported scalar action or section-existence
certificate is a premise. The choice is existential, with no pole/cycle claim. -/
theorem projectiveIntersection_genericNormalization_signedPointTensorIteration_exists_nonzero_topSection_of_weight_ge_bound
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := ν ≫ toBase I
    ∀ ops : List (closedPoints N × Bool),
      let T := schemeModuleIteratedSignedClosedPointTensor
        (SheafOfModules.unit N.ringCatSheaf) ops
      ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ) ≤
          schemeModuleSignedClosedPointTensorWeightSum pi ops →
        ∃ s : SchemeModuleOpenSectionsOver pi T ⊤, s ≠ 0 := by
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := ν ≫ toBase I
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  intro ops hw
  have h := projectiveIntersection_genericNormalization_signedPointTensorIteration_euler_and_h0_pos_of_weight_ge_bound
    p q hp hp0 n hn hq hnot ops hw
  letI := Module.nontrivial_of_finrank_pos h.2
  exact exists_ne 0

end PfaffianDescent.Coray
