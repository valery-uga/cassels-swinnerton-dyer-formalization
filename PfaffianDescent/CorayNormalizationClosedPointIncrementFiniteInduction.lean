import PfaffianDescent.SchemeModulePointIncrementFiniteEuler
import PfaffianDescent.CorayNormalizationClosedPointTensorDualIncrement
import PfaffianDescent.CorayNormalizationGlobalUnitSectionsFinite
import PfaffianDescent.CorayProjectiveNormalizationIntrinsicH1FiniteCore
import PfaffianDescent.CorayFiniteSchemeGenericNormalization

/-! Primitive base for genuine positive AND negative tensor point induction.
SAME original normalization, point ideal, dual, maps and independently
pi-induced scalar actions. Both base finiteness results, native HasExt and
actual point-ideal rank-one geometry are discharged internally. The full
normalization constants remain in the H0-H1 formula. No H0(N)=K, divisor,
pole, higher-degree Euler, genus or RR identification is concluded.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual first positive and negative tensor steps from O_N. This
primitive endpoint has no supplied finiteness, HasExt, rank-one ideal,
cohomology vanishing, exactness, fiber dimension or comparison certificate.
Its two actual new coefficients have the rank-one geometry and finite
H0/H1 required for further applications of the generic induction steps. -/
theorem projectiveIntersection_genericNormalization_unit_pointIncrements_finite_and_h0_h1_changes
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K N.Modules := schemeModulesLinearOver pi
    let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show N.Modules from closedImmersionModule i)
      let T := schemeModuleTensor O (SchemeModuleInternalHom.dual M)
      let R := schemeModuleTensor M O
      (schemeModuleLocallyRankOne T ∧
        Module.Finite K (SchemeModuleOpenSectionsOver pi T ⊤) ∧
        Module.Finite K (schemeModuleCohomology N T 1) ∧
        (Module.finrank K (SchemeModuleOpenSectionsOver pi T ⊤) : ℤ) -
            Module.finrank K (schemeModuleCohomology N T 1) =
          (Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) : ℤ) -
            Module.finrank K (schemeModuleCohomology N O 1) + pi.residueDegree P.1) ∧
      (schemeModuleLocallyRankOne R ∧
        Module.Finite K (SchemeModuleOpenSectionsOver pi R ⊤) ∧
        Module.Finite K (schemeModuleCohomology N R 1) ∧
        (Module.finrank K (SchemeModuleOpenSectionsOver pi R ⊤) : ℤ) -
            Module.finrank K (schemeModuleCohomology N R 1) =
          (Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) : ℤ) -
            Module.finrank K (schemeModuleCohomology N O 1) - pi.residueDegree P.1) := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  letI : IsFinite nu := integralScheme_genericNormalization_isFinite X (toBase I)
  letI : LocallyOfFiniteType pi := inferInstance
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
  have hO : schemeModuleLocallyRankOne O := by
    intro x
    exact ⟨⊤, by simp, ⟨Iso.refl _⟩⟩
  have h0 : Module.Finite K (SchemeModuleOpenSectionsOver pi O ⊤) :=
    projectiveIntersection_genericNormalization_unit_topSections_finite_native p q hp hp0 n hn hq hnot
  have h1 : Module.Finite K (schemeModuleCohomology N O 1) :=
    projectiveIntersection_genericNormalization_unit_cohomology_one_finite_native p q hp hp0 n hq hnot
  intro P
  have hM := projectiveIntersection_genericNormalization_closedPoint_ideal_locallyRankOne
    p q hp hp0 n hn hq hnot P
  exact ⟨schemeModuleClosedPoint_positiveIncrement_finite_and_h0_h1_change pi P O hM hO h0 h1,
    schemeModuleClosedPoint_negativeIncrement_finite_and_h0_h1_change pi P O hM hO h0 h1⟩

end PfaffianDescent.Coray
