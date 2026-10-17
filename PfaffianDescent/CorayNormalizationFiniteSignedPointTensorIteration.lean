import PfaffianDescent.SchemeModuleFiniteSignedPointTensorIteration
import PfaffianDescent.CorayNormalizationClosedPointIncrementFiniteInduction

/-! Primitive actual finite signed point tensor iteration from SAME O_N.
Original p/q geometry, rank-one ideal charts, both base finite statements,
native Ext and original pi actions are internal. This constructs actual
finite/rank-one module sheaves and their weighted H0-H1 change; it does
not supply a meromorphic/pole or divisor identification or assert RR.
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

/-- Actual finite arbitrary signed point tensor operations on O_N, with
full residue degree at every step. No base/final finiteness, rank-one ideal,
HasExt or formula certificate is a primitive input. The list may contain
repetitions and both signs, and the empty list is the original unit. -/
theorem projectiveIntersection_genericNormalization_signedPointTensorIteration_finite_and_h0_h1_change
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
    ∀ ops : List (closedPoints N × Bool),
      let T := schemeModuleIteratedSignedClosedPointTensor O ops
      schemeModuleLocallyRankOne T ∧
        Module.Finite K (SchemeModuleOpenSectionsOver pi T ⊤) ∧
        Module.Finite K (schemeModuleCohomology N T 1) ∧
        (Module.finrank K (SchemeModuleOpenSectionsOver pi T ⊤) : ℤ) -
            Module.finrank K (schemeModuleCohomology N T 1) =
          (Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) : ℤ) -
            Module.finrank K (schemeModuleCohomology N O 1) +
            schemeModuleSignedClosedPointTensorWeightSum pi ops := by
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
  intro ops
  have hM : ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i) :=
    fun P => projectiveIntersection_genericNormalization_closedPoint_ideal_locallyRankOne
      p q hp hp0 n hn hq hnot P
  exact schemeModuleIteratedSignedClosedPointTensor_finite_and_h0_h1_change pi ops O hM hO h0 h1

end PfaffianDescent.Coray
