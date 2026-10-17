import PfaffianDescent.CorayProjectiveNormalizationCohomologyOneBoundCore
import PfaffianDescent.CorayProjectiveIntersectionCohomologyOneBound
import PfaffianDescent.CorayProjectiveNormalizationIntrinsicH1Finite

/-! The SAME actual intrinsic-normalization original-K surjection gives the
primitive normalization H¹ rank bound. The stronger correction inequality
retains the FULL actual global projection image σ and canonical quotient Q.
SOURCE ONLY / UNVERIFIED. No genus, normalization constants or RR premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The stronger actual quotient-defect correction inequality retains the
FULL global normalization-function projection range. It never replaces that
range by constants or by zero, and never assumes a desired genus drop. -/
theorem projectiveIntersection_genericNormalization_cohomology_one_bound_with_globalProjectionImage
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let pi := toBase I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    let σ := genericNormalizationHomQuotientLinearMap X pi
    Module.finrank K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) +
        Module.finrank K
          ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
            genericNormalizationQuotientSheaf X) ≤
      (1 + 3 * n * (n - 1) / 2) + Module.finrank K (LinearMap.range σ) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  letI : LocallyOfFiniteType pi := inferInstance
  let σ := genericNormalizationHomQuotientLinearMap X pi
  have hcorrection :=
    projectiveIntersection_genericNormalization_cohomology_one_finrank_with_globalProjectionImage
      p q hp hp0 n hq hnot
  have hcurve := projectiveIntersection_unit_cohomology_one_finrank_le_native
    p q hp hp0 n hn hq hnot
  dsimp only [I, X, pi, N, ν, σ] at hcorrection hcurve ⊢
  exact hcorrection.symm.le.trans
    (Nat.add_le_add_right hcurve (Module.finrank K (LinearMap.range σ)))

end PfaffianDescent.Coray
