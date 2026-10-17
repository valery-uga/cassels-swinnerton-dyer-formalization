import PfaffianDescent.CorayProjectiveGeometricallyIntegralNormalizationConstants
import PfaffianDescent.CorayProjectiveNormalizationBaseEuler
import PfaffianDescent.CorayProjectiveIntersectionCohomologyOneBound
import PfaffianDescent.CorayNormalizationHomGroundAffineDefect
import Lean.Elab.Tactic.Omega

/-!
# Actual geometrically integral original-curve normalization genus/defect bound

SOURCE ONLY / UNVERIFIED. The C1 constant-rank leaf is a separate UNVERIFIED
prerequisite packet. Full-sigma BaseEuler and intrinsic rank identities plus
actual original-curve numerical H1 bound are accepted according to parent.
The actual projection rank zero is DERIVED from C1 and full rank balance;
it is never supplied. This yields the actual global normalization quotient
bound needed for source-faithful regularity. No native quotient-stalk comparison
or nonregularity-to-global-degree contribution is assumed or claimed here.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The FULL actual global normalization projection image has dimension0
for a geometrically integral original curve, by actual normalization H0 rank1
and the accepted full image balance. This conclusion is not a premise. -/
theorem projectiveIntersection_geometricallyIntegral_genericNormalization_globalProjectionImage_finrank_zero
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [GeometricallyIntegral (toBase (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let pi := toBase I
    letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton pi
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    let σ := genericNormalizationHomQuotientLinearMap X pi
    Module.finrank K (LinearMap.range σ) = 0 := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton pi
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  let σ := genericNormalizationHomQuotientLinearMap X pi
  have h0 := projectiveIntersection_genericNormalization_unit_topSections_finrank_eq_one_add_globalProjectionImage
    p q hp hp0 n hn hq hnot
  have hN := projectiveIntersection_geometricallyIntegral_genericNormalization_unit_topSections_finrank_eq_one
    p q hp hp0 n hn hq hnot
  dsimp only [I, X, pi, N, ν, σ] at h0 hN ⊢
  omega

/-- Actual normalization H1 plus the actual GLOBAL canonical quotient
section dimension is bounded by the original complete-intersection number.
Every dimension and action belongs to the same actual original-K schemes.
This is the source's genus/total-defect inequality; singularity contributions
and original-P regularity remain separate geometric work. -/
theorem projectiveIntersection_geometricallyIntegral_genericNormalization_cohomology_one_add_globalQuotient_finrank_le
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [GeometricallyIntegral (toBase (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let pi := toBase I
    letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton pi
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    Module.finrank K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) +
        Module.finrank K (SchemeModuleOpenSectionsOver pi
          (genericNormalizationQuotientSheaf X) ⊤) ≤
      1 + 3 * n * (n - 1) / 2 := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton pi
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
  have hσ := projectiveIntersection_geometricallyIntegral_genericNormalization_globalProjectionImage_finrank_zero
    p q hp hp0 n hn hq hnot
  have hidentity := projectiveIntersection_genericNormalization_cohomology_one_finrank_with_globalProjectionImage
    p q hp hp0 n hq hnot
  have hcurve := projectiveIntersection_unit_cohomology_one_finrank_le_native
    p q hp hp0 n hn hq hnot
  have hQ := (genericNormalizationUnitHomGroundLinearEquivOpenTop X pi).finrank_eq
  dsimp only [I, X, pi, N, ν, σ] at hσ hidentity hcurve hQ ⊢
  omega

end PfaffianDescent.Coray
