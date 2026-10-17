import PfaffianDescent.CorayOriginalPointAffineNormalizationDefectBound
import PfaffianDescent.CorayOriginalRegularClosedPointNormalizationLift
import PfaffianDescent.CorayProjectiveGeometricallyIntegralNormalizationDefectBound

/-! SOURCE ONLY / UNVERIFIED. The strict manuscript case is a genus/defect
contradiction, with genuine original K and all residue conjugates retained.
No regularity premise, native Q-stalk comparison premise, residue-degree-one
premise or desired degree inequality is used. GI remains the genuine branch
hypothesis; its construction and the reducible branch are not discharged. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- On the actual integral original curve, a nonregular original point
contributes its FULL original degree to the actual GLOBAL normalization
quotient. The chosen affine contains the point AND all quotient support;
finite native normalization and every localization bound are derived. -/
theorem projectiveIntersection_genericNormalization_nonregular_originalClosedPoint_degree_le_globalDefect
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hsing : ¬ IsRegularLocalRing
      ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk P.1)) :
    (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 ≤
      finrank K (SchemeModuleGlobalSectionsOver
        (toBase (projectiveIntersectionIdeal p q hp hq))
        (genericNormalizationQuotientSheaf (scheme (projectiveIntersectionIdeal p q hp hq)))) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  let Q := genericNormalizationQuotientSheaf X
  obtain ⟨U, hnonempty, hxU, ⟨E⟩⟩ :=
    projectiveIntersection_genericNormalizationQuotient_exists_globalSectionsEquiv_affineDefect
      p q hp hp0 n hq hnot P.1
  letI : Nonempty U.1 := hnonempty
  letI : Module.Finite K (SchemeModuleGlobalSectionsOver pi Q) :=
    projectiveIntersection_genericNormalizationQuotient_globalSections_finite p q hp hp0 n hq hnot
  let beta : K →+* Γ(X, U.1) :=
    (pi.appLE ⊤ U.1 (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let D := (ModuleCat.restrictScalars beta).obj
    (ModuleCat.of Γ(X, U.1) (localNormalizationDefect Γ(X, U.1) X.functionField))
  have hfinite : Module.Finite K D := Module.Finite.equiv E
  have hdim := projectiveIntersection_original_stalk_ringKrullDim_le_one p q hp hp0 n hq hnot P.1
  have hlocal := genericNormalization_originalClosedPoint_nonregular_degree_le_affineDefect
    X pi U.1 U.2 P hxU hdim hsing hfinite
  exact hlocal.trans E.finrank_eq.symm.le

/-- Strict d>G_n forces the OWN original point to be regular on a genuine
geometrically integral original curve. Normalization constants and sigma0
are derived in the separate C1/global bound leaf, never assumed here. The
case d=G_n needs extra singularities and an additive support bound. -/
theorem projectiveIntersection_geometricallyIntegral_originalClosedPoint_isRegularLocalRing_of_degree_gt
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [GeometricallyIntegral (toBase (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hdegree : 1 + 3 * n * (n - 1) / 2 <
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1) :
    IsRegularLocalRing ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk P.1) := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton pi
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let Q := genericNormalizationQuotientSheaf X
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  by_contra hsing
  have hpoint := projectiveIntersection_genericNormalization_nonregular_originalClosedPoint_degree_le_globalDefect
    p q hp hp0 n hq hnot P hsing
  have htop := (schemeModuleGlobalSectionsLinearEquivOpenTop pi Q).finrank_eq
  have hupper := projectiveIntersection_geometricallyIntegral_genericNormalization_cohomology_one_add_globalQuotient_finrank_le
    p q hp hp0 n hn hq hnot
  dsimp only [I, X, pi, N, ν, Q] at hpoint htop hupper ⊢
  omega

end PfaffianDescent.Coray
