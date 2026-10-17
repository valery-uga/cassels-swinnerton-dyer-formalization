import PfaffianDescent.CorayPerfectGenericNormalizationH1LinearSurjection
import PfaffianDescent.CorayPerfectOwnProjectiveNormalizationQuotientFinite

/-! SOURCE ONLY / UNVERIFIED. SAME OWN prime component and SAME actual
normalization over original perfect K. Primeness/actualP construct native
integrality;097 constructs whole actual Q closed support and actual affine
neighborhood internally. Only actual H1 SURJECTION is concluded, not H1
finite, a genus bound, constants=K, or a whole-CI substitution. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Small actual-component geometric cut. It contains no native Ext/H1
carrier or scalar action, and drops the two unused finite-section outputs. -/
private theorem selectedComponent_normalizationClosedAffineSupport
    {K : Type u} [Field K] [PerfectField K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
    IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf (scheme C))) ∧
      ∃ U : (scheme C).affineOpens,
        schemeModuleStalkSupport (genericNormalizationQuotientSheaf (scheme C)) ⊆ U.1 := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
  obtain ⟨hclosed, U, _hnonempty, hsU, _hPU⟩ :=
    (perfectField_selectedProjectivePrimeComponent_genericNormalizationQuotient_finite_sections_and_support
      p q hp hp0 n hq hnot C hIC hprime P).2.2
  exact ⟨hclosed, U, hsU⟩

/-- Small ordinary native application cut with X/pi abstract. All original
pi/nu>>pi Ext actions and SAME native normalization telescope are unchanged. -/
private theorem normalizationH1Surjective_of_closedAffineSupport
    {K : Type u} [Field K] [PerfectField K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (hgeometry : IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)) ∧
      ∃ U : X.affineOpens,
        schemeModuleStalkSupport (genericNormalizationQuotientSheaf X) ⊆ U.1) :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    Function.Surjective (perfectField_genericNormalizationCohomologyOneToNormalizationLinearMap X pi)  := by
  obtain ⟨hclosed, U, hsU⟩ := hgeometry
  exact perfectField_genericNormalization_intrinsicCohomologyOneLinearMap_surjective_of_closedSupport_subset_affine
    X pi hclosed U.1 U.2 hsU

/-- Construct the actual original-K map onto OWN normalization H1 from
original p,q,n and genuine OWN primeC/pointP, deriving every support and
comparison input. Full original fields/scalars and SAME nu are retained. -/
theorem perfectField_selectedProjectivePrimeComponent_genericNormalization_intrinsicCohomologyOneLinearMap_surjective
    {K : Type u} [Field K] [PerfectField K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver (toBase C)
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ toBase C)
    Function.Surjective
      (perfectField_genericNormalizationCohomologyOneToNormalizationLinearMap X (toBase C)) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
  letI : LocallyOfFiniteType (toBase C) := inferInstance
  exact normalizationH1Surjective_of_closedAffineSupport (scheme C) (toBase C)
    (selectedComponent_normalizationClosedAffineSupport p q hp hp0 n hq hnot C hIC hprime P)

end PfaffianDescent.Coray
