import PfaffianDescent.CorayProjectiveNormalizationIntrinsicH1FiniteCore
import Mathlib.Tactic.Trace
import PfaffianDescent.CorayProjectiveIntersectionIntrinsicH1Finite
import PfaffianDescent.CorayProjectiveNormalizationLowDegreeLinearExact
import PfaffianDescent.CorayProjectiveNormalizationFiniteCorrection
import Mathlib.RingTheory.Finiteness.Basic

/-! Finite intrinsic normalization H¹ over the ORIGINAL K for the SAME
literal integral p/q curve. The canonical inclusion, actual quotient Q,
actual normalization comparison and full global projection image are retained.
No constants equality, genus, source-H¹ finite or comparison certificate is
an input of either primitive endpoint. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ordinary finite-dimensional surjective rank-nullity combined with the
given full correction equality. The geometric maps remain parameters. -/
private theorem finrank_surjective_with_full_projection_correction
    {F : Type*} [Field F] {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module F A] [Module F B] [Module F C] [Module F D]
    [hFinite : Module.Finite F A] (g : A →ₗ[F] B) (σ : D →ₗ[F] C)
    (hsurj : Function.Surjective g)
    (hcorrection : Module.finrank F g.ker + Module.finrank F (LinearMap.range σ) =
      Module.finrank F C) :
    Module.finrank F A + Module.finrank F (LinearMap.range σ) =
      Module.finrank F B + Module.finrank F C := by
  have hdim := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hdim
  calc
    Module.finrank F A + Module.finrank F (LinearMap.range σ) =
        (Module.finrank F B + Module.finrank F g.ker) +
          Module.finrank F (LinearMap.range σ) := by rw [hdim]
    _ = Module.finrank F B +
        (Module.finrank F g.ker + Module.finrank F (LinearMap.range σ)) :=
      Nat.add_assoc _ _ _
    _ = Module.finrank F B + Module.finrank F C := by rw [hcorrection]

/-- The genuine finite-dimensional correction identity keeps the FULL
actual global normalization-function projection image σ. No equality of
constant fields or vanishing of σ is asserted. Both intrinsic H¹ groups
are proved finite from the original equations, and the existing actual
correction law is combined with rank-nullity for the SAME canonical g. -/
theorem projectiveIntersection_genericNormalization_cohomology_one_finrank_with_globalProjectionImage
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let pi := toBase I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
      integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
    letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
    let σ := genericNormalizationHomQuotientLinearMap X pi
    Module.finrank K (schemeModuleCohomology X (SheafOfModules.unit X.ringCatSheaf) 1) +
        Module.finrank K (LinearMap.range σ) =
      Module.finrank K (schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1) +
        Module.finrank K
          ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
            genericNormalizationQuotientSheaf X) := by
  trace "INTRARGS005 P00 second proof entry"
  intro I X pi N ν σ
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) :=
    integralGenericPointMap_quasiCompact X
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  letI hFiniteType : LocallyOfFiniteType pi :=
    @IsProper.toLocallyOfFiniteType _ _ (toBase I) (isProper_toBase I)
  letI : Module.Finite K (schemeModuleCohomology X
      (SheafOfModules.unit X.ringCatSheaf) 1) :=
    projectiveIntersection_unit_cohomology_one_finite_native p q hp hp0 n hq hnot
  letI : Module.Finite K (schemeModuleCohomology N
      (SheafOfModules.unit N.ringCatSheaf) 1) :=
    projectiveIntersection_genericNormalization_unit_cohomology_one_finite_native
      p q hp hp0 n hq hnot
  let g := genericNormalizationCohomologyOneToNormalizationLinearMap X pi
  have hsurj : Function.Surjective g :=
    (projectiveIntersection_genericNormalization_lowDegreeLinearExact_surjective_and_kernel
      p q hp hp0 n hq hnot).2.2.1
  have hcorrection :=
    projectiveIntersection_genericNormalizationCohomologyOneToNormalization_ker_finite_and_finrank
      p q hp hp0 n hq hnot
  have hcorrectionEq := hcorrection.2
  trace "INTRARGS005 G00 actual correction projection formed"
  let sourceFinite : Module.Finite K
      (schemeModuleCohomology X (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1) :=
    inferInstance
  trace "INTRARGS005 G01 SAME original source finite instance pinned"
  let mapsApplied := finrank_surjective_with_full_projection_correction
    (F := K)
    (A := schemeModuleCohomology X
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 1)
    (B := schemeModuleCohomology N (SheafOfModules.unit N.ringCatSheaf) 1)
    (C := ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      genericNormalizationQuotientSheaf X))
    (D := ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward ν).obj (SheafOfModules.unit N.ringCatSheaf)))
    (hFinite := sourceFinite) g σ
  trace "INTRARGS005 G02 actual g and sigma argument application formed"
  let surjApplied := mapsApplied hsurj
  trace "INTRARGS005 G03 actual surjectivity argument application formed"
  have hresult := surjApplied (by
    trace "INTRHELP014 N00 native correction cut entry"
    unfold g
    trace "INTRHELP014 N01 original g local definition substituted"
    unfold hFiniteType
    trace "INTRHELP014 N02 original canonical finite-type proof substituted"
    dsimp only [I, X, pi, N, ν, σ]
    trace "INTRHELP014 N03 remaining original local geometry aliases normalized"
    exact hcorrectionEq
    trace "INTRHELP014 N04 original correction proof matched"
  )
  trace "INTRARGS005 G04 actual correction argument application formed"
  exact hresult
  trace "INTRARGS005 G05 final target matched"

end PfaffianDescent.Coray
