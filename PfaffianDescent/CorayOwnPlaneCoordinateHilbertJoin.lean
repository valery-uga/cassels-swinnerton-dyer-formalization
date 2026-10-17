import PfaffianDescent.CorayWholeIdealRestrictionHomogeneousKernel
import PfaffianDescent.CorayWholeIdealGradeRestriction
import PfaffianDescent.CorayWholeSurfaceIdealGradeHilbertRank
import PfaffianDescent.CorayOriginalWholePlaneIdealNativeHZeroInjection
import PfaffianDescent.CorayComponentHilbertCoefficientInvariance
import PfaffianDescent.CorayActualComponentHilbertDegree
import PfaffianDescent.CorayLinearGradeExactSequence
import PfaffianDescent.CorayPlaneCubicHilbertFunction
import PfaffianDescent.ProjectivePositiveGlobalSectionsLinear
import Mathlib.Tactic.Linarith

/-! SOURCE ONLY / UNVERIFIED. Actual one-sided graded restriction and native
H0 bounds for the SAME component and ENTIRE generic plane cut. This module
imports no229/positive-Euler or desired genus producer. Native H0 finiteness
is the honest future capability input; NO numerical spectrum, genus/Hodge,
GI, incidence, or restriction-surjectivity certificate is assumed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open ProjectiveNegativeTwist
open scoped BigOperators
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

private theorem wholeIdealGrade_finite_of_grade001
    {A : Type u} [CommRing A] [Algebra K A]
    (G : ℕ → Submodule K A) (J : Ideal A) (d : ℕ)
    [Module.Finite K (G d)] : Module.Finite K (wholeIdealGrade G J d) := by
  let h : wholeIdealGrade G J d ≤ G d := inf_le_right
  exact Module.Finite.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

private theorem quotientCoordinateGrade_finite001
    {σ : Type} [Finite σ]
    (I : HomogeneousIdeal (homogeneousSubmodule σ K)) (d : ℕ) :
    Module.Finite K (grading I d) := by
  change Module.Finite K ((homogeneousSubmodule σ K d).map
    (Ideal.Quotient.mkₐ K I.toIdeal).toLinearMap)
  infer_instance

/-- The actual surface quotient restriction preserves the actual quotient
homogeneous degree, using the SAME original polynomial representative. -/
theorem surfacePlaneCoordinateRestriction_mem_grading001
    (t : Fin 3 → K) (p : MvPolynomial (Fin 4) K) {e : ℕ}
    (hp : p.IsHomogeneous e) (d : ℕ)
    (x : CoordinateRing (equationIdeal p hp)) (hx : x ∈ grading (equationIdeal p hp) d) :
    surfacePlaneCoordinateRestriction t p hp x ∈
      grading (equationIdeal (planeHyperplaneRestrictionHom t p)
        (planeHyperplaneRestrictionHom_homogeneous t p hp)) d := by
  obtain ⟨q, hq, hqx⟩ := hx
  rw [← hqx]
  change surfacePlaneCoordinateRestriction t p hp
    (Ideal.Quotient.mk (equationIdeal p hp).toIdeal q) ∈ _
  rw [surfacePlaneCoordinateRestriction_mk]
  exact ⟨planeHyperplaneRestrictionHom t q,
    planeHyperplaneRestrictionHom_homogeneous t q hq, rfl⟩

/-- Genuine one-sided grade inequality for the SAME whole surface ideal
and ENTIRE plane-cut ideal. A prime/nonempty component supplies the actual
kernel coefficient; no image-surjectivity or numerical bound is assumed. -/
theorem wholeOriginalSurfaceToPlaneCutIdealGrade_finrank_step001
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hpC : p ∈ C.toIdeal) (hprime : C.toIdeal.IsPrime) (x0 : scheme C) (d : ℕ) :
    let F := GenericHyperplaneField K
    let I := equationIdeal (p.map (algebraMap K F)) (hp.map _)
    let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
    finrank F (wholeIdealGrade (grading I) (wholeOriginalSurfaceCoordinateIdeal C p hp) (d + 1)) ≤
      finrank F (wholeIdealGrade (grading I) (wholeOriginalSurfaceCoordinateIdeal C p hp) d) +
        finrank F (wholeIdealGrade (grading E) (wholeOriginalPlaneCutCoordinateIdeal C p hp) (d + 1)) := by
  let F := GenericHyperplaneField K
  let f := p.map (algebraMap K F)
  let hf := hp.map (algebraMap K F)
  let t := genericHyperplaneCoefficient (K := K)
  let I := equationIdeal f hf
  let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
  let G := grading I
  let T := grading E
  let J := wholeOriginalSurfaceCoordinateIdeal C p hp
  let Q := wholeOriginalPlaneCutCoordinateIdeal C p hp
  let r := surfacePlaneCoordinateRestriction t f hf
  let H := Ideal.Quotient.mk I.toIdeal (genericHyperplaneEquation (K := K))
  letI : ∀ k, Module.Finite F (G k) := fun k => quotientCoordinateGrade_finite001 I k
  letI : ∀ k, Module.Finite F (T k) := fun k => quotientCoordinateGrade_finite001 E k
  letI : ∀ k, Module.Finite F (wholeIdealGrade G J k) := fun k =>
    wholeIdealGrade_finite_of_grade001 G J k
  letI : ∀ k, Module.Finite F (wholeIdealGrade T Q k) := fun k =>
    wholeIdealGrade_finite_of_grade001 T Q k
  have hr : ∀ k y, y ∈ G k → r y ∈ T k := by
    intro k y hy
    exact surfacePlaneCoordinateRestriction_mem_grading001 t f hf k y hy
  have hJ : ∀ y, y ∈ J → r y ∈ Q := by
    intro y hy
    exact wholeOriginalSurfaceCoordinateIdealRestriction_mem_planeCut C p hp ⟨y, hy⟩
  have hkernel : ∀ y, y ∈ J → r y = 0 → ∃ z, z ∈ J ∧ H * z = y := by
    intro y hy hz
    have hz' : wholeOriginalSurfaceCoordinateIdealRestriction C p hp ⟨y, hy⟩ = 0 := hz
    obtain ⟨z, hzy⟩ := (wholeOriginalSurfaceCoordinateIdealRestriction_eq_zero_iff
      C p hp hpC hprime x0 ⟨y, hy⟩).mp hz'
    exact ⟨z.val, z.property, congrArg Subtype.val hzy⟩
  exact wholeIdealGradeRestriction_finrank_le G T J Q
    (wholeOriginalSurfaceCoordinateIdeal_isHomogeneous C p hp) r hr hJ H
    (wholeOriginalSurfaceHyperplaneCoordinate_mem_degree_one p hp)
    (surfacePlaneCoordinateRestriction_hyperplane t f hf) hkernel d

/-- Exact grade equivalence for the actual (p,H) quotient and actual Fin3
plane cubic, built from the already checked literal inverse graded maps. -/
def planeSectionCoordinateGradeLinearEquiv001
    (t : Fin 3 → K) (p : MvPolynomial (Fin 4) K) {e : ℕ}
    (hp : p.IsHomogeneous e) (d : ℕ) :
    grading (planeSectionHomogeneousIdeal t p hp) d ≃ₗ[K]
      grading (equationIdeal (planeHyperplaneRestrictionHom t p)
        (planeHyperplaneRestrictionHom_homogeneous t p hp)) d where
  toFun x := ⟨planeSectionQuotientRestriction t p hp x.val,
    (planeSectionGradedRestriction t p hp).map_mem x.property⟩
  invFun y := ⟨planeSectionQuotientInclusion t p hp y.val,
    (planeSectionGradedInclusion t p hp).map_mem y.property⟩
  left_inv x := Subtype.ext
    (AlgHom.congr_fun (planeSectionQuotientInclusion_comp_restriction t p hp) x.val)
  right_inv y := Subtype.ext
    (AlgHom.congr_fun (planeSectionQuotientRestriction_comp_inclusion t p hp) y.val)
  map_add' x y := Subtype.ext (map_add (planeSectionQuotientRestriction t p hp) x.val y.val)
  map_smul' c x := Subtype.ext (map_smul (planeSectionQuotientRestriction t p hp) c x.val)

/-- Actual generic hyperplane restriction gives exact surface Hilbert
increment 3(d+1), including d=0. No Hilbert-polynomial premise. -/
theorem smoothCubic_genericSurface_coordinateHilbert_step001
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (d : ℕ) :
    let F := GenericHyperplaneField K
    let I := equationIdeal (p.map (algebraMap K F)) (hp.map _)
    finrank F (grading I (d + 1)) = finrank F (grading I d) + 3 * (d + 1) := by
  let F := GenericHyperplaneField K
  let f := p.map (algebraMap K F)
  let hf := hp.map (algebraMap K F)
  let I := equationIdeal f hf
  let H := genericHyperplaneEquation (K := K)
  let hH := genericHyperplaneEquation_isHomogeneous (K := K)
  let t := genericHyperplaneCoefficient (K := K)
  have hf0 : f ≠ 0 := by
    intro hz
    apply hp0
    exact (MvPolynomial.map_injective (algebraMap K F)
      (FaithfulSMul.algebraMap_injective K F)) (by simpa using hz)
  letI : Smooth (hypersurfaceToBase f hf) :=
    smooth_hypersurfaceToBase_map (algebraMap K F) p hp
  letI : I.toIdeal.IsPrime :=
    Ideal.isPrime_span_singleton_of_prime
      (irreducible_of_smooth_homogeneous_cubic_of_field f hf hf0).prime
  have hH0 : H ≠ 0 := genericHyperplaneEquation_ne_zero
  have hnot : H ∉ I.toIdeal := by
    intro hm
    have hdiv : f ∣ H := Ideal.mem_span_singleton.mp hm
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hH0
    rw [hf.totalDegree hf0, hH.totalDegree hH0] at hle
    omega
  have hstep := componentLinearGrade_hilbertFunction_recurrence I H hH hnot d
  have hcut : finrank F (grading (I ⊔ equationIdeal H hH) (d + 1)) = 3 * (d + 1) := by
    exact (planeSectionCoordinateGradeLinearEquiv001 t f hf (d + 1)).finrank_eq.trans
      (planeCubicCoordinateGrade_finrank_eq_three_mul (genericPlaneCubic p)
        (genericPlaneCubic_isHomogeneous p hp) (genericPlaneCubic_ne_zero p hp hp0)
        (d + 1) (by omega))
  rw [hcut] at hstep
  exact hstep

/-- The genuine coordinate Hilbert increment on the ORIGINAL field K is
bounded below by the actual ENTIRE generic plane-ideal grade deficit.
Coefficient extension compares only actual coordinate grades, never H1. -/
theorem wholeOriginalComponent_coordinateHilbert_step_planeIdealGrade001
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hpC : p ∈ C.toIdeal) (hprime : C.toIdeal.IsPrime) (x0 : scheme C) (d : ℕ) :
    let F := GenericHyperplaneField K
    let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
    finrank K (grading C d) + 3 * (d + 1) ≤ finrank K (grading C (d + 1)) +
      finrank F (wholeIdealGrade (grading E) (wholeOriginalPlaneCutCoordinateIdeal C p hp) (d + 1)) := by
  let F := GenericHyperplaneField K
  let I := equationIdeal (p.map (algebraMap K F)) (hp.map _)
  let CF := wholeGenericCurveIdeal C
  have hIC : I.toIdeal ≤ CF.toIdeal :=
    equationIdeal_le_homogeneousIdeal_of_mem (hp.map _)
      (originalEquation_mem_wholeGenericCurveIdeal C p hpC)
  have hprev := homogeneousQuotientGrade_finrank_add_wholeIdealGrade I CF hIC d
  have hnext := homogeneousQuotientGrade_finrank_add_wholeIdealGrade I CF hIC (d + 1)
  change finrank F (grading CF d) +
    finrank F (wholeIdealGrade (grading I) (wholeOriginalSurfaceCoordinateIdeal C p hp) d) =
      finrank F (grading I d) at hprev
  change finrank F (grading CF (d + 1)) +
    finrank F (wholeIdealGrade (grading I) (wholeOriginalSurfaceCoordinateIdeal C p hp) (d + 1)) =
      finrank F (grading I (d + 1)) at hnext
  have hdim (k : ℕ) : finrank F (grading CF k) = finrank K (grading C k) :=
    actualComponentGrade_finrank_eq_coefficientExtension C CF (wholeGenericCurveIdeal_toIdeal C).symm k
  rw [hdim d] at hprev
  rw [hdim (d + 1)] at hnext
  have hgrade := wholeOriginalSurfaceToPlaneCutIdealGrade_finrank_step001 p hp C hpC hprime x0 d
  have hsurface := smoothCubic_genericSurface_coordinateHilbert_step001 p hp hp0 d
  dsimp only [F, I] at hprev hnext
  omega

/-- The SAME actual component's intrinsic degree is unchanged by this
literal coefficient extension. No surrogate degree is introduced. -/
theorem wholeGenericCurve_actualCoordinateDegree_eq_original001
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    actualCurveCoordinateHilbertDegree (wholeGenericCurveIdeal C) = actualCurveCoordinateHilbertDegree C :=
  actualCurveCoordinateHilbertDegree_eq_coefficientExtension C (wholeGenericCurveIdeal C)
    (wholeGenericCurveIdeal_toIdeal C).symm

/-- Original-field coordinate grade injectivity supplies the genuine lower
bound on intrinsic native H0. Finiteness is explicit; no H0-surjectivity,
GI/constants field equality or desired numerical rank bound is assumed. -/
theorem actualComponent_coordinateGrade_finrank_le_originalNativeHZero001
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime) (x0 : scheme C) (d : ℕ)
    [Module.Finite K (SchemeModuleOpenSectionsOver (toBase C)
      (positiveSheafOfModules (grading C) d) ⊤)] :
    finrank K (grading C d) ≤
      finrank K (SchemeModuleOpenSectionsOver (toBase C)
        (positiveSheafOfModules (grading C) d) ⊤) := by
  letI : IsDomain (CoordinateRing C) := (Ideal.Quotient.isDomain_iff_prime C.toIdeal).mpr hprime
  letI : Nonempty (scheme C) := ⟨x0⟩
  exact LinearMap.finrank_le_finrank_of_injective
    (positiveHomogeneousTopSectionLinearMap_injective C d)

/-- The actual original-K coordinate Hilbert step is bounded below by the
ENTIRE canonical plane-cut native H0 deficit. The only supplied capability
is finiteness of that same H0; no Euler/spectrum or target genus premise. -/
theorem wholeOriginalComponent_coordinateHilbert_step_planeNativeHZero001
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hpC : p ∈ C.toIdeal) (hprime : C.toIdeal.IsPrime) (x0 : scheme C) (d : ℕ) :
    let F := GenericHyperplaneField K
    let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
    let i := wholeGenericCutPlaneIdealImmersion C p hp hpC
    let J : (scheme E).Modules := closedImmersionIdealTwist i
      (positiveSheafOfModules (grading E) (d + 1))
    Module.Finite F (SchemeModuleOpenSectionsOver (toBase E) J ⊤) →
      finrank K (grading C d) + 3 * (d + 1) ≤ finrank K (grading C (d + 1)) +
        finrank F (SchemeModuleOpenSectionsOver (toBase E) J ⊤) := by
  let F := GenericHyperplaneField K
  let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
  let i := wholeGenericCutPlaneIdealImmersion C p hp hpC
  let J : (scheme E).Modules := closedImmersionIdealTwist i
    (positiveSheafOfModules (grading E) (d + 1))
  dsimp only
  intro hfinite
  letI : Module.Finite F (SchemeModuleOpenSectionsOver (toBase E) J ⊤) := hfinite
  have hstep := wholeOriginalComponent_coordinateHilbert_step_planeIdealGrade001
    p hp hp0 C hpC hprime x0 d
  have hnative := originalWholePlaneIdealGrade_finrank_le_nativeHZero p hp hp0 C hpC (d + 1)
  omega

private theorem hilbertStep_finitePrefix001
    (H B : ℕ → ℕ) (hstep : ∀ d, H d + 3 * (d + 1) ≤ H (d + 1) + B (d + 1)) :
    ∀ N, 2 * H 0 + 3 * N * (N + 1) ≤
      2 * H N + 2 * ∑ d ∈ Finset.range N, B (d + 1) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hs := hstep N
      nlinarith

/-- Actual finite-prefix Hilbert lower bound, retaining the ENTIRE cut's
actual native H0 function rather than assuming its eventual sharp spectrum.
It is ready for substitution only after the genuine plane-Euler branches
are accepted. The curve dimensions already use the ORIGINAL scalar field. -/
theorem wholeOriginalComponent_coordinateHilbert_finitePrefix_planeNativeHZero001
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hpC : p ∈ C.toIdeal) (hprime : C.toIdeal.IsPrime) (x0 : scheme C) :
    let F := GenericHyperplaneField K
    let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
    let i := wholeGenericCutPlaneIdealImmersion C p hp hpC
    let J : ℕ → (scheme E).Modules := fun d => closedImmersionIdealTwist i
      (positiveSheafOfModules (grading E) d)
    (∀ d : ℕ, 1 ≤ d → Module.Finite F (SchemeModuleOpenSectionsOver (toBase E) (J d) ⊤)) →
      ∀ N : ℕ, 2 * finrank K (grading C 0) + 3 * N * (N + 1) ≤
        2 * finrank K (grading C N) +
          2 * ∑ d ∈ Finset.range N,
            finrank F (SchemeModuleOpenSectionsOver (toBase E) (J (d + 1)) ⊤) := by
  let F := GenericHyperplaneField K
  let E := equationIdeal (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
  let i := wholeGenericCutPlaneIdealImmersion C p hp hpC
  let J : ℕ → (scheme E).Modules := fun d => closedImmersionIdealTwist i
    (positiveSheafOfModules (grading E) d)
  dsimp only
  intro hfinite N
  exact hilbertStep_finitePrefix001 (fun d => finrank K (grading C d))
    (fun d => finrank F (SchemeModuleOpenSectionsOver (toBase E) (J d) ⊤))
    (fun d => wholeOriginalComponent_coordinateHilbert_step_planeNativeHZero001
      p hp hp0 C hpC hprime x0 d (hfinite (d + 1) (by omega))) N

end PfaffianDescent.Coray
