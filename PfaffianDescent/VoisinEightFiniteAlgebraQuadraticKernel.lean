import PfaffianDescent.VoisinEightNormalizedEvaluation
import PfaffianDescent.VoisinQuadraticEvaluationMatrix

/-!
# An exact quadratic pencil in the generic eight-point coordinate algebra

The ordered generic configuration gives an actual finite étale subscheme.
Its split coordinate algebra admits normalized elements whose quadratic
restriction map is onto and has exactly the explicit two-quadric kernel.
The remaining geometric comparison is to show that these elements are the
pullbacks of the ambient projective coordinates along the subscheme map.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An isomorphism from the labeled disjoint union lets its eight components
detect equality of arbitrary morphisms out of the finite subscheme. -/
theorem morphism_eq_of_eight_labeled_components
    {L : Type u} [Field L] {Z Y : Scheme.{u}}
    (E : (∐ fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L)) ≅ Z)
    (f g : Z ⟶ Y)
    (h : ∀ i : Fin 8,
      Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
        (ULift.up i) ≫ E.hom ≫ f =
      Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
        (ULift.up i) ≫ E.hom ≫ g) : f = g := by
  apply (cancel_epi E.hom).mp
  apply Sigma.hom_ext
  intro i
  exact h i.down

/-- A normalized projective map out of an affine eight-point scheme equals
the original map if its coordinates give the same normalized projective
point on every labeled component. -/
theorem linearNormalizedPointAt_eq_of_eight_labeled_coordinates
    {L : Type u} [Field L] {Z : Scheme.{u}} [IsAffine Z]
    [Algebra L Γ(Z, ⊤)]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (E : (∐ fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L)) ≅ Z)
    (j : Z ⟶ scheme I) (x : Fin 4 → Γ(Z, ⊤))
    (he : ∀ s ∈ I.toIdeal,
      (eval₂Hom (algebraMap L Γ(Z, ⊤)) x) s = 0)
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap L Γ(Z, ⊤)) x) he) z = 1)
    (φ : Fin 8 → Γ(Z, ⊤) →ₐ[L] L)
    (v : Fin 8 → Fin 4 → L)
    (heV : ∀ i, ∀ s ∈ I.toIdeal,
      (eval₂Hom (algebraMap L L) (v i)) s = 0)
    (hzOneV : ∀ i, (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap L L) (v i)) (heV i)) z = 1)
    (hφspec : ∀ i,
      Spec.map (CommRingCat.ofHom (φ i).toRingHom) =
        (Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
          (ULift.up i) ≫ E.hom) ≫ Z.isoSpec.hom)
    (hcoord : ∀ i k, φ i (x k) = v i k)
    (hpoint : ∀ i,
      linearNormalizedPointAt I (v i) (heV i) z hz (hzOneV i) =
        Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
          (ULift.up i) ≫ E.hom ≫ j) :
    linearNormalizedPointAt I x he z hz hzOne = Z.isoSpec.inv ≫ j := by
  have hZ : Z.isoSpec.hom ≫ linearNormalizedPointAt I x he z hz hzOne = j := by
    apply morphism_eq_of_eight_labeled_components E
    intro i
    let a := Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
      (ULift.up i) ≫ E.hom
    have hnat := linearNormalizedPointAt_naturality I x he (φ i)
      (v i) (fun k => (hcoord i k).symm) (heV i) z hz hzOne (hzOneV i)
    calc
      a ≫ (Z.isoSpec.hom ≫ linearNormalizedPointAt I x he z hz hzOne) =
          (a ≫ Z.isoSpec.hom) ≫ linearNormalizedPointAt I x he z hz hzOne := by
            simp only [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (φ i).toRingHom) ≫
          linearNormalizedPointAt I x he z hz hzOne := by rw [hφspec i]
      _ = linearNormalizedPointAt I (v i) (heV i) z hz (hzOneV i) := hnat.symm
      _ = a ≫ j := hpoint i
  apply (cancel_epi Z.isoSpec.hom).mp
  simpa only [Iso.hom_inv_id_assoc] using hZ

/-- Vanishing of the defining cubic in a coordinate algebra is exactly the
condition needed to evaluate the whole homogeneous equation ideal there. -/
theorem cubic_equationIdeal_eval_zero_of_cubic_zero
    {L A : Type u} [Field L] [CommRing A] [Algebra L A]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (x : Fin 4 → A) (hpx : p.eval₂ (algebraMap L A) x = 0) :
    ∀ s ∈ (equationIdeal p hp).toIdeal,
      (eval₂Hom (algebraMap L A) x) s = 0 := by
  intro s hs
  change s ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) L)) at hs
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hs
  simp [hpx]

/-- The exact split-quadrics pencil on the coordinate algebra of a finite
subscheme of a cubic surface. -/
def FiniteEightDatumHasSplitQuadraticKernel
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8) : Prop :=
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  letI := finiteSchemeCoefficientAlgebra
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∃ (c : Fin 4 → L) (x : Fin 4 → Γ(D.val.subscheme, ⊤)),
    (homogeneousLinearForm c).eval₂
      (algebraMap L Γ(D.val.subscheme, ⊤)) x = 1 ∧
    p.eval₂ (algebraMap L Γ(D.val.subscheme, ⊤)) x = 0 ∧
    Function.Surjective
      (eval₂Hom (algebraMap L Γ(D.val.subscheme, ⊤)) x) ∧
    Function.Surjective (homogeneousSectionRestriction (K := L) x 2) ∧
    LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) =
      Submodule.span L (Set.range
        (![⟨(X 1 * X 2 : MvPolynomial (Fin 4) L),
            (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)⟩,
          ⟨(X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L),
            (isHomogeneous_X L 3).mul
              (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
                (isHomogeneous_X L 3))⟩] :
          Fin 2 → homogeneousSubmodule (Fin 4) L 2)) ∧
    let z : CoordinateRing (equationIdeal p hp) :=
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c)
    let hz : z ∈ grading (equationIdeal p hp) 1 :=
      polynomial_class_mem_grading (equationIdeal p hp)
        (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
    ∃ (he : ∀ s ∈ (equationIdeal p hp).toIdeal,
        (eval₂Hom (algebraMap L Γ(D.val.subscheme, ⊤)) x) s = 0)
      (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
        (eval₂Hom (algebraMap L Γ(D.val.subscheme, ⊤)) x) he) z = 1),
      linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
        D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι

theorem exists_generic_eight_finite_datum_with_exact_quadratic_kernel_and_minor
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      ((genericCubicTensor K).map φ)
    Smooth (hypersurfaceToBase p hp) ∧
      ∃ (y : Fin 8 → Fin 4 → L)
        (hzero : ∀ i, p.eval (y i) = 0)
        (c : Fin 4 → L)
        (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0)
        (m : Fin 8 ↪ AllCharacteristics.UniversalHomogeneous.Monomials (Fin 4) 2)
        (A : Spec (.of L) ⟶
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
        (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
        (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8),
        (∀ i, (A ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i).left =
            projectiveVectorSchemePointInLinearChart
              (equationIdeal p hp) c (y i)
              (cubicVector_zero_equationIdeal p hp (y i) (hzero i)) (hc i)) ∧
        A ≫ configurationQuotientMap (equationIdeal p hp) 8 = B ∧
        (∃ hB : B ≫ cubicConfigurationToBase p hp 8 = 𝟙 _,
          D = projectiveConfigurationFiniteSubschemeAt
            (grading (equationIdeal p hp))
            (hypersurfaceToBase p hp) 8 B hB) ∧
        Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
        FiniteEightDatumHasSplitQuadraticKernel p hp D ∧
        Function.Surjective
          (homogeneousSectionRestriction (K := L)
            (fun j i => y i j) 2) ∧
        (∀ i, (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (y i) = 0 ∧
          (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval (y i) = 0) ∧
        IsUnit (eightPointQuadraticEvaluationMinor m y).det := by
  dsimp only
  letI : Infinite L := CharZero.infinite L
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three
    ((genericCubicTensor K).map φ)
  obtain ⟨hsmooth, y, hzero, hsurj, hquadrics, _, c, hc,
    q, A, B, D, hq, hqinj, hA, hAB, hBbase, hD,
    hEt, ⟨E, hE⟩, hcoords⟩ :=
    exists_generic_ordered_eight_configuration_with_quadratic_witness K φ
  have hqbase : ∀ i, q i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (RingHom.id L)) := by
    intro i
    rw [hq i]
    exact projectiveVectorSchemePointInLinearChart_toBase
      (equationIdeal p hp) c (y i)
      (cubicVector_zero_equationIdeal p hp (y i) (hzero i)) (hc i)
  let f := D.val.subschemeι ≫ hypersurfaceToBase p hp
  letI : IsFinite f := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom f
  letI := finiteSchemeCoefficientAlgebra f
  letI : FiniteDimensional L Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite f
  let e := finiteEightDatum_coordinateAlgebra_equiv_pi_of_labeled_points_canonical
    p hp D E q hE hqbase hqinj
  let x : Fin 4 → Γ(D.val.subscheme, ⊤) := fun j =>
    e.symm (fun i => normalizedVectorInLinearChart c (y i) j)
  have h := split_quadrics_span_finite_algebra_eight_evaluation_kernel
    e y c hc hsurj hquadrics
  have hlinear := normalized_eight_coordinates_linear_form_eq_one e y c hc
  have hcubic := normalized_eight_coordinates_cubic_eq_zero
    e y c hc p hp hzero
  have hgen :=
    polynomial_evaluation_surjective_of_homogeneous_restriction_surjective
      x 2 h.1
  let z : CoordinateRing (equationIdeal p hp) :=
    Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c)
  have hz : z ∈ grading (equationIdeal p hp) 1 :=
    polynomial_class_mem_grading (equationIdeal p hp)
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
  have he : ∀ s ∈ (equationIdeal p hp).toIdeal,
      (eval₂Hom (algebraMap L Γ(D.val.subscheme, ⊤)) x) s = 0 :=
    cubic_equationIdeal_eval_zero_of_cubic_zero p hp x hcubic
  have hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap L Γ(D.val.subscheme, ⊤)) x) he) z = 1 := by
    exact hlinear
  let a : Fin 8 → (Spec (.of L) ⟶ D.val.subscheme) := fun i =>
    Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L)) (ULift.up i) ≫ E.hom
  have habase : ∀ i, a i ≫ f =
      Spec.map (CommRingCat.ofHom (RingHom.id L)) := by
    intro i
    dsimp only [a, f]
    simpa only [Category.assoc] using
      (congrArg (· ≫ hypersurfaceToBase p hp) (hE i)).trans (hqbase i)
  let ψ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[L] L := fun i =>
    finiteSchemePointAlgHom f (a i) (RingHom.id L) (habase i)
  have hψspec : ∀ i,
      Spec.map (CommRingCat.ofHom (ψ i).toRingHom) =
        (Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
          (ULift.up i) ≫ E.hom) ≫ D.val.subscheme.isoSpec.hom := by
    intro i
    exact finiteSchemePointAlgHom_spec f (a i) (RingHom.id L) (habase i)
  have hψcoord : ∀ i j, ψ i (x j) = normalizedVectorInLinearChart c (y i) j := by
    intro i j
    calc
      ψ i (x j) = e (x j) i := by
        exact (finiteEightDatum_coordinateAlgebra_equiv_pi_canonical_apply
          p hp D E q hE hqbase hqinj (x j) i).symm
      _ = normalizedVectorInLinearChart c (y i) j := by
        exact congrFun (e.apply_symm_apply _) i
  have heV : ∀ i, ∀ s ∈ (equationIdeal p hp).toIdeal,
      (eval₂Hom (algebraMap L L)
        (normalizedVectorInLinearChart c (y i))) s = 0 := by
    intro i
    exact normalizedVectorInLinearChart_zero (equationIdeal p hp) c (y i)
      (cubicVector_zero_equationIdeal p hp (y i) (hzero i))
  have hzOneV : ∀ i, (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap L L)
        (normalizedVectorInLinearChart c (y i))) (heV i)) z = 1 := by
    intro i
    change (homogeneousLinearForm c).eval₂ (algebraMap L L)
      (normalizedVectorInLinearChart c (y i)) = 1
    simpa only [Algebra.algebraMap_self, MvPolynomial.eval₂_id] using
      normalizedVectorInLinearChart_eval_one c (y i) (hc i)
  have hpointV : ∀ i,
      linearNormalizedPointAt (equationIdeal p hp)
        (normalizedVectorInLinearChart c (y i)) (heV i) z hz (hzOneV i) =
        Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
          (ULift.up i) ≫ E.hom ≫ D.val.subschemeι := by
    intro i
    have hleft : linearNormalizedPointAt (equationIdeal p hp)
        (normalizedVectorInLinearChart c (y i)) (heV i) z hz (hzOneV i) =
        q i := by rw [hq i]; rfl
    exact hleft.trans (hE i).symm
  have hmap := linearNormalizedPointAt_eq_of_eight_labeled_coordinates
    (equationIdeal p hp) E D.val.subschemeι x he z hz hzOne ψ
    (fun i => normalizedVectorInLinearChart c (y i))
    heV hzOneV hψspec hψcoord hpointV
  obtain ⟨m, hm⟩ :=
    exists_unit_eightPointQuadraticEvaluationMinor_of_surjective y
      (eightPointQuadraticEvaluationMatrix_surjective_of_restriction y hsurj)
  have hkernel : FiniteEightDatumHasSplitQuadraticKernel p hp D :=
    ⟨c, x, hlinear, hcubic, hgen, h.1, h.2,
      he, hzOne, hmap⟩
  exact ⟨hsmooth, y, hzero, c, hc, m, A, B, D,
    (fun i => (hcoords i).trans (hq i)), hAB, hD, hEt,
    hkernel, hsurj, hquadrics, hm⟩

/-- Forgetting the marked minor recovers the exact-kernel finite-datum
endpoint used by the later residual argument. -/
theorem exists_generic_eight_finite_datum_with_exact_quadratic_kernel
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      ((genericCubicTensor K).map φ)
    Smooth (hypersurfaceToBase p hp) ∧
      ∃ (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
        (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8),
        (∃ hB : B ≫ cubicConfigurationToBase p hp 8 = 𝟙 _,
          D = projectiveConfigurationFiniteSubschemeAt
            (grading (equationIdeal p hp))
            (hypersurfaceToBase p hp) 8 B hB) ∧
        Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
        FiniteEightDatumHasSplitQuadraticKernel p hp D := by
  dsimp only
  obtain ⟨hsmooth, _, _, _, _, _, _, B, D, _, _, hD, hEt, hkernel, _, _, _⟩ :=
    exists_generic_eight_finite_datum_with_exact_quadratic_kernel_and_minor K φ
  exact ⟨hsmooth, B, D, hD, hEt, hkernel⟩

end PfaffianDescent
