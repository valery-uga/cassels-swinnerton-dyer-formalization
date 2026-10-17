import PfaffianDescent.VoisinSmoothOriginalEightEtaleWitness
import PfaffianDescent.VoisinEtaleKernelMemberCriterion
import PfaffianDescent.VoisinEightNormalizedEvaluation

/-!
# A smooth cubic has a geometric degree-eight datum with a proper member

The four-line witness is transported to the original cubic coordinates,
turned into an ordered projective configuration over the algebraic closure,
and identified with the corresponding split finite coordinate algebra.  Its
two transported quadrics are the full quadratic restriction kernel and give
an étale member of the canonical pencil.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_geometric_orderedEight_with_proper_member_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (cubic : Cubic K 4) (hcubic : cubic.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    let L := AlgebraicClosure K
    let p := (cubic.map (algebraMap K L)).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      (cubic.map (algebraMap K L))
    ∃ (y : Fin 8 → Fin 4 → L)
      (hzero : ∀ i, p.eval (y i) = 0)
      (ell : Fin 4 → L)
      (hell : ∀ i, (homogeneousLinearForm ell).eval (y i) ≠ 0)
      (q r : MvPolynomial (Fin 4) L)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
      (A : Spec (.of L) ⟶
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
      (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
      (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8),
      (∀ i, y i ≠ 0) ∧
      Function.Surjective (homogeneousSectionRestriction (K := L)
        (fun j i => y i j : Fin 4 → Fin 8 → L) 2) ∧
      LinearIndependent L
        ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2), ⟨r, hr⟩] ∧
      (∀ i, q.eval (y i) = 0 ∧ r.eval (y i) = 0) ∧
      IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
        p q r hp hq hr)) ∧
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
        p q r hp hq hr)) ∧
      (∀ i, (A ≫ Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i).left =
          projectiveVectorSchemePointInLinearChart
            (equationIdeal p hp) ell (y i)
            (cubicVector_zero_equationIdeal p hp (y i) (hzero i)) (hell i)) ∧
      A ≫ (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).hom = 𝟙 _ ∧
      A ≫ configurationQuotientMap (equationIdeal p hp) 8 = B ∧
      B ≫ cubicConfigurationToBase p hp 8 = 𝟙 _ ∧
      (∃ hB : B ≫ cubicConfigurationToBase p hp 8 = 𝟙 _,
        D = projectiveConfigurationFiniteSubschemeAt
          (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 8 B hB) ∧
      Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      DegreeEightQuadraticRestrictionKernelProperMemberExists p hp D := by
  dsimp only
  let L : Type u := AlgebraicClosure K
  let p : MvPolynomial (Fin 4) L :=
    (cubic.map (algebraMap K L)).toMvPolynomial
  let hp : p.IsHomogeneous 3 :=
    cubic_toMvPolynomial_isHomogeneous_three
      (cubic.map (algebraMap K L))
  obtain ⟨y, q, r, hq, hr, hsurj, hincidence, hy0, hdistinct,
    hq0, hr0, hlin, hfinite, htripleEtale⟩ :=
    exists_original_geometricEight_and_etale_quadratic_pair_of_smooth
      F hF hF0 cubic hcubic
  letI : Infinite L := CharZero.infinite L
  obtain ⟨ell, hell, points, A, B, D, hpoints, hpointsInj, hAbase,
    hAB, hBbase, hD, hDetale, ⟨E, hE⟩, hcoords⟩ :=
    exists_ordered_eight_finite_datum_of_cubic_vectors
      p hp y (fun i => (hincidence i).1) hy0 hdistinct
  have hpointsBase : ∀ i, points i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (RingHom.id L)) := by
    intro i
    rw [hpoints i]
    exact projectiveVectorSchemePointInLinearChart_toBase
      (equationIdeal p hp) ell (y i)
      (cubicVector_zero_equationIdeal p hp (y i) (hincidence i).1)
      (hell i)
  let f := D.val.subschemeι ≫ hypersurfaceToBase p hp
  letI : IsFinite f := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom f
  letI := finiteSchemeCoefficientAlgebra f
  letI : FiniteDimensional L Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite f
  let e := finiteEightDatum_coordinateAlgebra_equiv_pi_of_labeled_points_canonical
    p hp D E points hE hpointsBase hpointsInj
  let x : Fin 4 → Γ(D.val.subscheme, ⊤) := fun j =>
    e.symm (fun i => normalizedVectorInLinearChart ell (y i) j)
  have hkernel := quadrics_span_finite_algebra_eight_evaluation_kernel
    e y ell hell q r hq hr hlin hsurj
      (fun i => ⟨(hincidence i).2.1, (hincidence i).2.2⟩)
  have hlinear := normalized_eight_coordinates_linear_form_eq_one e y ell hell
  have hcubic := normalized_eight_coordinates_cubic_eq_zero
    e y ell hell p hp (fun i => (hincidence i).1)
  have hgen :=
    polynomial_evaluation_surjective_of_homogeneous_restriction_surjective
      x 2 hkernel.1
  let z : CoordinateRing (equationIdeal p hp) :=
    Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm ell)
  have hz : z ∈ grading (equationIdeal p hp) 1 :=
    polynomial_class_mem_grading (equationIdeal p hp)
      (homogeneousLinearForm ell) (homogeneousLinearForm_isHomogeneous ell)
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
      (congrArg (· ≫ hypersurfaceToBase p hp) (hE i)).trans
        (hpointsBase i)
  let psi : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[L] L := fun i =>
    finiteSchemePointAlgHom f (a i) (RingHom.id L) (habase i)
  have hpsiSpec : ∀ i,
      Spec.map (CommRingCat.ofHom (psi i).toRingHom) =
        (Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
          (ULift.up i) ≫ E.hom) ≫ D.val.subscheme.isoSpec.hom := by
    intro i
    exact finiteSchemePointAlgHom_spec f (a i) (RingHom.id L) (habase i)
  have hpsiCoord : ∀ i j,
      psi i (x j) = normalizedVectorInLinearChart ell (y i) j := by
    intro i j
    calc
      psi i (x j) = e (x j) i := by
        exact (finiteEightDatum_coordinateAlgebra_equiv_pi_canonical_apply
          p hp D E points hE hpointsBase hpointsInj (x j) i).symm
      _ = normalizedVectorInLinearChart ell (y i) j := by
        exact congrFun (e.apply_symm_apply _) i
  have heV : ∀ i, ∀ s ∈ (equationIdeal p hp).toIdeal,
      (eval₂Hom (algebraMap L L)
        (normalizedVectorInLinearChart ell (y i))) s = 0 := by
    intro i
    exact normalizedVectorInLinearChart_zero (equationIdeal p hp) ell (y i)
      (cubicVector_zero_equationIdeal p hp (y i) (hincidence i).1)
  have hzOneV : ∀ i, (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap L L)
        (normalizedVectorInLinearChart ell (y i))) (heV i)) z = 1 := by
    intro i
    change (homogeneousLinearForm ell).eval₂ (algebraMap L L)
      (normalizedVectorInLinearChart ell (y i)) = 1
    simpa only [Algebra.algebraMap_self, MvPolynomial.eval₂_id] using
      normalizedVectorInLinearChart_eval_one ell (y i) (hell i)
  have hpointV : ∀ i,
      linearNormalizedPointAt (equationIdeal p hp)
        (normalizedVectorInLinearChart ell (y i)) (heV i) z hz (hzOneV i) =
        Sigma.ι (fun _ : ULift.{u} (Fin 8) ↦ Spec (.of L))
          (ULift.up i) ≫ E.hom ≫ D.val.subschemeι := by
    intro i
    have hleft : linearNormalizedPointAt (equationIdeal p hp)
        (normalizedVectorInLinearChart ell (y i)) (heV i) z hz (hzOneV i) =
        points i := by rw [hpoints i]; rfl
    exact hleft.trans (hE i).symm
  have hmap := linearNormalizedPointAt_eq_of_eight_labeled_coordinates
    (equationIdeal p hp) E D.val.subschemeι x he z hz hzOne psi
    (fun i => normalizedVectorInLinearChart ell (y i))
    heV hzOneV hpsiSpec hpsiCoord hpointV
  let Q : Fin 2 → homogeneousSubmodule (Fin 4) L 2 :=
    ![(⟨q, hq⟩), (⟨r, hr⟩)]
  have hqmem : (⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2) ∈
      LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) := by
    rw [hkernel.2]
    exact Submodule.subset_span ⟨0, rfl⟩
  have hrmem : (⟨r, hr⟩ : homogeneousSubmodule (Fin 4) L 2) ∈
      LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) := by
    rw [hkernel.2]
    exact Submodule.subset_span ⟨1, rfl⟩
  have hqvan : q.eval₂ (algebraMap L Γ(D.val.subscheme, ⊤)) x = 0 :=
    LinearMap.mem_ker.mp hqmem
  have hrvan : r.eval₂ (algebraMap L Γ(D.val.subscheme, ⊤)) x = 0 :=
    LinearMap.mem_ker.mp hrmem
  have hproper :=
    cubicTwoQuadricRestrictionKernelSingularParameterLocus_ne_univ_of_etale_kernel_member
      p q r hp hq hr x hrvan hr0 htripleEtale
  have hmember :
      DegreeEightQuadraticRestrictionKernelProperMemberExists p hp D :=
    ⟨z, hz, x, he, hzOne, hgen, hmap,
      q, hq, hqvan, hq0, hproper⟩
  exact ⟨y, (fun i => (hincidence i).1), ell, hell, q, r, hq, hr,
    A, B, D, hy0, hsurj, hlin,
    (fun i => ⟨(hincidence i).2.1, (hincidence i).2.2⟩), hfinite,
    htripleEtale,
    (fun i => (hcoords i).trans (hpoints i)), (by simpa using hAbase), hAB,
    (by simpa using hBbase),
    hD, hDetale, hmember⟩

/-- Forgetting the ordered presentation leaves the geometric finite étale
degree-eight datum with its proper quadratic member. -/
theorem exists_geometric_degreeEight_datum_with_proper_member_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (cubic : Cubic K 4) (hcubic : cubic.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    let L := AlgebraicClosure K
    let p := (cubic.map (algebraMap K L)).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      (cubic.map (algebraMap K L))
    ∃ D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8,
      Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      DegreeEightQuadraticRestrictionKernelProperMemberExists p hp D := by
  dsimp only
  obtain ⟨y, hzero, ell, hell, q, r, hq, hr, A, B, D, hy0, hsurj,
    hlin, hquad, hfinite, htripleEtale, hcoord, hAbase, hAB,
    hBbase, hD, hEtale, hmember⟩ :=
    exists_geometric_orderedEight_with_proper_member_of_smooth
      F hF hF0 cubic hcubic
  exact ⟨D, hEtale, hmember⟩

end PfaffianDescent
