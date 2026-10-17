import PfaffianDescent.VoisinGenericFixedCurveIncidence
import PfaffianDescent.VoisinGenericDegreeEightFixedCurveDichotomy

/-!
# The ground-field descent requirement for a generic fixed curve

A fixed curve over the configuration function field can vary with the eight
points. An incidence estimate for a ground-field quadratic system applies
only after the relevant member has been represented in such a fixed system.
This module records that exact descent input and eliminates the branch in
which the fixed curve contains all eight points.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A nonzero quadratic over the generic configuration field is represented
by a fixed ground-field frame whose finite incidence excludes the generic
eight-point configuration. This is stronger than descent of a Picard class
alone: the frame must represent the actual member as an ambient quadric.
It does not follow from the rank of a varying Grassmannian fibre. -/
def DegreeEightGroundQuadraticFrameWitness
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    (a : CommRingCat.of K ⟶
      CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
    (q' : MvPolynomial (Fin 4)
      (cubicConfigurationBase p hp 8).functionField)
    (hq' : q'.IsHomogeneous 2) (hq'0 : q' ≠ 0) : Prop :=
  ∃ (m n : ℕ) (e : Fin m ≃ Monomials (Fin 4) 2)
    (q : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (hqli : LinearIndependent K q)
    (t : Spec (.of (cubicConfigurationBase p hp 8).functionField) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin n)),
    t ≫ toBase
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) = Spec.map a ∧
      t ≫ homogeneousFrameToParameters 2 e q hqli =
        projectiveClassifyingMap q' hq' hq'0 a.hom ∧
      ¬ GenericEightConfigurationInHomogeneousFrameIncidence
        p hp 2 e q hqli

/-- A fixed ground-field quadratic subspace of dimension at most eight,
together with an exact representation of the generic member in its frame,
supplies the descent witness. The subspace is fixed over `K`; this theorem
does not apply to the quadratic kernel varying over the configuration field. -/
theorem DegreeEightGroundQuadraticFrameWitness.of_groundSubmodule_le_eight
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    (hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [IsSeparated (hypersurfaceToBase p hp)]
    [LocallyOfFiniteType (hypersurfaceToBase p hp)]
    [IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    (a : CommRingCat.of K ⟶
      CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
    (q' : MvPolynomial (Fin 4)
      (cubicConfigurationBase p hp 8).functionField)
    (hq' : q'.IsHomogeneous 2) (hq'0 : q' ≠ 0)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ w ∈ W, w.IsHomogeneous 2)
    (hseparate : ∀ w ∈ W,
      w ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) → w = 0)
    (hdim : Module.finrank K W ≤ 8)
    {m n : ℕ} (e : Fin m ≃ Monomials (Fin 4) 2)
    (qW : Fin n → W)
    (q : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqliW : LinearIndependent K qW) (hqli : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (t : Spec (.of (cubicConfigurationBase p hp 8).functionField) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (htbase : t ≫ toBase
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) = Spec.map a)
    (htframe : t ≫ homogeneousFrameToParameters 2 e q hqli =
      projectiveClassifyingMap q' hq' hq'0 a.hom) :
    DegreeEightGroundQuadraticFrameWitness p hp a q' hq' hq'0 := by
  exact ⟨m, n, e, q, hqli, t, htbase, htframe,
    not_genericEightConfigurationInHomogeneousFrameIncidence_of_finrank_le_eight
      p hp hp0 hpprime (by decide) W hhom hseparate hdim
      qW q hq hqliW hqli hn e⟩

/-- A descended ground-field frame representing one nonzero equation of a
generic fixed curve excludes factorization of the entire generic degree-eight
scheme through that curve. No chosen ordered lift is needed in the premise. -/
theorem fixedCurve_factor_impossible_of_groundQuadraticFrameWitness
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    [Infinite (cubicConfigurationBase p hp 8).functionField]
    (a : CommRingCat.of K ⟶
      CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
      cubicConfigurationToBase p hp 8)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase p hp 8).functionField))
    (hCp : p.map a.hom ∈ C.toIdeal)
    (h : (cubicConfigurationGenericFiniteSubscheme
      p hp 8 a ha).val.subscheme ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic
        (p.map a.hom) (hp.map a.hom) C hCp =
      (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha).val.subschemeι)
    (q' : MvPolynomial (Fin 4)
      (cubicConfigurationBase p hp 8).functionField)
    (hq' : q'.IsHomogeneous 2) (hq'C : q' ∈ C.toIdeal) (hq'0 : q' ≠ 0)
    (hw : DegreeEightGroundQuadraticFrameWitness p hp a q' hq' hq'0) : False := by
  obtain ⟨m, n, e, q, hqli, t, htbase, htframe, havoid⟩ := hw
  let Q := (projectiveConfigurationQuotientOpen
    (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8).toScheme
  let π := projectiveConfigurationQuotientMap
    (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8
  let η := Q.fromSpecStalk (genericPoint Q)
    (IsLocalRing.closedPoint Q.functionField)
  letI : Surjective π :=
    surjective_projectiveConfigurationQuotientMap
      (grading (equationIdeal p hp)) (hypersurfaceToBase p hp) 8
  obtain ⟨z, hz⟩ := π.surjective η
  exact fixedCurve_factor_groundFrame_member_impossible
    p hp a ha z hz C hCp h hfac q' hq' hq'C hq'0
    e q hqli t htbase htframe havoid

/-- In the all-or-none dichotomy, a descended ground-field frame forces the
fixed curve to miss the generic length-eight subscheme. The remaining
disjoint-curve branch is a separate geometric obstruction. -/
theorem DegreeEightFixedCurveDichotomyData.misses_of_groundQuadraticFrameWitness
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    [Infinite (cubicConfigurationBase p hp 8).functionField]
    (a : CommRingCat.of K ⟶
      CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
      cubicConfigurationToBase p hp 8) :
    let F := (cubicConfigurationBase p hp 8).functionField
    let pη := p.map a.hom
    let hpη := hp.map a.hom
    let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
    letI : IsFinite (Dη.val.subschemeι ≫ hypersurfaceToBase pη hpη) :=
      Dη.property.1
    letI := finiteSchemeCoefficientAlgebra
      (Dη.val.subschemeι ≫ hypersurfaceToBase pη hpη)
    ∀ (D : DegreeEightFixedCurveDichotomyData pη hpη Dη),
      DegreeEightGroundQuadraticFrameWitness p hp a D.q
        D.fixedSubscheme.1 D.fixedSubscheme.2.2.1 →
      IsEmpty (pullback
        (homogeneousFixedCurveToCubic pη hpη D.C D.hCp)
        Dη.val.subschemeι : Scheme.{u}) := by
  let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  letI : IsFinite
      (Dη.val.subschemeι ≫ hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    Dη.property.1
  letI := finiteSchemeCoefficientAlgebra
    (Dη.val.subschemeι ≫ hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
  dsimp only
  intro D hw
  rcases D.allOrNone with hmiss | ⟨h, hfac⟩
  · exact hmiss
  · obtain ⟨_, _, _, _, _, _, _, _, _, hspan, _, _, _⟩ := D.fixedSubscheme
    have hqC : D.q ∈ D.C.toIdeal := hspan (Ideal.subset_span (by simp))
    exact False.elim
      (fixedCurve_factor_impossible_of_groundQuadraticFrameWitness
        p hp a ha D.C D.hCp h hfac D.q
        D.fixedSubscheme.1 hqC D.fixedSubscheme.2.2.1 hw)

end PfaffianDescent
