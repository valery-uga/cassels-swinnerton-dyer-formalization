import PfaffianDescent.VoisinHypersurfaceFieldPointDescent
import PfaffianDescent.VoisinQuadraticEvaluationMatrixExtension
import PfaffianDescent.VoisinProjectiveLinearSystem
import PfaffianDescent.VoisinGenericQuadraticDetection
import PfaffianDescent.VoisinSmoothCubicChartDomain
import AllCharacteristics.ProjectiveFiberSmoothness

/-! An algebraically closed coefficient extension supplies a detecting
eight-point configuration on the original cubic's configuration scheme. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A nonzero smooth cubic stays nonzero and prime after any extension of
its coefficient field. This supplies the geometric witness theorem's
primeness hypothesis for an arbitrary smooth ground-field cubic. -/
theorem smoothCubic_coefficientExtension_ne_zero_and_prime
    {K L : Type u} [Field K] [Field L]
    (b : K →+* L)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)] :
    p.map b ≠ 0 ∧
      (Ideal.span ({p.map b} : Set (MvPolynomial (Fin 4) L))).IsPrime := by
  have hpneL : p.map b ≠ 0 := by
    simpa only [map_zero] using
      (MvPolynomial.map_injective b (RingHom.injective b)).ne hpne
  letI : Smooth (hypersurfaceToBase (p.map b) (hp.map b)) :=
    smooth_hypersurfaceToBase_map b p hp
  exact ⟨hpneL,
    principalIdeal_prime_of_irreducible_cubic (p.map b)
      (irreducible_of_smooth_homogeneous_cubic_of_field
        (p.map b) (hp.map b) hpneL)⟩

/-- Injective affine evaluation of the fixed quadratic submodule rules out
a frame combination that vanishes on the whole selected finite set. -/
theorem quadraticEightFrame_coefficients_zero_of_affineVanishing
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L)
    (S : Finset (cubicSurfaceAffinePoints p))
    (hinj : Function.Injective ((finsetEvaluation S).comp
      (cubicSurfacePointEvaluation p (quadraticEightPolynomialSubmodule L))))
    (c : Fin 8 → L)
    (hvan : ∀ y ∈ S,
      MvPolynomial.aeval (fun j => (RingHom.id L) (y.1 j))
        (∑ j, MvPolynomial.C (c j) *
          (quadraticEightFrame L j).1.map (RingHom.id L)) = 0) :
    c = 0 := by
  let W := quadraticEightPolynomialSubmodule L
  let qW : Fin 8 → W := fun i =>
    ⟨quadraticEightPolynomialFrame L i,
      Submodule.subset_span (Set.mem_range_self i)⟩
  have hqW : ∀ i, (qW i : MvPolynomial (Fin 4) L) =
      (quadraticEightFrame L i).1 := by
    intro i
    rfl
  have hqWli : LinearIndependent L qW := by
    apply LinearIndependent.of_comp W.subtype
    change LinearIndependent L (quadraticEightPolynomialFrame L)
    exact quadraticEightPolynomialFrame_linearIndependent L
  letI : FiniteDimensional L W := Module.Finite.of_fg
    (Submodule.fg_span (Set.finite_range (quadraticEightPolynomialFrame L)))
  exact homogeneousFrame_fieldExtension_coefficients_zero_of_large_submodule_evaluation_injective
    (RingHom.id L) p W qW (quadraticEightFrame L) hqW hqWli
    (quadraticEightPolynomialSubmodule_finrank L) S hinj c hvan

/-- Evaluation with identity coefficient change is ordinary evaluation of
the fixed quadratic frame combination. -/
theorem quadraticEightFrame_affineEvaluation_id
    {L : Type u} [Field L]
    (y : Fin 4 → L) (c : Fin 8 → L) :
    MvPolynomial.aeval (fun j => (RingHom.id L) (y j))
      (∑ j, MvPolynomial.C (c j) *
        (quadraticEightFrame L j).1.map (RingHom.id L)) =
      MvPolynomial.eval y
        (homogeneousFrameMap 2 (quadraticEightFrame L) c).1 := by
  have hcomb := quadraticEightFrameCombination_over_extension
    (RingHom.id L) c
  simp only [MvPolynomial.map_id] at hcomb
  simp only [MvPolynomial.map_id, RingHom.id_apply]
  rw [hcomb]
  simp

/-- Injective evaluation of the eight-dimensional quadratic submodule on
eight affine points detects every coefficient vector in the fixed frame. -/
theorem quadraticEightFrame_detected_by_affineEvaluation
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L)
    (S : Finset (cubicSurfaceAffinePoints p))
    (E : Fin 8 ≃ S)
    (hinj : Function.Injective ((finsetEvaluation S).comp
      (cubicSurfacePointEvaluation p (quadraticEightPolynomialSubmodule L)))) :
    ∀ c : Fin 8 → L,
      (∀ i, MvPolynomial.eval (E i).1.1
        (homogeneousFrameMap 2 (quadraticEightFrame L) c).1 = 0) →
      c = 0 := by
  intro c hc
  apply quadraticEightFrame_coefficients_zero_of_affineVanishing p S hinj c
  intro y hy
  obtain ⟨i, hi⟩ := E.surjective ⟨y, hy⟩
  have hpoint : (E i).1 = y := congrArg Subtype.val hi
  rw [quadraticEightFrame_affineEvaluation_id]
  rw [← hpoint]
  exact hc i

/-- A prime cubic over an algebraically closed field has eight ordered
projective points whose affine coordinate vectors detect the fixed
eight-dimensional quadratic frame. -/
theorem exists_cubic_orderedEight_detectingFrame
    {L : Type u} [Field L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0)
    (hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) L))).IsPrime) :
    ∃ (a : Spec (.of L) ⟶
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
      (x : Fin 8 → Fin 4 → L),
      a ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom =
        𝟙 _ ∧
      (∀ c : Fin 8 → L,
        (∀ i, MvPolynomial.eval (x i)
          (homogeneousFrameMap 2 (quadraticEightFrame L) c).1 = 0) →
        c = 0) := by
  let W := quadraticEightPolynomialSubmodule L
  letI : FiniteDimensional L W := Module.Finite.of_fg
    (Submodule.fg_span (Set.finite_range (quadraticEightPolynomialFrame L)))
  obtain ⟨S, ell, hcommon, E, points, aL, hcard, hinj, hdir,
      hpoints, haBase, haCoordinates⟩ :=
    exists_eight_cubicSurfaceHomogeneousSystem_evaluation_injective_orderedConfigurationFieldPoint
      p hp hpne hpprime (d := 2) (by decide) W
      (quadraticEightPolynomialSubmodule_isHomogeneous L)
      (fun z hz hmem => homogeneousQuadratic_separate_cubic_equation p z hp
        (quadraticEightPolynomialSubmodule_isHomogeneous L z hz) hmem)
      (by rw [quadraticEightPolynomialSubmodule_finrank])
  let x : Fin 8 → Fin 4 → L := fun i => (E i).1.1
  refine ⟨aL, x, by simpa using haBase, ?_⟩
  exact quadraticEightFrame_detected_by_affineEvaluation p S E hinj

/-- The geometric detecting configuration on a coefficient extension is
also an extension-field-valued configuration of the original cubic. -/
theorem exists_originalCubic_orderedEight_geometricFrameWitness
    {K L : Type u} [Field K] [Field L] [IsAlgClosed L]
    (b : K →+* L)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p.map b ≠ 0)
    (hpprime : (Ideal.span ({p.map b} : Set (MvPolynomial (Fin 4) L))).IsPrime) :
    ∃ (S : Finset (cubicSurfaceAffinePoints (p.map b)))
      (ell : Fin 4 → L)
      (hcommon : ∀ y ∈ S,
        MvPolynomial.aeval y.1 (homogeneousLinearForm ell) ≠ 0)
      (E : Fin 8 ≃ S)
      (aK : Spec (.of L) ⟶
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left),
      aK ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom =
        Spec.map (CommRingCat.ofHom b) ∧
      (∀ i, (aK ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i).left =
        cubicSurfaceAffinePointLinearNormalizedProjectivePoint
          (p.map b) (hp.map b) ell (E i).1
          (hcommon (E i).1 (E i).2) ≫
        projectiveCoefficientMap b (equationIdeal p hp)
          (equationIdeal (p.map b) (hp.map b)) (equationIdeal_map b p hp)) ∧
      (∀ c : Fin 8 → L,
        (∀ i, MvPolynomial.eval (E i).1.1
          (homogeneousFrameMap 2 (quadraticEightFrame L) c).1 = 0) →
        c = 0) := by
  let W := quadraticEightPolynomialSubmodule L
  letI : FiniteDimensional L W := Module.Finite.of_fg
    (Submodule.fg_span (Set.finite_range (quadraticEightPolynomialFrame L)))
  obtain ⟨S, ell, hcommon, E, points, aL, hcard, hinj, hdir,
      hpoints, haBase, haCoordinates⟩ :=
    exists_eight_cubicSurfaceHomogeneousSystem_evaluation_injective_orderedConfigurationFieldPoint
      (p.map b) (hp.map b) hpne hpprime (d := 2) (by decide) W
      (quadraticEightPolynomialSubmodule_isHomogeneous L)
      (fun z hz hmem => homogeneousQuadratic_separate_cubic_equation (p.map b) z
        (hp.map b) (quadraticEightPolynomialSubmodule_isHomogeneous L z hz) hmem)
      (by rw [quadraticEightPolynomialSubmodule_finrank])
  obtain ⟨aK, haK, hcoords⟩ :=
    exists_orderedCubicConfigurationFieldPoint_of_baseChangedConfiguration
      b p hp aL (by simpa using haBase)
  refine ⟨S, ell, hcommon, E, aK, haK, ?_, ?_⟩
  · intro i
    simpa only [haCoordinates i, hpoints i] using hcoords i
  · exact quadraticEightFrame_detected_by_affineEvaluation
      (p.map b) S E hinj

end PfaffianDescent
