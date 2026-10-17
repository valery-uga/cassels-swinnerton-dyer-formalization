import PfaffianDescent.VoisinSectionRestriction
import PfaffianDescent.VoisinQuadraticKernelSpecialization
import PfaffianDescent.VoisinGenericQuadraticEvaluation
import PfaffianDescent.VoisinGenericQuadraticDetection

/-!
# Quadratic vanishing in a finite algebra and at its eight split components

This is the algebraic bridge from the canonical unordered finite scheme's
coordinate algebra to the eight ordered points over a splitting field.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.UniversalHomogeneous
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

/-- If eight algebra maps jointly detect elements of a coordinate algebra,
polynomial vanishing in that algebra is equivalent to vanishing at all eight
component coordinate vectors. -/
theorem eval₂_zero_iff_eight_components
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [CommRing L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (x : Fin 4 → A) (q : MvPolynomial (Fin 4) K) :
    q.eval₂ (algebraMap K A) x = 0 ↔
      ∀ i : Fin 8,
        q.eval₂ (algebraMap K L) (fun j => φ i (x j)) = 0 := by
  have hnat (i : Fin 8) :
      φ i (q.eval₂ (algebraMap K A) x) =
      q.eval₂ (algebraMap K L) (fun j => φ i (x j)) := by
    change (φ i).toRingHom (q.eval₂ (algebraMap K A) x) = _
    rw [MvPolynomial.eval₂_comp_left]
    congr 1
    · ext k
      exact (φ i).commutes k
  constructor
  · intro h i
    rw [← hnat i, h, map_zero]
  · intro h
    apply hφ
    funext i
    change φ i (q.eval₂ (algebraMap K A) x) = φ i (0 : A)
    rw [hnat i, map_zero]
    exact h i

/-- The homogeneous quadratic restriction kernel in the finite algebra is
detected by the eight ordered splitting components. -/
theorem homogeneousSectionRestriction_mem_ker_iff_eight_components
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [CommRing L] [Algebra K L] [FiniteDimensional K A]
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (x : Fin 4 → A)
    (q : homogeneousSubmodule (Fin 4) K 2) :
    q ∈ LinearMap.ker (homogeneousSectionRestriction (K := K) x 2) ↔
      ∀ i : Fin 8,
        q.1.eval₂ (algebraMap K L) (fun j => φ i (x j)) = 0 := by
  rw [LinearMap.mem_ker]
  change q.1.eval₂ (algebraMap K A) x = 0 ↔ _
  exact eval₂_zero_iff_eight_components φ hφ x q.1

/-- In coefficient coordinates, vanishing in the finite algebra is exactly
membership in the eight-row quadratic evaluation kernel after passage to
the splitting coefficient ring. -/
theorem quadraticCoefficients_vanish_iff_splitMatrixKernel
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [CommRing L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (x : Fin 4 → A)
    (v : Monomials (Fin 4) 2 → K) :
    (quadraticPolynomialOfCoefficients v).eval₂ (algebraMap K A) x = 0 ↔
      (fun m => algebraMap K L (v m)) ∈
        LinearMap.ker (Matrix.toLin'
          (eightPointQuadraticEvaluationMatrix
            (fun i j => φ i (x j)))) := by
  let y : Fin 8 → Fin 4 → L := fun i j => φ i (x j)
  let w : Monomials (Fin 4) 2 → L := fun m => algebraMap K L (v m)
  have hpoint (i : Fin 8) :
      (quadraticPolynomialOfCoefficients v).eval₂
        (algebraMap K L) (y i) =
      (Matrix.toLin' (eightPointQuadraticEvaluationMatrix y) w) i := by
    rw [MvPolynomial.eval₂_eq_eval_map,
      quadraticPolynomialOfCoefficients_map,
      quadraticPolynomialOfCoefficients_eval]
  have hsplit := eval₂_zero_iff_eight_components φ hφ x
    (quadraticPolynomialOfCoefficients v)
  constructor
  · intro hv
    rw [LinearMap.mem_ker]
    funext i
    rw [← hpoint i]
    exact hsplit.mp hv i
  · intro hv
    apply hsplit.mpr
    intro i
    rw [hpoint i]
    exact congrFun (LinearMap.mem_ker.mp hv) i

/-- In a rank-eight coordinate algebra, detection of the fixed eight-quadric
frame by eight component evaluations forces those component maps to be
jointly injective on the entire algebra. -/
theorem eight_component_algHom_joint_injective_of_quadraticFrame_detection
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L] [Algebra K L]
    (x : Fin 4 → A) (hA : Module.finrank K A = 8)
    (φ : Fin 8 → A →ₐ[K] L)
    (hdetect : ∀ c : Fin 8 → K,
      (∀ i, MvPolynomial.eval₂ (algebraMap K L)
        (fun j => φ i (x j))
        (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 = 0) →
      c = 0) :
    Function.Injective (fun t : A => fun i => φ i t) := by
  let g := (homogeneousSectionRestriction (K := K) x 2).comp
    (homogeneousFrameMap 2 (quadraticEightFrame K))
  have hginj : Function.Injective g :=
    quadraticEightFrame_restriction_injective_of_embedding_evaluations
      x φ hdetect
  have hdim : Module.finrank K (Fin 8 → K) = Module.finrank K A := by
    rw [Module.finrank_pi_fintype, Module.finrank_self, hA]
    simp
  have hgsurj : Function.Surjective g :=
    (LinearEquiv.ofInjectiveOfFinrankEq g hginj hdim).surjective
  intro t u htu
  have hz (i : Fin 8) : φ i (t - u) = 0 := by
    have hi := congrFun htu i
    change φ i t = φ i u at hi
    rw [map_sub, hi, sub_self]
  obtain ⟨c, hc⟩ := hgsurj (t - u)
  have hc0 : c = 0 := by
    apply hdetect c
    intro i
    let q := homogeneousFrameMap 2 (quadraticEightFrame K) c
    have heval := MvPolynomial.hom_eval₂ q.1 (algebraMap K A)
      (φ i).toRingHom x
    have hcomp : (φ i).toRingHom.comp (algebraMap K A) =
        algebraMap K L := by
      ext k
      exact (φ i).commutes k
    rw [hcomp] at heval
    calc
      MvPolynomial.eval₂ (algebraMap K L)
          (fun j => φ i (x j)) q.1 =
          φ i (MvPolynomial.eval₂ (algebraMap K A) x q.1) := heval.symm
      _ = φ i (g c) := rfl
      _ = φ i (t - u) := congrArg (φ i) hc
      _ = 0 := hz i
  rw [hc0, map_zero] at hc
  exact sub_eq_zero.mp hc.symm

/-- The rank-eight detection hypothesis used at the unordered generic
configuration identifies its quadratic restriction kernel with the
coefficient-matrix kernel tested on the ordered splitting components. -/
theorem quadraticCoefficients_vanish_iff_splitMatrixKernel_of_detection
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L] [Algebra K L]
    (x : Fin 4 → A) (hA : Module.finrank K A = 8)
    (φ : Fin 8 → A →ₐ[K] L)
    (hdetect : ∀ c : Fin 8 → K,
      (∀ i, MvPolynomial.eval₂ (algebraMap K L)
        (fun j => φ i (x j))
        (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 = 0) →
      c = 0)
    (v : Monomials (Fin 4) 2 → K) :
    (quadraticPolynomialOfCoefficients v).eval₂ (algebraMap K A) x = 0 ↔
      (fun m => algebraMap K L (v m)) ∈
        LinearMap.ker (Matrix.toLin'
          (eightPointQuadraticEvaluationMatrix
            (fun i j => φ i (x j)))) :=
  quadraticCoefficients_vanish_iff_splitMatrixKernel φ
    (eight_component_algHom_joint_injective_of_quadraticFrame_detection
      x hA φ hdetect) x v

/-- The normalized detecting coordinate data already constructed at the
unordered generic configuration supply jointly injective component maps. -/
theorem DetectingQuadraticEightFrameCoordinates.componentJointInjective
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (d : DetectingQuadraticEightFrameCoordinates K A L φ)
    (hA : Module.finrank K A = 8) :
    Function.Injective (fun t : A => fun i => φ i t) :=
  eight_component_algHom_joint_injective_of_quadraticFrame_detection
    d.x hA φ d.detects

/-- For those normalized coordinates, the finite-algebra quadratic kernel
and the split eight-point evaluation kernel have identical membership tests. -/
theorem DetectingQuadraticEightFrameCoordinates.quadraticKernel_iff_splitMatrixKernel
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L] [Algebra K L]
    (φ : Fin 8 → A →ₐ[K] L)
    (d : DetectingQuadraticEightFrameCoordinates K A L φ)
    (hA : Module.finrank K A = 8)
    (v : Monomials (Fin 4) 2 → K) :
    (quadraticPolynomialOfCoefficients v).eval₂
      (algebraMap K A) d.x = 0 ↔
      (fun m => algebraMap K L (v m)) ∈
        LinearMap.ker (Matrix.toLin'
          (eightPointQuadraticEvaluationMatrix
            (fun i j => φ i (d.x j)))) :=
  quadraticCoefficients_vanish_iff_splitMatrixKernel φ
    (d.componentJointInjective φ hA) d.x v

/-- The eight ordered splitting components of the actual unordered generic
finite subscheme jointly detect its entire coordinate algebra. -/
theorem cubicConfigurationGenericEight_componentJointInjective_of_noCommon
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    [Infinite (cubicConfigurationBase cubic hcubic 8).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
      cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (hno : QuadraticEightNoCommonResidueFieldEquationAt cubic hcubic z) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
    let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
      fun i => quadraticOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i
    Function.Injective (fun t : Γ(D.val.subscheme, ⊤) =>
      fun i => φ i t) := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  haveI : Module.Finite Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  let φ : Fin 8 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
    fun i => quadraticOrderedLiftCoefficientChangedComponentAlgHom
      cubic hcubic a ha z hz i
  obtain ⟨d⟩ :=
    exists_cubicConfigurationGenericEight_detectingCoordinates_of_noCommon
      cubic hcubic a ha z hz hno
  have hA : Module.finrank Q.functionField Γ(D.val.subscheme, ⊤) = 8 := by
    apply (finiteSchemeCoefficient_finrank pD).trans
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint Q.functionField)
  exact d.componentJointInjective φ hA

end PfaffianDescent
