import AllCharacteristics.TwoProofs
import PfaffianDescent.IndependentPerfectDegreeFourPointSection
import PfaffianDescent.QuarticNetKoszul
import PfaffianDescent.HomogeneousIdealPieces
import PfaffianDescent.TripleQuadricsCubicFactor
import PfaffianDescent.VoisinRegularSequenceCriteria
import PfaffianDescent.TripleQuadricsSequentialRegularity
import PfaffianDescent.TripleQuadricsArbitraryFieldLength
import PfaffianDescent.TripleQuadricsFiniteCodimension
import PfaffianDescent.TripleQuadricsFiniteRegularity
import PfaffianDescent.TripleQuadricsGlobalThirdRegularity
import PfaffianDescent.TwoQuadricsNoIrrelevantSocle
import PfaffianDescent.QuarticFiniteNetIndependence
import PfaffianDescent.QuarticFourCycleIndependence
import PfaffianDescent.QuarticAffineLengthEight
import PfaffianDescent.QuarticHomogeneousJets
import PfaffianDescent.PolynomialIdealDescent
import PfaffianDescent.QuarticExceptionalBaseLocus
import PfaffianDescent.QuarticExceptionalTwistedCubicPresentation
import PfaffianDescent.QuarticExceptionalResidual
import PfaffianDescent.QuarticExceptionalProjectiveLength
import PfaffianDescent.QuarticCoordinateChangedJetIdeal
import PfaffianDescent.QuarticExceptionalGroundJetSection
import PfaffianDescent.QuarticExceptionalTangentParam
import PfaffianDescent.QuarticGeometricNetAssembly
import PfaffianDescent.QuarticAffineGroundJetAssembly
import PfaffianDescent.QuarticTwistedCubicSmooth

/-!
# Paper-facing Section 4 statements

This module exposes the checked algebraic heart of Section 4 of
`2-proofs.tex`: a finite net of quadrics whose ideal contains the cubic gives
a rational section, and a degree-four closed point on a smooth cubic gives a
rational section.  The coordinate and tangent calculations supporting the
net are in the `PfaffianDescent.QuarticNet` modules.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
open HomogeneousProjective PfaffianDescent Module

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u

/-- The perfect-field homogeneous-ideal form of `lem:twisted-cubic`.
It is the paper lemma after the embedded curve has been represented by its
homogeneous ideal and geometrically identified with the standard cubic. -/
theorem sectionFour_twisted_cubic_descent_perfect
    {k : Type u} [Field k] [PerfectField k]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    (hgeo : QuarticNet.GeometricallyStandardTwistedCubic I) :
    QuarticNet.GroundTwistedCubicPresentation I ∧
      ∃ e : scheme I ≅ projectiveLineProj k,
        e.hom ≫ projectiveLineProjToBase k = toBase I ∧
          Smooth (toBase I) ∧
            ∃ s : Spec (.of k) ⟶ scheme I, s ≫ toBase I = 𝟙 _ :=
  twoProofs_twisted_cubic_descent_perfect I hgeo

/-- The arbitrary-field homogeneous-ideal form when the geometric
standardization is defined over the separable closure. -/
theorem sectionFour_twisted_cubic_descent_separable
    {k : Type u} [Field k]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    (hgeo : QuarticNet.SeparableGeometricallyStandardTwistedCubic I) :
    QuarticNet.GroundTwistedCubicPresentation I ∧
      ∃ e : scheme I ≅ projectiveLineProj k,
        e.hom ≫ projectiveLineProjToBase k = toBase I ∧
          Smooth (toBase I) ∧
            ∃ s : Spec (.of k) ⟶ scheme I, s ≫ toBase I = 𝟙 _ :=
  twoProofs_twisted_cubic_descent_separable I hgeo

/-- The smooth-embedding form used when the non-finite base locus in the
degree-four argument is a geometrically standard twisted cubic. -/
theorem sectionFour_twisted_cubic_smooth_embedding
    {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i]
    (hsmooth : Smooth (i ≫ ambientToBase))
    (hgeo : QuarticNet.GeometricallyStandardTwistedCubic
      (closedImmersionVanishingIdeal i)) :
    QuarticNet.GroundTwistedCubicPresentation (closedImmersionVanishingIdeal i) ∧
      ∃ r : X ≅ scheme (closedImmersionVanishingIdeal i),
        r.hom ≫ quotientProjMap (closedImmersionVanishingIdeal i) = i ∧
          ∃ e : X ≅ projectiveLineProj k,
            e.hom ≫ projectiveLineProjToBase k = i ≫ ambientToBase ∧
              ∃ s : Spec (.of k) ⟶ X, s ≫ i ≫ ambientToBase = 𝟙 _ :=
  twoProofs_twisted_cubic_smooth_embedding i hsmooth hgeo

/-- The algebraic-closure form of the twisted-cubic descent step in the
non-finite base-locus branch.  Its hypothesis is exactly the standard
coordinate presentation of the canonical ideal after scalar extension. -/
theorem sectionFour_twisted_cubic_smooth_embedding_of_algebraicClosure_presentation
    {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i]
    (hsmooth : Smooth (i ≫ ambientToBase))
    (hbar : IsTwistedCubicAfterCoefficientExtension
      (algebraMap k (AlgebraicClosure k)) i) :
    QuarticNet.GroundTwistedCubicPresentation (closedImmersionVanishingIdeal i) ∧
      ∃ r : X ≅ scheme (closedImmersionVanishingIdeal i),
        r.hom ≫ quotientProjMap (closedImmersionVanishingIdeal i) = i ∧
          ∃ e : X ≅ projectiveLineProj k,
            e.hom ≫ projectiveLineProjToBase k = i ≫ ambientToBase ∧
              ∃ s : Spec (.of k) ⟶ X, s ≫ i ≫ ambientToBase = 𝟙 _ :=
  twoProofs_twisted_cubic_smooth_embedding_of_algebraicClosure_presentation
    i hsmooth hbar

/-- The arbitrary-field counterpart when the canonical ideal has a separable
geometric standardization. -/
theorem sectionFour_twisted_cubic_smooth_embedding_separable
    {k : Type u} [Field k]
    {X : Scheme.{u}}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i]
    (hsmooth : Smooth (i ≫ ambientToBase))
    (hgeo : QuarticNet.SeparableGeometricallyStandardTwistedCubic
      (closedImmersionVanishingIdeal i)) :
    QuarticNet.GroundTwistedCubicPresentation (closedImmersionVanishingIdeal i) ∧
      ∃ r : X ≅ scheme (closedImmersionVanishingIdeal i),
        r.hom ≫ quotientProjMap (closedImmersionVanishingIdeal i) = i ∧
          ∃ e : X ≅ projectiveLineProj k,
            e.hom ≫ projectiveLineProjToBase k = i ≫ ambientToBase ∧
              ∃ s : Spec (.of k) ⟶ X, s ≫ i ≫ ambientToBase = 𝟙 _ :=
  twoProofs_twisted_cubic_smooth_embedding_separable i hsmooth hgeo

/-- The rational-point conclusion of the net-of-quadrics argument. The
scheme-theoretic work in Lemma 5.2 supplies its ideal-membership hypothesis. -/
theorem sectionFour_section_of_cubic_mem_three_quadrics
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hmem : F ∈ Ideal.span ({Q₁, Q₂, Q₃} : Set (MvPolynomial (Fin 4) k))) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ :=
  QuarticNet.cubic_section_of_mem_three_quadrics F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hmem

/-- The explicit conclusion of the algebraic part of `lem:net-of-quadrics`:
cubic membership in a three-quadric ideal supplies three linear coefficients. -/
theorem sectionFour_linear_quadric_decomposition_of_mem_three_quadrics
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hmem : F ∈ Ideal.span ({Q₁, Q₂, Q₃} : Set (MvPolynomial (Fin 4) k))) :
    ∃ H₁ H₂ H₃ : MvPolynomial (Fin 4) k,
      H₁.IsHomogeneous 1 ∧ H₂.IsHomogeneous 1 ∧ H₃.IsHomogeneous 1 ∧
        F = H₁ * Q₁ + H₂ * Q₂ + H₃ * Q₃ := by
  obtain ⟨H₁, H₂, H₃, hH₁, hH₂, hH₃, hdecomp⟩ :=
    QuarticNet.cubic_decomposition_of_mem_three_quadrics
      F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hmem
  refine ⟨H₁, H₂, H₃, hH₁, hH₂, hH₃, ?_⟩
  simpa only [mul_comm] using hdecomp

/-- The dimension assertion in Remark `rem:h^0(I_Z)=3`: when the ideal of
the finite net is generated by three independent quadrics, its quadratic
piece has dimension three. -/
theorem sectionFour_quadratic_piece_dimension_three
    {k : Type u} [Field k]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (hIQ : I.toIdeal = Ideal.span (Set.range Q))
    (hlin : LinearIndependent k Q) :
    Module.finrank k (homogeneousIdealPiece I 2) = 3 :=
  finrank_homogeneousIdealPiece_eq_three_of_ideal_eq_span_quadrics
    I Q hQ hIQ hlin

/-- The dimension assertion in Remark `rem:h^0(I_Z)=3` follows directly
from the ordinary regular-sequence hypothesis of `lem:net-of-quadrics`. -/
theorem sectionFour_quadratic_piece_dimension_three_of_regular_sequence
    {k : Type u} [Field k]
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hseq : RingTheory.Sequence.IsRegular (MvPolynomial (Fin 4) k) [Q₁, Q₂, Q₃]) :
    Module.finrank k (homogeneousIdealPiece
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃) 2) = 3 := by
  apply sectionFour_quadratic_piece_dimension_three
    (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃)
    ![Q₁, Q₂, Q₃]
  · intro i
    fin_cases i <;> assumption
  · rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
      tripleCompleteIntersectionIdeal]
    apply congrArg Ideal.span
    ext q
    simp [or_comm, or_left_comm]
  · exact triple_quadrics_linearIndependent_of_isRegular
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hseq

/-- The finite-base-locus hypothesis in `lem:net-of-quadrics` gives
codimension three on every nonempty dehomogenized chart. -/
theorem sectionFour_dehomogenized_triple_quadric_height_of_finite
    {k : Type u} [Field k] {a b c : ℕ}
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous a) (hQ₂ : Q₂.IsHomogeneous b)
    (hQ₃ : Q₃.IsHomogeneous c)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (j : Fin 4)
    (hproper : tripleCompleteIntersectionDehomogenizedIdeal Q₁ Q₂ Q₃ j ≠ ⊤) :
    (tripleCompleteIntersectionDehomogenizedIdeal Q₁ Q₂ Q₃ j).height = 3 :=
  tripleCompleteIntersection_dehomogenized_height_of_finite
    Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ j hproper

/-- A finite nonempty three-quadric base locus has a standard affine chart
of codimension three.  This removes the auxiliary choice of a chart from the
finite-net hypotheses occurring in `lem:net-of-quadrics`. -/
theorem sectionFour_exists_dehomogenized_triple_quadric_height_of_finite_of_nonempty
    {k : Type u} [Field k] {a b c : ℕ}
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous a) (hQ₂ : Q₂.IsHomogeneous b)
    (hQ₃ : Q₃.IsHomogeneous c)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (hX : Nonempty (scheme
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))) :
    ∃ j : Fin 4,
      (tripleCompleteIntersectionDehomogenizedIdeal Q₁ Q₂ Q₃ j).height = 3 :=
  exists_tripleCompleteIntersection_dehomogenized_height_of_finite_of_nonempty
    Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hX

/-- The finite net has no redundant dehomogenized equation on a nonempty
chart.  This records the minimality portion of `lem:net-of-quadrics` before
the remaining regular-sequence bridge is invoked. -/
theorem sectionFour_dehomogenized_triple_quadric_generators_minimal_of_finite
    {k : Type u} [Field k] {a b c : ℕ}
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous a) (hQ₂ : Q₂.IsHomogeneous b)
    (hQ₃ : Q₃.IsHomogeneous c)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (j : Fin 4)
    (hproper : tripleCompleteIntersectionDehomogenizedIdeal Q₁ Q₂ Q₃ j ≠ ⊤) :
    coordinateOneEvaluation j Q₁ ∉ Ideal.span
      ({coordinateOneEvaluation j Q₂, coordinateOneEvaluation j Q₃} :
        Set (MvPolynomial {i : Fin 4 // i ≠ j} k)) ∧
      coordinateOneEvaluation j Q₂ ∉ Ideal.span
        ({coordinateOneEvaluation j Q₁, coordinateOneEvaluation j Q₃} :
          Set (MvPolynomial {i : Fin 4 // i ≠ j} k)) ∧
      coordinateOneEvaluation j Q₃ ∉ Ideal.span
        ({coordinateOneEvaluation j Q₁, coordinateOneEvaluation j Q₂} :
          Set (MvPolynomial {i : Fin 4 // i ≠ j} k)) :=
  tripleCompleteIntersection_dehomogenized_generators_minimal_of_finite
    Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ j hproper

/-- A finite net of three homogeneous quadrics is linearly independent as
soon as one affine chart of its base locus is nonempty. -/
theorem sectionFour_triple_quadrics_linearIndependent_of_finite
    {k : Type u} [Field k] {a b c : ℕ}
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous a) (hQ₂ : Q₂.IsHomogeneous b)
    (hQ₃ : Q₃.IsHomogeneous c)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (j : Fin 4)
    (hproper : tripleCompleteIntersectionDehomogenizedIdeal Q₁ Q₂ Q₃ j ≠ ⊤) :
    LinearIndependent k ![Q₁, Q₂, Q₃] :=
  tripleCompleteIntersection_linearIndependent_of_finite
    Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ j hproper

/-- A finite nonempty net of three homogeneous quadrics is linearly
independent. -/
theorem sectionFour_triple_quadrics_linearIndependent_of_finite_of_nonempty
    {k : Type u} [Field k] {a b c : ℕ}
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous a) (hQ₂ : Q₂.IsHomogeneous b)
    (hQ₃ : Q₃.IsHomogeneous c)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (hX : Nonempty (scheme
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))) :
    LinearIndependent k ![Q₁, Q₂, Q₃] :=
  tripleCompleteIntersection_linearIndependent_of_finite_of_nonempty
    Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hX

/-- A finite nonempty net of three quadrics has relatively prime first two
quadrics.  This derives the first non-zero-divisor condition in
`lem:net-of-quadrics` directly from the finite-base-locus hypothesis. -/
theorem sectionFour_triple_quadrics_isRelPrime_of_finite_of_nonempty
    {k : Type u} [Field k]
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (hX : Nonempty (scheme
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))) :
    IsRelPrime Q₁ Q₂ :=
  tripleCompleteIntersection_isRelPrime_of_finite_of_nonempty
    Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ (by decide : 0 < 2) hX

/-- The finite-base-locus hypothesis makes every pair in the net relatively
prime.  This supplies the pairwise component of the complete-intersection
argument independently of a choice of ordering. -/
theorem sectionFour_triple_quadrics_pairwise_isRelPrime_of_finite_of_nonempty
    {k : Type u} [Field k]
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (hX : Nonempty (scheme
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))) :
    IsRelPrime Q₁ Q₂ ∧ IsRelPrime Q₁ Q₃ ∧ IsRelPrime Q₂ Q₃ :=
  tripleCompleteIntersection_pairwise_isRelPrime_of_finite_of_nonempty
    Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ (by decide : 0 < 2)
      (by decide : 0 < 2) (by decide : 0 < 2) hX

/-- The second equation in a finite nonempty net is a non-zero-divisor modulo
the first.  This is the first sequential regularity clause of the paper's
complete-intersection argument. -/
theorem sectionFour_triple_quadrics_second_regular_of_finite_of_nonempty
    {k : Type u} [Field k]
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (hX : Nonempty (scheme
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))) :
    ∀ x : MvPolynomial (Fin 4) k,
      Q₂ * x ∈ Ideal.span ({Q₁} : Set (MvPolynomial (Fin 4) k)) →
        x ∈ Ideal.span ({Q₁} : Set (MvPolynomial (Fin 4) k)) :=
  regular_mod_span_singleton_of_isRelPrime
    (sectionFour_triple_quadrics_isRelPrime_of_finite_of_nonempty
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hX)

/-- A finite nonempty net supplies the first two clauses of its sequential
regularity: the first quadric is nonzero and the second is regular modulo it. -/
theorem sectionFour_triple_quadrics_first_two_sequential_of_finite_of_nonempty
    {k : Type u} [Field k]
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (hX : Nonempty (scheme
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))) :
    Q₁ ≠ 0 ∧
      (∀ x : MvPolynomial (Fin 4) k,
        Q₂ * x ∈ Ideal.span ({Q₁} : Set (MvPolynomial (Fin 4) k)) →
          x ∈ Ideal.span ({Q₁} : Set (MvPolynomial (Fin 4) k))) := by
  have hlinear := sectionFour_triple_quadrics_linearIndependent_of_finite_of_nonempty
    Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hX
  refine ⟨fun hzero => by
    apply hlinear.ne_zero 0
    simp [hzero], ?_⟩
  exact sectionFour_triple_quadrics_second_regular_of_finite_of_nonempty
    Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hX

/-- The third quadric in a finite nonempty net is regular modulo the first
two.  This is the saturation step which completes the regular-sequence bridge
in the finite branch of `lem:net-of-quadrics`. -/
theorem sectionFour_triple_quadrics_third_regular_of_finite_of_nonempty
    {k : Type u} [Field k]
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (hX : Nonempty (scheme
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))) :
    ∀ x : MvPolynomial (Fin 4) k,
      Q₃ * x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)) →
        x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)) := by
  intro x hx
  exact third_regular_of_finite Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ (by decide : 0 < 2) hX x hx

/-- A finite nonempty net of three homogeneous quadrics is a regular
sequence.  Thus the geometric finiteness hypothesis supplies all three
non-zero-divisor clauses used in the degree-eight Bézout calculation. -/
theorem sectionFour_triple_quadrics_isRegular_of_finite_of_nonempty
    {k : Type u} [Field k]
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (hX : Nonempty (scheme
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin 4) k) [Q₁, Q₂, Q₃] := by
  obtain ⟨hQ₁0, hQ₂regular⟩ :=
    sectionFour_triple_quadrics_first_two_sequential_of_finite_of_nonempty
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hX
  exact triple_quadrics_isRegular_of_sequential_regular Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃
    hQ₁0 hQ₂regular
    (sectionFour_triple_quadrics_third_regular_of_finite_of_nonempty
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hX)

/-- The pair cut out by the first two quadrics has no component supported only
at the irrelevant locus.  This is the saturation input for lifting chartwise
regularity of the third equation back to the homogeneous coordinate ring. -/
theorem sectionFour_pair_no_irrelevant_annihilator_of_finite_of_nonempty
    {k : Type u} [Field k]
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (hX : Nonempty (scheme
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃)))
    (x : MvPolynomial (Fin 4) k ⧸ Ideal.span
      ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)))
    (hx : ∀ r : Fin 4,
      Ideal.Quotient.mk (Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)))
        (MvPolynomial.X r) * x = 0) :
    x = 0 := by
  obtain ⟨hQ₁0, _⟩ :=
    sectionFour_triple_quadrics_first_two_sequential_of_finite_of_nonempty
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hX
  exact two_quadrics_no_irrelevant_annihilator Q₁ Q₂ hQ₁0
    (sectionFour_triple_quadrics_isRelPrime_of_finite_of_nonempty
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hX) x hx

/-- The degree-two component of a finite nonempty net of quadrics has
dimension three.  This proves the dimension assertion in
Remark `rem:h^0(I_Z)=3` for the net itself, independently of the pending
regular-sequence bridge. -/
theorem sectionFour_triple_quadric_ideal_quadratic_piece_dimension_three_of_finite
    {k : Type u}
    [Field k]
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (j : Fin 4)
    (hproper : tripleCompleteIntersectionDehomogenizedIdeal Q₁ Q₂ Q₃ j ≠ ⊤) :
    Module.finrank k (homogeneousIdealPiece
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃) 2) = 3 := by
  apply sectionFour_quadratic_piece_dimension_three
    (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃)
    ![Q₁, Q₂, Q₃]
  · intro i
    fin_cases i <;> assumption
  · rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
      tripleCompleteIntersectionIdeal]
    apply congrArg Ideal.span
    ext q
    simp [or_comm, or_left_comm]
  · exact sectionFour_triple_quadrics_linearIndependent_of_finite
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ j hproper

/-- For a finite nonempty net of three quadrics, the degree-two part of its
homogeneous ideal has dimension three. -/
theorem sectionFour_triple_quadric_ideal_quadratic_piece_dimension_three_of_finite_of_nonempty
    {k : Type u}
    [Field k]
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (hX : Nonempty (scheme
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))) :
    Module.finrank k (homogeneousIdealPiece
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃) 2) = 3 := by
  apply sectionFour_quadratic_piece_dimension_three
    (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃)
    ![Q₁, Q₂, Q₃]
  · intro i
    fin_cases i <;> assumption
  · rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
      tripleCompleteIntersectionIdeal]
    apply congrArg Ideal.span
    ext q
    simp [or_comm, or_left_comm]
  · exact sectionFour_triple_quadrics_linearIndependent_of_finite_of_nonempty
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hX

/-- The coordinate linear-algebra form of `lem:uij-skew-symmetric`: the
quadric space through four tangent double points has dimension at least three
exactly when its six weighted skew relations have a nonzero solution. -/
theorem sectionFour_tangent_quadric_dimension_iff_weighted_skew
    {k : Type u} [Field k] (u : Fin 4 → Fin 4 → k) :
    3 ≤ Module.finrank k (LinearMap.ker (QuarticNet.tangentQuadricEvaluationLinearMap u)) ↔
      ∃ w : Fin 4 → k, w ≠ 0 ∧
        (w 0 * u 0 1 + w 1 * u 1 0 = 0) ∧
        (w 0 * u 0 2 + w 2 * u 2 0 = 0) ∧
        (w 0 * u 0 3 + w 3 * u 3 0 = 0) ∧
        (w 1 * u 1 2 + w 2 * u 2 1 = 0) ∧
        (w 1 * u 1 3 + w 3 * u 3 1 = 0) ∧
        (w 2 * u 2 3 + w 3 * u 3 2 = 0) :=
  QuarticNet.three_le_finrank_ker_tangentQuadricEvaluation_iff u

/-- The rescaling conclusion in `lem:uij=-uji`: if every coordinate occurs
nontrivially in a weighted relation, the tangent-direction matrix can be
rescaled to a skew-symmetric one. -/
theorem sectionFour_rescale_tangent_directions_skew
    {k : Type u} [Field k] [Infinite k]
    (u : Fin 4 → Fin 4 → k) (hdiag : ∀ i, u i i = 0)
    (hcoordinate : ∀ i : Fin 4,
      ∃ w ∈ LinearMap.ker (QuarticNet.weightedRelationLinearMap u), w i ≠ 0) :
    ∃ w : Fin 4 → k, (∀ i : Fin 4, w i ≠ 0) ∧
      ∀ i j, QuarticNet.rescaleTangentDirections w u i j =
        -QuarticNet.rescaleTangentDirections w u j i :=
  QuarticNet.exists_rescaling_skew_of_weighted_relation_coordinates u hdiag hcoordinate

/-- The projective rank form of the scheme-theoretic equality step in the
net-of-quadrics lemma.  It isolates the geometric degree-eight comparison
from the regular-sequence calculation that can establish that comparison. -/
theorem sectionFour_triple_quadrics_factor_through_cubic_of_finite_rank_eight
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (hW : finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃)) = 8)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁) :
    ∃ q : scheme (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃) ⟶
        hypersurface F hF,
      IsClosedImmersion q ∧
        q ≫ hypersurfaceToAmbient F hF =
          tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ ≫
            hypersurfaceToAmbient Q₁ hQ₁ :=
  triple_quadrics_factor_through_cubic_of_finite_rank_eight
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hW i hker hZ j hcompat

/-- The projective rank form of ambient cubic ideal-sheaf containment. It
uses only the finite rank-eight comparison, leaving any regular-sequence
argument to establish that comparison outside this conclusion. -/
theorem sectionFour_triple_quadrics_cubic_ker_le_of_finite_rank_eight
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (hW : finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃)) = 8)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁) :
    (hypersurfaceToAmbient F hF).ker ≤
      (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ ≫
        hypersurfaceToAmbient Q₁ hQ₁).ker :=
  triple_quadrics_cubic_ker_le_of_finite_rank_eight
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hW i hker hZ j hcompat

/-- The direct homogeneous saturation form of the finite-net argument.
Ambient cubic ideal-sheaf containment and the intrinsic absence of irrelevant
coordinate torsion imply literal cubic membership over every field. -/
theorem sectionFour_cubic_mem_of_ker_le_and_no_irrelevant_annihilator
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hker : (hypersurfaceToAmbient F hF).ker ≤
      (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ ≫
        hypersurfaceToAmbient Q₁ hQ₁).ker)
    (hsocle : ∀ x : CoordinateRing
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃),
      (∀ r : Fin 4,
        coordinate (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃) r * x = 0) →
        x = 0) :
    F ∈ (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).toIdeal :=
  triple_quadrics_mem_of_cubic_ker_le_and_no_irrelevant_annihilator
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hker hsocle

/-- The rational-section consequence of the direct homogeneous saturation
criterion for a net of three quadrics. -/
theorem sectionFour_section_of_cubic_of_ker_le_and_no_irrelevant_annihilator
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hker : (hypersurfaceToAmbient F hF).ker ≤
      (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ ≫
        hypersurfaceToAmbient Q₁ hQ₁).ker)
    (hsocle : ∀ x : CoordinateRing
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃),
      (∀ r : Fin 4,
        coordinate (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃) r * x = 0) →
        x = 0) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  apply sectionFour_section_of_cubic_mem_three_quadrics F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃
  change F ∈ tripleCompleteIntersectionIdeal Q₁ Q₂ Q₃
  rw [← tripleCompleteIntersectionHomogeneousIdeal_toIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃]
  exact sectionFour_cubic_mem_of_ker_le_and_no_irrelevant_annihilator
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hker hsocle

/-- The finite-net cubic decomposition over an arbitrary field. A finite
rank-eight three-quadric intersection containing the rank-eight cubic
subscheme yields the decomposition once its quotient has no irrelevant
coordinate socle. -/
theorem sectionFour_linear_quadric_decomposition_of_finite_rank_eight_and_no_irrelevant_annihilator
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (hW : finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃)) = 8)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁)
    (hsocle : ∀ x : CoordinateRing
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃),
      (∀ r : Fin 4,
        coordinate (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃) r * x = 0) →
        x = 0) :
    ∃ H₁ H₂ H₃ : MvPolynomial (Fin 4) k,
      H₁.IsHomogeneous 1 ∧ H₂.IsHomogeneous 1 ∧ H₃.IsHomogeneous 1 ∧
        F = H₁ * Q₁ + H₂ * Q₂ + H₃ * Q₃ := by
  apply sectionFour_linear_quadric_decomposition_of_mem_three_quadrics
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃
  change F ∈ tripleCompleteIntersectionIdeal Q₁ Q₂ Q₃
  rw [← tripleCompleteIntersectionHomogeneousIdeal_toIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃]
  apply sectionFour_cubic_mem_of_ker_le_and_no_irrelevant_annihilator
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃
  · exact sectionFour_triple_quadrics_cubic_ker_le_of_finite_rank_eight
      F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hW i hker hZ j hcompat
  · exact hsocle

/-- The rational-section conclusion of the arbitrary-field finite-net cubic
decomposition. -/
theorem sectionFour_section_of_cubic_of_finite_rank_eight_and_no_irrelevant_annihilator
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    (hW : finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃)) = 8)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁)
    (hsocle : ∀ x : CoordinateRing
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃),
      (∀ r : Fin 4,
        coordinate (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃) r * x = 0) →
        x = 0) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  apply sectionFour_section_of_cubic_mem_three_quadrics F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃
  change F ∈ tripleCompleteIntersectionIdeal Q₁ Q₂ Q₃
  rw [← tripleCompleteIntersectionHomogeneousIdeal_toIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃]
  apply sectionFour_cubic_mem_of_ker_le_and_no_irrelevant_annihilator
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃
  · exact sectionFour_triple_quadrics_cubic_ker_le_of_finite_rank_eight
      F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hW i hker hZ j hcompat
  · exact hsocle

/-- The scheme-theoretic equality step in `lem:net-of-quadrics`: a regular
three-quadric intersection with the same degree-eight closed subscheme as a
cubic factors through that cubic. -/
theorem sectionFour_triple_quadrics_factor_through_cubic_of_rank_eight
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hQ₁0 : Q₁ ≠ 0) (hQ₂0 : Q₂ ≠ 0)
    (hrel : IsRelPrime Q₁ Q₂)
    (hregular : ∀ x : MvPolynomial (Fin 4) k,
      Q₃ * x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)) →
        x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁) :
    ∃ q : scheme (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃) ⟶
        hypersurface F hF,
      IsClosedImmersion q ∧
        q ≫ hypersurfaceToAmbient F hF =
          tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ ≫
            hypersurfaceToAmbient Q₁ hQ₁ :=
  triple_quadrics_factor_through_cubic_of_rank_eight
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hQ₁0 hQ₂0 hrel hregular i hker hZ j hcompat


/-- The rational-point conclusion of the finite-net branch from the
chart-local form of cubic containment.  Associated-prime avoidance selects a
single regular degree-one chart, and localized cubic vanishing there gives
the three-quadric ideal membership needed by the Koszul argument. -/
theorem sectionFour_section_of_cubic_of_degreeOne_localization_zero
    {k : Type u} [Field k] [Infinite k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (havoid : ∀ P ∈ associatedPrimes
      (MvPolynomial (Fin 4) k ⧸ tripleCompleteIntersectionIdeal Q₁ Q₂ Q₃)
      (MvPolynomial (Fin 4) k ⧸ tripleCompleteIntersectionIdeal Q₁ Q₂ Q₃),
      ∃ z ∈ MvPolynomial.homogeneousSubmodule (Fin 4) k 1,
        Ideal.Quotient.mk (tripleCompleteIntersectionIdeal Q₁ Q₂ Q₃) z ∉ P)
    (hzero : ∀ z ∈ MvPolynomial.homogeneousSubmodule (Fin 4) k 1,
      algebraMap (MvPolynomial (Fin 4) k ⧸ tripleCompleteIntersectionIdeal Q₁ Q₂ Q₃)
        (Localization (Submonoid.powers
          (Ideal.Quotient.mk (tripleCompleteIntersectionIdeal Q₁ Q₂ Q₃) z)))
        (Ideal.Quotient.mk (tripleCompleteIntersectionIdeal Q₁ Q₂ Q₃) F) = 0) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  apply sectionFour_section_of_cubic_mem_three_quadrics F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃
  exact triple_quadrics_mem_of_degreeOne_localization_zero F Q₁ Q₂ Q₃ havoid hzero

/-- The finite-net branch gives a rational point once its degree-eight
complete intersection is regular and its projective degree-one system avoids
the associated primes.  The cubic membership is obtained here directly from
the projective rank-eight containment, rather than being supplied as an
external ideal-membership assumption. -/
theorem sectionFour_section_of_cubic_of_rank_eight_and_avoids_associatedPrimes
    {k : Type u} [Field k] [Infinite k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hQ₁0 : Q₁ ≠ 0) (hQ₂0 : Q₂ ≠ 0)
    (hrel : IsRelPrime Q₁ Q₂)
    (hregular : ∀ x : MvPolynomial (Fin 4) k,
      Q₃ * x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)) →
        x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁)
    (havoid : ∀ P ∈ associatedPrimes
      (MvPolynomial (Fin 4) k ⧸
        (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).toIdeal)
      (MvPolynomial (Fin 4) k ⧸
        (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).toIdeal),
      ∃ z ∈ MvPolynomial.homogeneousSubmodule (Fin 4) k 1,
        Ideal.Quotient.mk
          (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).toIdeal z ∉ P) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  apply sectionFour_section_of_cubic_mem_three_quadrics F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃
  change F ∈ tripleCompleteIntersectionIdeal Q₁ Q₂ Q₃
  rw [← tripleCompleteIntersectionHomogeneousIdeal_toIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃]
  exact triple_quadrics_mem_of_rank_eight_and_avoids_associatedPrimes
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hQ₁0 hQ₂0 hrel hregular
      i hker hZ j hcompat havoid

/-- The preceding finite-net conclusion with the associated-prime premise
expressed projectively: every associated component of the complete
intersection meets one of the four standard affine charts. -/
theorem sectionFour_section_of_cubic_of_rank_eight_and_coordinate_avoidance
    {k : Type u} [Field k] [Infinite k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hQ₁0 : Q₁ ≠ 0) (hQ₂0 : Q₂ ≠ 0)
    (hrel : IsRelPrime Q₁ Q₂)
    (hregular : ∀ x : MvPolynomial (Fin 4) k,
      Q₃ * x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)) →
        x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁)
    (hcoordinate : ∀ P ∈ associatedPrimes
      (CoordinateRing (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))
      (CoordinateRing (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃)),
      ∃ r : Fin 4,
        coordinate (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃) r ∉ P) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  apply sectionFour_section_of_cubic_mem_three_quadrics F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃
  change F ∈ tripleCompleteIntersectionIdeal Q₁ Q₂ Q₃
  rw [← tripleCompleteIntersectionHomogeneousIdeal_toIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃]
  exact triple_quadrics_mem_of_rank_eight_and_coordinate_avoidance
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hQ₁0 hQ₂0 hrel hregular
      i hker hZ j hcompat hcoordinate

/-- The finite-net branch of `lem:net-of-quadrics` under its intrinsic
saturation condition: a regular three-quadric quotient with no irrelevant
coordinate socle forces the cubic surface to have a rational point. -/
theorem sectionFour_section_of_cubic_of_rank_eight_and_no_irrelevant_annihilator
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hQ₁0 : Q₁ ≠ 0) (hQ₂0 : Q₂ ≠ 0)
    (hrel : IsRelPrime Q₁ Q₂)
    (hregular : ∀ x : MvPolynomial (Fin 4) k,
      Q₃ * x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)) →
        x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁)
    (hsocle : ∀ x : CoordinateRing
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃),
      (∀ r : Fin 4,
        coordinate (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃) r * x = 0) →
        x = 0) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  apply sectionFour_section_of_cubic_mem_three_quadrics F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃
  change F ∈ tripleCompleteIntersectionIdeal Q₁ Q₂ Q₃
  rw [← tripleCompleteIntersectionHomogeneousIdeal_toIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃]
  exact triple_quadrics_mem_of_rank_eight_and_no_irrelevant_annihilator
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hQ₁0 hQ₂0 hrel hregular
      i hker hZ j hcompat hsocle

/-- The literal linear decomposition in the finite-net branch of
`lem:net-of-quadrics`.  A regular degree-eight three-quadric intersection
contained in the cubic puts its equation in the three-quadric ideal. -/
theorem sectionFour_linear_quadric_decomposition_of_rank_eight
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hQ₁0 : Q₁ ≠ 0) (hQ₂0 : Q₂ ≠ 0)
    (hrel : IsRelPrime Q₁ Q₂)
    (hregular : ∀ x : MvPolynomial (Fin 4) k,
      Q₃ * x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)) →
        x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁) :
    ∃ H₁ H₂ H₃ : MvPolynomial (Fin 4) k,
      H₁.IsHomogeneous 1 ∧ H₂.IsHomogeneous 1 ∧ H₃.IsHomogeneous 1 ∧
        F = H₁ * Q₁ + H₂ * Q₂ + H₃ * Q₃ := by
  apply sectionFour_linear_quadric_decomposition_of_mem_three_quadrics
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃
  change F ∈ tripleCompleteIntersectionIdeal Q₁ Q₂ Q₃
  rw [← tripleCompleteIntersectionHomogeneousIdeal_toIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃]
  exact triple_quadrics_mem_of_rank_eight
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hQ₁0 hQ₂0 hrel hregular
      i hker hZ j hcompat

/-- The Bézout part of `lem:net-of-quadrics` in its standard
regular-sequence form: three homogeneous quadrics forming a regular sequence
cut out an actual finite projective scheme. -/
theorem sectionFour_triple_quadrics_intersection_finite_of_regular_sequence
    {k : Type u} [Field k]
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hseq : RingTheory.Sequence.IsRegular (MvPolynomial (Fin 4) k) [Q₁, Q₂, Q₃]) :
    IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃)) := by
  obtain ⟨hQ₁0, hQ₂regular, hQ₃regular⟩ :=
    (triple_quadrics_isRegular_iff_sequential_regular
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).mp hseq
  exact triple_quadrics_intersection_finite_of_sequential_regular
    Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hQ₁0 hQ₂regular hQ₃regular

/-- The rank-eight Bézout conclusion of `lem:net-of-quadrics` under its
ordinary regular-sequence hypothesis. -/
theorem sectionFour_triple_quadrics_intersection_rank_eight_of_regular_sequence
    {k : Type u} [Field k]
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hseq : RingTheory.Sequence.IsRegular (MvPolynomial (Fin 4) k) [Q₁, Q₂, Q₃]) :
    letI := sectionFour_triple_quadrics_intersection_finite_of_regular_sequence
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hseq
    finiteSchemeRank (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃)) = 8 := by
  letI := sectionFour_triple_quadrics_intersection_finite_of_regular_sequence
    Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hseq
  exact triple_quadrics_intersection_length_eight_of_regular_sequence
    Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hseq

/-- The literal finite-net conclusion in the sequential regularity form
used in the manuscript: the second quadric is regular modulo the first, and
the third modulo the first two. -/
theorem sectionFour_linear_quadric_decomposition_of_sequential_regular
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2) (hQ₁0 : Q₁ ≠ 0)
    (hQ₂regular : ∀ x : MvPolynomial (Fin 4) k,
      Q₂ * x ∈ Ideal.span ({Q₁} : Set (MvPolynomial (Fin 4) k)) →
        x ∈ Ideal.span ({Q₁} : Set (MvPolynomial (Fin 4) k)))
    (hQ₃regular : ∀ x : MvPolynomial (Fin 4) k,
      Q₃ * x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)) →
        x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁) :
    ∃ H₁ H₂ H₃ : MvPolynomial (Fin 4) k,
      H₁.IsHomogeneous 1 ∧ H₂.IsHomogeneous 1 ∧ H₃.IsHomogeneous 1 ∧
        F = H₁ * Q₁ + H₂ * Q₂ + H₃ * Q₃ :=
  sectionFour_linear_quadric_decomposition_of_rank_eight
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hQ₁0
    (right_ne_zero_of_regular_mod_span_singleton
      (homogeneous_not_isUnit_of_pos_degree hQ₁ (by omega)) hQ₂regular)
    (isRelPrime_of_regular_mod_span_singleton hQ₁0 hQ₂regular)
    hQ₃regular i hker hZ j hcompat

/-- The finite-net decomposition in the standard regular-sequence form
stated in the manuscript. -/
theorem sectionFour_linear_quadric_decomposition_of_regular_sequence
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hseq : RingTheory.Sequence.IsRegular (MvPolynomial (Fin 4) k) [Q₁, Q₂, Q₃])
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁) :
    ∃ H₁ H₂ H₃ : MvPolynomial (Fin 4) k,
      H₁.IsHomogeneous 1 ∧ H₂.IsHomogeneous 1 ∧ H₃.IsHomogeneous 1 ∧
        F = H₁ * Q₁ + H₂ * Q₂ + H₃ * Q₃ := by
  letI := sectionFour_triple_quadrics_intersection_finite_of_regular_sequence
    Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hseq
  refine sectionFour_linear_quadric_decomposition_of_finite_rank_eight_and_no_irrelevant_annihilator
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ ?_ i hker hZ j hcompat ?_
  · exact sectionFour_triple_quadrics_intersection_rank_eight_of_regular_sequence
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hseq
  · obtain ⟨hQ₁0, hQ₂regular, hQ₃regular⟩ :=
      (triple_quadrics_isRegular_iff_sequential_regular
        Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).mp hseq
    exact triple_quadrics_no_irrelevant_annihilator
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hQ₁0
      (right_ne_zero_of_regular_mod_span_singleton
        (homogeneous_not_isUnit_of_pos_degree hQ₁ (by omega)) hQ₂regular)
      (isRelPrime_of_regular_mod_span_singleton hQ₁0 hQ₂regular)
      hQ₃regular

/-- The finite-net branch of `lem:net-of-quadrics`: every regular
three-quadric degree-eight intersection contained projectively in the cubic
has cubic equation in its homogeneous ideal, hence yields a rational point. -/
theorem sectionFour_section_of_cubic_of_rank_eight
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hQ₁0 : Q₁ ≠ 0) (hQ₂0 : Q₂ ≠ 0)
    (hrel : IsRelPrime Q₁ Q₂)
    (hregular : ∀ x : MvPolynomial (Fin 4) k,
      Q₃ * x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)) →
        x ∈ Ideal.span ({Q₁, Q₂} : Set (MvPolynomial (Fin 4) k)))
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  apply sectionFour_section_of_cubic_mem_three_quadrics F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃
  change F ∈ tripleCompleteIntersectionIdeal Q₁ Q₂ Q₃
  rw [← tripleCompleteIntersectionHomogeneousIdeal_toIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃]
  exact triple_quadrics_mem_of_rank_eight
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hQ₁0 hQ₂0 hrel hregular
      i hker hZ j hcompat

/-- The rational-section conclusion of the finite-net branch under the
ordinary regular-sequence hypothesis stated in `lem:net-of-quadrics`. -/
theorem sectionFour_section_of_cubic_of_regular_sequence
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hseq : RingTheory.Sequence.IsRegular (MvPolynomial (Fin 4) k) [Q₁, Q₂, Q₃])
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  letI := sectionFour_triple_quadrics_intersection_finite_of_regular_sequence
    Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hseq
  refine sectionFour_section_of_cubic_of_finite_rank_eight_and_no_irrelevant_annihilator
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ ?_ i hker hZ j hcompat ?_
  · exact sectionFour_triple_quadrics_intersection_rank_eight_of_regular_sequence
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hseq
  · obtain ⟨hQ₁0, hQ₂regular, hQ₃regular⟩ :=
      (triple_quadrics_isRegular_iff_sequential_regular
        Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).mp hseq
    exact triple_quadrics_no_irrelevant_annihilator
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ hQ₁0
      (right_ne_zero_of_regular_mod_span_singleton
        (homogeneous_not_isUnit_of_pos_degree hQ₁ (by omega)) hQ₂regular)
      (isRelPrime_of_regular_mod_span_singleton hQ₁0 hQ₂regular)
      hQ₃regular


/-- A length-eight subscheme contained in a finite three-quadric intersection
makes that intersection nonempty.  This removes the auxiliary nonemptiness
assumption from the paper-facing finite-net criterion. -/
theorem sectionFour_triple_quadrics_nonempty_of_containing_rank_eight
    {k : Type u} [Field k]
    (Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8) :
    Nonempty (scheme
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃)) := by
  obtain ⟨z, hz⟩ := AllCharacteristics.exists_effectiveZeroCycle_degree_finiteSchemeRank
    (i ≫ hypersurfaceToBase Q₁ hQ₁)
  obtain ⟨x, _, _⟩ := EffectiveZeroCycle.exists_coprime_degree
    (i ≫ hypersurfaceToBase Q₁ hQ₁) z (by
      rw [hz, hZ]
      norm_num)
  exact Nonempty.map
    (tripleCompleteIntersectionLift Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ i hker) ⟨x.1⟩

/-- The decomposition in `lem:net-of-quadrics`, with regularity derived from
the finite nonempty base locus.  The closed immersion and rank hypothesis
express that the three-quadric intersection contains the specified
length-eight subscheme of the cubic. -/
theorem sectionFour_linear_quadric_decomposition_of_finite_nonempty_net
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁) :
    ∃ H₁ H₂ H₃ : MvPolynomial (Fin 4) k,
      H₁.IsHomogeneous 1 ∧ H₂.IsHomogeneous 1 ∧ H₃.IsHomogeneous 1 ∧
        F = H₁ * Q₁ + H₂ * Q₂ + H₃ * Q₃ :=
  sectionFour_linear_quadric_decomposition_of_regular_sequence
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃
    (sectionFour_triple_quadrics_isRegular_of_finite_of_nonempty
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃
      (sectionFour_triple_quadrics_nonempty_of_containing_rank_eight
        Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ i hker hZ))
    i hker hZ j hcompat

/-- The rational-section form of `lem:net-of-quadrics`, with its
finite-base-locus hypothesis used directly instead of assumed regularity. -/
theorem sectionFour_section_of_cubic_of_finite_nonempty_net
    {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ :=
  sectionFour_section_of_cubic_of_regular_sequence
    F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃
    (sectionFour_triple_quadrics_isRegular_of_finite_of_nonempty
      Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃
      (sectionFour_triple_quadrics_nonempty_of_containing_rank_eight
        Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃ i hker hZ))
    i hker hZ j hcompat


/-- The finite-net conclusion descends through an extension field and an
invertible linear coordinate change.  This is the bridge from a geometric
calculation with conjugate tangent points to the ground-field criterion. -/
theorem sectionFour_section_of_coordinate_changed_extension_ideal
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    (hmem : PfaffianDescent.linearSubstitution M (MvPolynomial.map (algebraMap k K) F) ∈
      Ideal.span ({PfaffianDescent.linearSubstitution M
        (MvPolynomial.map (algebraMap k K) Q₁),
        PfaffianDescent.linearSubstitution M
        (MvPolynomial.map (algebraMap k K) Q₂),
        PfaffianDescent.linearSubstitution M
        (MvPolynomial.map (algebraMap k K) Q₃)} : Set (MvPolynomial (Fin 4) K))) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  let Q : Fin 3 → MvPolynomial (Fin 4) k := ![Q₁, Q₂, Q₃]
  have hset : Set.range (fun i => PfaffianDescent.linearSubstitution M
      (MvPolynomial.map (algebraMap k K) (Q i))) =
      {PfaffianDescent.linearSubstitution M (MvPolynomial.map (algebraMap k K) Q₁),
        PfaffianDescent.linearSubstitution M (MvPolynomial.map (algebraMap k K) Q₂),
        PfaffianDescent.linearSubstitution M (MvPolynomial.map (algebraMap k K) Q₃)} := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [Q]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h | h)
      · exact ⟨0, by simpa [Q] using h.symm⟩
      · exact ⟨1, by simpa [Q] using h.symm⟩
      · exact ⟨2, by simpa [Q] using h.symm⟩
  have hground : F ∈ Ideal.span (Set.range Q) := by
    apply PfaffianDescent.polynomial_mem_span_of_linearSubstitution_map_range_descends
      M hM Q F
    rwa [hset]
  have hground' : F ∈ Ideal.span ({Q₁, Q₂, Q₃} : Set (MvPolynomial (Fin 4) k)) := by
    have hQset : Set.range Q = {Q₁, Q₂, Q₃} := by
      ext q
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp [Q]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rintro (h | h | h)
        · exact ⟨0, by simpa [Q] using h.symm⟩
        · exact ⟨1, by simpa [Q] using h.symm⟩
        · exact ⟨2, by simpa [Q] using h.symm⟩
    rwa [hQset] at hground
  exact sectionFour_section_of_cubic_mem_three_quadrics F Q₁ Q₂ Q₃ hF hQ₁ hQ₂ hQ₃ hground'

/-- A coordinate-changed parametrized base curve which is contained in the
cubic gives a ground-field section as soon as its ideal is generated by three
ground quadrics.  This is the contained-curve alternative in the exceptional
branch of the tangent-net proof. -/
theorem sectionFour_section_of_coordinate_changed_param_ideal
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (P : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 2) K)
    (hideal : Ideal.span (Set.range (fun i =>
      PfaffianDescent.linearSubstitution M (MvPolynomial.map (algebraMap k K) (Q i)))) =
        RingHom.ker P.toRingHom)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hmem : PfaffianDescent.linearSubstitution M
      (MvPolynomial.map (algebraMap k K) F) ∈ RingHom.ker P.toRingHom) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  obtain ⟨x, hx, hFx⟩ := QuarticNet.cubic_point_of_mem_three_quadrics_range Q hQ F hF
    (PfaffianDescent.polynomial_mem_span_of_linearSubstitution_map_range_descends M hM Q F
      (by rwa [hideal]))
  exact PfaffianDescent.cubic_projective_section_of_coordinates F hF x hx hFx

/-- The finite alternative in the base-locus calculation.  Outside the
exceptional discriminant, every common zero of the three displayed quadrics
lies on a coordinate axis, hence the projective base locus is supported at
the four coordinate vertices. -/
theorem sectionFour_nonexceptional_base_locus_common_zero_is_coordinate_axis
    {k : Type u} [Field k]
    (a b c d e f : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : QuarticNet.baseLocusDelta a b c d e f ≠ 0)
    (x : Fin 4 → k)
    (h₁ : QuarticNet.offDiagonalQuadricEval
      (QuarticNet.baseLocusQuadric1 a b c d e f) x = 0)
    (h₂ : QuarticNet.offDiagonalQuadricEval
      (QuarticNet.baseLocusQuadric2 a b c d e f) x = 0)
    (h₃ : QuarticNet.offDiagonalQuadricEval
      (QuarticNet.baseLocusQuadric3 a b c d e f) x = 0) :
    ∃ i : Fin 4, ∀ j, j ≠ i → x j = 0 :=
  QuarticNet.baseLocus_common_zero_is_coordinate_axis_of_delta_ne_zero
    a b c d e f ha hb hc hd he hdelta x h₁ h₂ h₃

/-- The linear-decomposition form of the finite branch of the base-locus
lemma.  The displayed nonexceptional net gives the three degree-one
coefficients in the cubic equation directly. -/
theorem sectionFour_nonexceptional_tangent_net_linear_decomposition
    {k : Type u} [Field k]
    (a b c d e f : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (hdelta : QuarticNet.baseLocusDelta a b c d e f ≠ 0)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hvan : ∀ i : Fin 4,
      MvPolynomial.aeval (QuarticNet.tangentDualPoint
        (QuarticNet.skewTangentDirections a b c d e f) i) F = 0) :
    ∃ H₁ H₂ H₃ : MvPolynomial (Fin 4) k,
      H₁.IsHomogeneous 1 ∧ H₂.IsHomogeneous 1 ∧ H₃.IsHomogeneous 1 ∧
        F = H₁ * QuarticNet.scaledBaseLocusQuadricPolynomials a b c d e f 0 +
          H₂ * QuarticNet.scaledBaseLocusQuadricPolynomials a b c d e f 1 +
          H₃ * QuarticNet.scaledBaseLocusQuadricPolynomials a b c d e f 2 := by
  let Q := QuarticNet.scaledBaseLocusQuadricPolynomials a b c d e f
  have hset : Set.range Q = {Q 0, Q 1, Q 2} := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h | h)
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
  obtain ⟨H₁, H₂, H₃, hH₁, hH₂, hH₃, hdecomp⟩ :=
    sectionFour_linear_quadric_decomposition_of_mem_three_quadrics
      F (Q 0) (Q 1) (Q 2) hF
      (QuarticNet.scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f 0)
      (QuarticNet.scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f 1)
      (QuarticNet.scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f 2) (by
        rw [← hset]
        exact QuarticNet.cubic_mem_scaledBaseLocus_ideal_of_nonexceptional_tangent_vanishing
          a b c d e f ha hb hc hd he hf hdelta F hF hvan)
  exact ⟨H₁, H₂, H₃, hH₁, hH₂, hH₃, by simpa [Q] using hdecomp⟩

/-- The finite branch of the literal Section 4 tangent-net argument.  A
nonexceptional skew tangent matrix forces every cubic through the four double
points into the ideal of the three displayed quadrics, and hence gives a
rational section. -/
theorem sectionFour_nonexceptional_tangent_net_section
    {k : Type u} [Field k]
    (a b c d e f : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0)
    (hdelta : QuarticNet.baseLocusDelta a b c d e f ≠ 0)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hvan : ∀ i : Fin 4,
      MvPolynomial.aeval (QuarticNet.tangentDualPoint
        (QuarticNet.skewTangentDirections a b c d e f) i) F = 0) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  let Q := QuarticNet.scaledBaseLocusQuadricPolynomials a b c d e f
  have hset : Set.range Q = {Q 0, Q 1, Q 2} := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h | h)
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
  apply QuarticNet.cubic_section_of_mem_three_quadrics F (Q 0) (Q 1) (Q 2) hF
  · exact QuarticNet.scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f 0
  · exact QuarticNet.scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f 1
  · exact QuarticNet.scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f 2
  · rw [← hset]
    exact QuarticNet.cubic_mem_scaledBaseLocus_ideal_of_nonexceptional_tangent_vanishing
      a b c d e f ha hb hc hd he hf hdelta F hF hvan

/-- The four-cycle branch of Proposition 4.2: the three explicit quadrics
force a cubic through the four tangent double points to have a rational
section. -/
theorem sectionFour_fourCycle_tangent_net_section
    {k : Type u} [Field k]
    (b c d e : k) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hvan : ∀ i : Fin 4,
      MvPolynomial.aeval (QuarticNet.tangentDualPoint
        (QuarticNet.skewTangentDirections 0 b c d e 0) i) F = 0) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  let Q := QuarticNet.fourCycleScaledQuadricPolynomials b c d e
  have hset : Set.range Q = {Q 0, Q 1, Q 2} := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h | h)
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
  apply QuarticNet.cubic_section_of_mem_three_quadrics F (Q 0) (Q 1) (Q 2) hF
  · exact QuarticNet.fourCycleScaledQuadricPolynomials_homogeneous b c d e 0
  · exact QuarticNet.fourCycleScaledQuadricPolynomials_homogeneous b c d e 1
  · exact QuarticNet.fourCycleScaledQuadricPolynomials_homogeneous b c d e 2
  · rw [← hset]
    exact QuarticNet.cubic_mem_fourCycleScaled_ideal_of_nonzero_tangent_vanishing
      b c d e hb hc hd he F hF hvan

/-- The matching branch of Proposition 4.2.  Its two geometric lines form a
Galois-stable pair, and the checked quadratic descent produces a section over
the ground field. -/
theorem sectionFour_matching_tangent_net_section
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    (B : Basis (Fin 4) K (Fin 4 → K))
    (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (hskew : ∀ i j, U i j = -U j i)
    (hmatch : QuarticNet.matchingPattern (QuarticNet.nonzeroEdge (U 0 1))
      (QuarticNet.nonzeroEdge (U 0 2)) (QuarticNet.nonzeroEdge (U 0 3))
      (QuarticNet.nonzeroEdge (U 1 2)) (QuarticNet.nonzeroEdge (U 1 3))
      (QuarticNet.nonzeroEdge (U 2 3)))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hvan : ∀ r : Fin 4,
      MvPolynomial.aeval (QuarticNet.tangentDualPoint U r)
        (PfaffianDescent.linearSubstitution (QuarticNet.basisCoordinateMatrix B)
          (MvPolynomial.map (algebraMap k K) F)) = 0)
    (hact : ∀ g : K ≃ₐ[k] K, ∃ τ : Equiv.Perm (Fin 4),
      (∀ i m, g (B i m) = B (τ i) m) ∧
      (∀ i j, U i j ≠ 0 ↔ U (τ i) (τ j) ≠ 0)) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  obtain ⟨x, hx, hFx⟩ := QuarticNet.cubic_point_of_matching_skew_geometric_net
    B U hdiag hskew hmatch F hF hvan hact
  exact PfaffianDescent.cubic_projective_section_of_coordinates F hF x hx hFx

/-- The arithmetic tangent-net construction gives a ground-field section in
every finite-support branch.  The sole remaining case is the full-support
exceptional locus where the base-locus discriminant vanishes. -/
theorem sectionFour_ground_jet_section_or_exceptional
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Normal k K] [Infinite K] [IsGalois k K]
    {L : Type u} [Field L] [Algebra k L]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hp : p 0 = 1) (hv0 : v 0 = 0) (hv : v ≠ 0)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (hdim : 3 ≤ Module.finrank k (QuarticNet.affineJetQuadrics (k := k)
      (fun i : Fin 3 => p i.succ) (fun i : Fin 3 => v i.succ)))
    (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0)
    (hskew : ∀ i j, l i * QuarticNet.conjugateTangentMatrix e p v hspan i j =
      -(l j * QuarticNet.conjugateTangentMatrix e p v hspan j i))
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hFjet : MvPolynomial.aeval (R := k) (S₁ := DualNumber L)
      (fun i => TrivSqZeroExt.inl (p i) + TrivSqZeroExt.inr (v i)) F = 0) :
    (∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _) ∨
      ((∀ i j, i ≠ j →
        QuarticNet.rescaleTangentDirections l (QuarticNet.conjugateTangentMatrix e p v hspan) i j ≠ 0) ∧
      QuarticNet.baseLocusDelta
        (QuarticNet.rescaleTangentDirections l (QuarticNet.conjugateTangentMatrix e p v hspan) 0 1)
        (QuarticNet.rescaleTangentDirections l (QuarticNet.conjugateTangentMatrix e p v hspan) 0 2)
        (QuarticNet.rescaleTangentDirections l (QuarticNet.conjugateTangentMatrix e p v hspan) 0 3)
        (QuarticNet.rescaleTangentDirections l (QuarticNet.conjugateTangentMatrix e p v hspan) 1 2)
        (QuarticNet.rescaleTangentDirections l (QuarticNet.conjugateTangentMatrix e p v hspan) 1 3)
        (QuarticNet.rescaleTangentDirections l (QuarticNet.conjugateTangentMatrix e p v hspan) 2 3) = 0) := by
  obtain hpoint | hexception :=
    QuarticNet.cubic_point_or_exceptional_full_support_ground_jet
      e p v hp hv0 hv hspan hdim l hl hskew F hF hFjet
  · obtain ⟨x, hx, hFx⟩ := hpoint
    exact Or.inl (PfaffianDescent.cubic_projective_section_of_coordinates F hF x hx hFx)
  · exact Or.inr hexception

/-- Starting from the affine chart at a separable degree-four point, the
trace-selected length-eight subscheme gives a section in every finite branch.
The remaining alternative is exactly the exceptional full-support locus. -/
theorem sectionFour_affine_degree_four_point_section_or_exceptional
    {k L K : Type u} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    [IsAlgClosed K] [Normal k K] [IsGalois k K]
    (b : Basis (Fin 4) k L) (hb : b 0 = 1)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hp : MvPolynomial.aeval b F = 0)
    (hsmooth : QuarticNet.affineDifferential (fun i : Fin 3 => b i.succ)
      (QuarticNet.dehomogenizeAtZero F) ≠ 0) :
    (∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _) ∨
      (∃ (e : Fin 4 ≃ (L →ₐ[k] K)) (v : Fin 3 → L) (l : Fin 4 → K),
        (∀ i, l i ≠ 0) ∧
        (∀ i j, i ≠ j →
          QuarticNet.rescaleTangentDirections l
            (QuarticNet.conjugateTangentMatrix e b (Fin.cons 0 v)
              (QuarticNet.conjugate_basis_span b e)) i j ≠ 0) ∧
        QuarticNet.baseLocusDelta
          (QuarticNet.rescaleTangentDirections l
            (QuarticNet.conjugateTangentMatrix e b (Fin.cons 0 v)
              (QuarticNet.conjugate_basis_span b e)) 0 1)
          (QuarticNet.rescaleTangentDirections l
            (QuarticNet.conjugateTangentMatrix e b (Fin.cons 0 v)
              (QuarticNet.conjugate_basis_span b e)) 0 2)
          (QuarticNet.rescaleTangentDirections l
            (QuarticNet.conjugateTangentMatrix e b (Fin.cons 0 v)
              (QuarticNet.conjugate_basis_span b e)) 0 3)
          (QuarticNet.rescaleTangentDirections l
            (QuarticNet.conjugateTangentMatrix e b (Fin.cons 0 v)
              (QuarticNet.conjugate_basis_span b e)) 1 2)
          (QuarticNet.rescaleTangentDirections l
            (QuarticNet.conjugateTangentMatrix e b (Fin.cons 0 v)
              (QuarticNet.conjugate_basis_span b e)) 1 3)
          (QuarticNet.rescaleTangentDirections l
            (QuarticNet.conjugateTangentMatrix e b (Fin.cons 0 v)
              (QuarticNet.conjugate_basis_span b e)) 2 3) = 0) := by
  obtain hpoint | hexception := QuarticNet.affine_cubic_point_or_exceptional_tangent_net
    (K := K) b hb F hF hp hsmooth
  · obtain ⟨x, hx, hFx⟩ := hpoint
    exact Or.inl (PfaffianDescent.cubic_projective_section_of_coordinates F hF x hx hFx)
  · exact Or.inr hexception

/-- The tangent-direction construction in Proposition 4.3 gives the stated
projective length-eight subscheme on the cubic, with its rank computed over
the ground field. -/
theorem sectionFour_affine_length_eight_subscheme
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (b : Basis (Fin 4) k L) (hb : b 0 = 1)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hpoint : MvPolynomial.aeval b F = 0)
    (hsmooth : QuarticNet.affineDifferential (fun i : Fin 3 => b i.succ)
      (QuarticNet.dehomogenizeAtZero F) ≠ 0) :
    ∃ (v : Fin 3 → L), v ≠ 0 ∧
      ∃ (j : Spec (.of (DualNumber L)) ⟶ hypersurface F hF),
        IsClosedImmersion j ∧ ∃ hfinite : IsFinite (j ≫ hypersurfaceToBase F hF),
        @finiteSchemeRank k _ _ (j ≫ hypersurfaceToBase F hF) hfinite = 8 ∧
        j ≫ hypersurfaceToBase F hF =
          Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber L))) :=
  QuarticNet.affine_length_eight_projectivized b hb F hF hpoint hsmooth

/-- The length-eight construction and its net of three quadrics are
simultaneous: the tangent subscheme is contained in the actual
scheme-theoretic quadric--cubic intersection.  This is the projective
scheme form of Proposition 4.3 used in the exceptional residual branch. -/
theorem sectionFour_affine_length_eight_quadricCubicIntersection
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (b : Basis (Fin 4) k L) (hb : b 0 = 1)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hpoint : MvPolynomial.aeval b F = 0)
    (hsmooth : QuarticNet.affineDifferential (fun i : Fin 3 => b i.succ)
      (QuarticNet.dehomogenizeAtZero F) ≠ 0) :
    ∃ (v : Fin 3 → L) (Q : Fin 3 → MvPolynomial (Fin 4) k), v ≠ 0 ∧
      LinearIndependent k Q ∧ ∃ hQ : ∀ i, (Q i).IsHomogeneous 2,
      ∃ (j : Spec (.of (DualNumber L)) ⟶ scheme
          (QuarticNet.jetQuadricCubicIntersectionIdeal Q hQ F hF)),
        IsClosedImmersion j ∧ ∃ hfinite : IsFinite
          (j ≫ QuarticNet.jetQuadricCubicIntersectionToHypersurface Q hQ F hF ≫
            hypersurfaceToBase F hF),
        @finiteSchemeRank k _ _
          (j ≫ QuarticNet.jetQuadricCubicIntersectionToHypersurface Q hQ F hF ≫
            hypersurfaceToBase F hF) hfinite = 8 :=
  QuarticNet.affine_length_eight_quadricCubicIntersection b hb F hF hpoint hsmooth

/-- The exceptional full-support branch of the base-locus lemma.  If `Δ`
vanishes, the three displayed quadrics generate the ideal of the explicit
twisted cubic, recorded as the kernel of its binary-cubic parametrization. -/
theorem sectionFour_exceptional_tangent_net_twisted_cubic_ideal
    {k : Type u} [Field k]
    (a b c d e f : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : QuarticNet.baseLocusDelta a b c d e f = 0) :
    Ideal.span (Set.range (QuarticNet.scaledBaseLocusQuadricPolynomials a b c d e f)) =
      RingHom.ker (QuarticNet.exceptionalTwistedCubicParam a b c d e).toRingHom :=
  QuarticNet.exceptionalTwistedCubic_ideal_eq_param_ker a b c d e f
    ha hb hc hd he hdelta

/-- The exceptional base-locus curve is a twisted cubic in the full embedded
sense: an invertible ground-field coordinate change takes its homogeneous
ideal to the standard cubic ideal. -/
theorem sectionFour_exceptional_tangent_net_ground_twisted_cubic_presentation
    {k : Type u} [Field k]
    (a b c d e f : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : QuarticNet.baseLocusDelta a b c d e f = 0) :
    QuarticNet.GroundTwistedCubicPresentation
      (QuarticNet.exceptionalTwistedCubicHomogeneousIdeal a b c d e f) :=
  QuarticNet.exceptionalTwistedCubic_groundPresentation
    a b c d e f ha hb hc hd he hdelta

/-- The exceptional base curve is the ground projective line, smoothly and
with its standard cubic embedding.  This gives the full conclusion of
`lem:twisted-cubic` for the explicit exceptional branch of Section 4. -/
theorem sectionFour_exceptional_tangent_net_twisted_cubic_descent
    {k : Type u} [Field k]
    (a b c d e f : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : QuarticNet.baseLocusDelta a b c d e f = 0) :
    ∃ e' : scheme (QuarticNet.exceptionalTwistedCubicHomogeneousIdeal a b c d e f) ≅
        projectiveLineProj k,
      e'.hom ≫ projectiveLineProjToBase k =
          toBase (QuarticNet.exceptionalTwistedCubicHomogeneousIdeal a b c d e f) ∧
        Smooth (toBase (QuarticNet.exceptionalTwistedCubicHomogeneousIdeal a b c d e f)) ∧
          ∃ s : Spec (.of k) ⟶
              scheme (QuarticNet.exceptionalTwistedCubicHomogeneousIdeal a b c d e f),
            s ≫ toBase (QuarticNet.exceptionalTwistedCubicHomogeneousIdeal a b c d e f) = 𝟙 _ := by
  let hground : QuarticNet.GroundTwistedCubicPresentation
      (QuarticNet.exceptionalTwistedCubicHomogeneousIdeal a b c d e f) :=
    QuarticNet.exceptionalTwistedCubic_groundPresentation
      a b c d e f ha hb hc hd he hdelta
  refine ⟨hground.schemeIsoProjectiveLine,
    hground.schemeIsoProjectiveLine_hom_toBase, hground.toBase_smooth, ?_⟩
  exact QuarticNet.exceptionalTwistedCubic_has_rational_section
    a b c d e f ha hb hc hd he hdelta

/-- The explicit exceptional twisted cubic has a rational section over the
ground field.  This is the split twisted-cubic point used in the contained
curve alternative of the degree-four proof. -/
theorem sectionFour_exceptional_twisted_cubic_has_rational_section
    {k : Type u} [Field k]
    (a b c d e f : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : QuarticNet.baseLocusDelta a b c d e f = 0) :
    ∃ s : Spec (.of k) ⟶
      scheme (QuarticNet.exceptionalTwistedCubicHomogeneousIdeal a b c d e f),
      s ≫ toBase (QuarticNet.exceptionalTwistedCubicHomogeneousIdeal a b c d e f) = 𝟙 _ :=
  QuarticNet.exceptionalTwistedCubic_has_rational_section a b c d e f
    ha hb hc hd he hdelta

/-- The exceptional twisted-cubic parametrization contains the four
normalized tangent double points, in the explicit binary coordinates used by
the residual-degree-nine argument. -/
theorem sectionFour_exceptional_param_contains_tangent_net
    {k : Type u} [Field k]
    (a b c d e f : k) (hdelta : QuarticNet.baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hvan : ∀ i : Fin 4,
      MvPolynomial.aeval (QuarticNet.tangentDualPoint
        (QuarticNet.skewTangentDirections a b c d e f) i) F = 0) :
    MvPolynomial.aeval ![(1 : DualNumber k), TrivSqZeroExt.inr a]
        (QuarticNet.exceptionalTwistedCubicParam a b c d e F) = 0 ∧
      MvPolynomial.aeval ![TrivSqZeroExt.inr (-a), (1 : DualNumber k)]
        (QuarticNet.exceptionalTwistedCubicParam a b c d e F) = 0 ∧
      MvPolynomial.aeval ![TrivSqZeroExt.inl b + TrivSqZeroExt.inr (-b * b * d),
        TrivSqZeroExt.inl d] (QuarticNet.exceptionalTwistedCubicParam a b c d e F) = 0 ∧
      MvPolynomial.aeval ![TrivSqZeroExt.inl c + TrivSqZeroExt.inr (-c * c * e),
        TrivSqZeroExt.inl e] (QuarticNet.exceptionalTwistedCubicParam a b c d e F) = 0 :=
  QuarticNet.exceptional_param_contains_normalized_tangent_net a b c d e f hdelta F hF hvan

/-- In the non-contained exceptional branch, the actual projective
intersection of the three base-locus quadrics with the cubic is finite of
rank nine.  This is the projective form of the degree calculation used by
the residual argument. -/
theorem sectionFour_exceptional_projective_intersection_rank_nine
    {k : Type u} [Field k] [Infinite k]
    (a b c d e f : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : QuarticNet.baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hnonzero : QuarticNet.exceptionalTwistedCubicParam a b c d e F ≠ 0) :
    ∃ hfinite : IsFinite (toBase
      (QuarticNet.exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF)),
      @finiteSchemeRank k _ _ (toBase
        (QuarticNet.exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF)) hfinite = 9 := by
  let hfinite : IsFinite (toBase
      (QuarticNet.exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF)) :=
    QuarticNet.exceptionalTwistedCubicCubicIntersection_isFinite
      a b c d e f ha hb hc hd he hdelta F hF hnonzero
  letI : IsFinite (toBase
      (QuarticNet.exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF)) := hfinite
  exact ⟨hfinite,
    QuarticNet.exceptionalTwistedCubicCubicIntersection_finiteSchemeRank
      a b c d e f ha hb hc hd he hdelta F hF hnonzero⟩

/-- The same rank-nine conclusion applies to any homogeneous net of three
quadrics whose ideal is identified with the exceptional twisted-cubic
parametrization kernel.  This is the form used after the tangent-net
coordinates have been selected. -/
theorem sectionFour_exceptional_quadricCubicIntersection_rank_nine
    {k : Type u} [Field k] [Infinite k]
    (a b c d e f : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : QuarticNet.baseLocusDelta a b c d e f = 0)
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (hQideal : Ideal.span (Set.range Q) =
      RingHom.ker (QuarticNet.exceptionalTwistedCubicParam a b c d e).toRingHom)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hnonzero : QuarticNet.exceptionalTwistedCubicParam a b c d e F ≠ 0) :
    ∃ hfinite : IsFinite (toBase (QuarticNet.jetQuadricCubicIntersectionIdeal Q hQ F hF)),
      @finiteSchemeRank k _ _
        (toBase (QuarticNet.jetQuadricCubicIntersectionIdeal Q hQ F hF)) hfinite = 9 :=
  QuarticNet.jetQuadricCubicIntersection_exceptional_finiteSchemeRank
    a b c d e f ha hb hc hd he hdelta Q hQ hQideal F hF hnonzero

/-- In the non-contained exceptional branch, the binary parameter-space
intersection with the cubic is a finite scheme of rank nine. -/
theorem sectionFour_exceptional_binary_intersection_rank_nine
    {k : Type u} [Field k] [Infinite k]
    (a b c d e : k) (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hnonzero : QuarticNet.exceptionalTwistedCubicParam a b c d e F ≠ 0) :
    ∃ hfinite : IsFinite (toBase (equationIdeal
      (QuarticNet.exceptionalTwistedCubicParam a b c d e F)
      (QuarticNet.exceptionalTwistedCubicParam_homogeneous a b c d e hF))),
      @finiteSchemeRank k _ _ (toBase (equationIdeal
        (QuarticNet.exceptionalTwistedCubicParam a b c d e F)
        (QuarticNet.exceptionalTwistedCubicParam_homogeneous a b c d e hF))) hfinite = 9 := by
  let hfinite : IsFinite (toBase (equationIdeal
      (QuarticNet.exceptionalTwistedCubicParam a b c d e F)
      (QuarticNet.exceptionalTwistedCubicParam_homogeneous a b c d e hF))) :=
    QuarticNet.exceptional_param_cubic_intersection_isFinite a b c d e F hF hnonzero
  letI : IsFinite (toBase (equationIdeal
      (QuarticNet.exceptionalTwistedCubicParam a b c d e F)
      (QuarticNet.exceptionalTwistedCubicParam_homogeneous a b c d e hF))) := hfinite
  exact ⟨hfinite,
    QuarticNet.exceptional_param_cubic_intersection_rank a b c d e F hF hnonzero⟩

/-- The residual-degree-nine step for the exceptional branch. Once the
quartic tangent double point is identified with the displayed parametrization
of the `Δ = 0` twisted cubic, this produces a rational section. -/
theorem sectionFour_exceptional_twisted_cubic_section
    {k : Type u} [Field k]
    (a b c d e f : k)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : QuarticNet.baseLocusDelta a b c d e f = 0)
    {L : Type u} [Field L] [Algebra k L] [Algebra.IsSeparable k L]
    (r w : L) (hw : w ≠ 0) (hr : (minpoly k r).natDegree = 4)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hjet : MvPolynomial.aeval ![(1 : DualNumber L),
      TrivSqZeroExt.inl r + TrivSqZeroExt.inr w]
      (QuarticNet.exceptionalTwistedCubicParam a b c d e F) = 0) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  obtain ⟨x, hx, hFx⟩ :=
    QuarticNet.cubic_point_of_exceptional_twisted_cubic_double_point
      a b c d e f ha hb hc hd he hdelta r w hw hr F hF hjet
  exact PfaffianDescent.cubic_projective_section_of_coordinates F hF x hx hFx

/-- The non-contained exceptional alternative becomes a rational section once
the ground intersection of the exceptional base curve with the cubic is
realized as a rank-nine finite scheme containing the rank-eight tangent jet. -/
theorem sectionFour_rank_nine_exceptional_intersection_section
    {k : Type u} [Field k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    {X Z : Scheme.{u}}
    (c : X ⟶ hypersurface F hF)
    (i : Z ⟶ X) [IsClosedImmersion i]
    [IsFinite (c ≫ hypersurfaceToBase F hF)]
    (hX : finiteSchemeRank (c ≫ hypersurfaceToBase F hF) = 9)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase F hF) = 8) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ :=
  QuarticNet.cubic_section_of_rank_nine_exceptional_intersection F hF c i hX hZ

/-- The full non-contained exceptional branch after coefficient extension and
an invertible coordinate change.  The rank-nine intersection and its
finiteness descend to the ground field before the rank-eight tangent jet is
removed. -/
theorem sectionFour_coordinateChanged_exceptional_jet_section
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Infinite K]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (Q : Fin 3 → MvPolynomial (Fin 4) k)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : QuarticNet.baseLocusDelta a b c d e f = 0)
    (hQideal : Ideal.span (Set.range (fun i =>
      PfaffianDescent.linearSubstitution M (MvPolynomial.map (algebraMap k K) (Q i)))) =
        RingHom.ker (QuarticNet.exceptionalTwistedCubicParam a b c d e).toRingHom)
    (hnonzero : QuarticNet.exceptionalTwistedCubicParam a b c d e
      (PfaffianDescent.linearSubstitution M (MvPolynomial.map (algebraMap k K) F)) ≠ 0)
    {Z : Scheme.{u}}
    (j : Z ⟶ scheme (QuarticNet.jetQuadricCubicIntersectionIdeal Q hQ F hF))
    [IsClosedImmersion j]
    [IsFinite (j ≫ QuarticNet.jetQuadricCubicIntersectionToHypersurface Q hQ F hF ≫
      hypersurfaceToBase F hF)]
    (hjet : finiteSchemeRank
      (j ≫ QuarticNet.jetQuadricCubicIntersectionToHypersurface Q hQ F hF ≫
        hypersurfaceToBase F hF) = 8) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ :=
  QuarticNet.cubic_section_of_ground_exceptional_jet_intersection
    M hM Q hQ F hF a b c d e f ha hb hc hd he hdelta hQideal hnonzero j hjet

/-- The complete tangent-net proof of the degree-four affine branch.  Its
full-support discriminant-zero case is discharged by the descended
rank-nine exceptional intersection, so no exceptional alternative remains. -/
theorem sectionFour_smooth_affine_degree_four_point_section
    {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    [IsAlgClosed K] [Normal k K] [IsGalois k K]
    (b : Basis (Fin 4) k L) (hb : b 0 = 1)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hp : MvPolynomial.aeval b F = 0)
    (hsmooth : QuarticNet.affineDifferential (fun i : Fin 3 => b i.succ)
      (QuarticNet.dehomogenizeAtZero F) ≠ 0) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ :=
  QuarticNet.cubic_section_of_smooth_affine_degree_four_point (K := K)
    b hb F hF hp hsmooth

/-- The perfect-field theorem stated at the start of Section 4, proved by
the coplanar conic/secant and noncoplanar tangent-net arguments. Neither
branch uses the degree-five or Pfaffian results of Section 3. -/
theorem sectionFour_degree_four_closed_point_has_point
    {k : Type u} [Field k] [PerfectField k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 4) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  PfaffianDescent.independent_perfectField_degree_four_closed_point_rational_section
    p hp hne x hx

end AllCharacteristics
