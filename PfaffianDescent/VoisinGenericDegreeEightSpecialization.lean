import Mathlib.Algebra.CharZero.Infinite
import AllCharacteristics.VoisinFiniteEtaleResidualSpecialization
import PfaffianDescent.VoisinDegreeTenResidualEnd
import PfaffianDescent.VoisinDegreeTenResidualEndAdditions
import PfaffianDescent.VoisinDegreeEightRestrictionKernelEtale
import PfaffianDescent.VoisinDegreeEightHomogeneousCurve
import PfaffianDescent.VoisinGenericCubicResidual
import PfaffianDescent.VoisinEffectiveCycleGenericSpecialization
import PfaffianDescent.VoisinGenericQuadraticDetection
import PfaffianDescent.VoisinDegreeEightHilbertCriterion

/-!
# The generic degree-eight geometric premise in Voisin's specialization

The theorem below reduces the degree-eight specialization step to its exact
geometric core: transverse cubic--quadric--quadric data through the canonical
generic eight-point configuration.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- On a smooth cubic over an algebraically closed characteristic-zero field,
the canonical generic length-eight scheme has one coordinate presentation
for which both the ambient polynomial evaluation and quadratic restriction
are surjective. -/
theorem
    cubicConfigurationGenericEight_hasSurjectiveQuadraticCoordinates_of_smooth
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      let pD := cubicConfigurationCoefficientChangedBaseMap p hp 8 a ha
      letI : IsFinite pD := Dη.property.1
      letI := finiteSchemeCoefficientAlgebra pD
      HasSurjectiveQuadraticCoordinates
        (cubicConfigurationBase p hp 8).functionField
        Γ(Dη.val.subscheme, ⊤) := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  letI : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 8).toScheme :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite (cubicConfigurationBase p hp 8).functionField :=
    CharZero.infinite _
  exact cubicConfigurationGenericEight_hasSurjectiveQuadraticCoordinates
    p hp hne (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hne) a ha

/-- The resulting quadratic restriction statement in the form used by
Voisin's fixed-component argument: the full vanishing system is a pencil. -/
theorem cubicConfigurationGenericEight_hasQuadraticPencilCoordinates_of_smooth
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      let pD := cubicConfigurationCoefficientChangedBaseMap p hp 8 a ha
      letI : IsFinite pD := Dη.property.1
      letI := finiteSchemeCoefficientAlgebra pD
      HasQuadraticPencilCoordinates
        (cubicConfigurationBase p hp 8).functionField
        Γ(Dη.val.subscheme, ⊤) := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  letI : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 8).toScheme :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 8 a ha
  letI : IsFinite pD := Dη.property.1
  letI : IsAffine Dη.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  haveI : Module.Finite (cubicConfigurationBase p hp 8).functionField
      Γ(Dη.val.subscheme, ⊤) := finiteSchemeCoefficient_finite pD
  apply HasSurjectiveQuadraticCoordinates.exists_kernel_finrank_eq_two
  · apply (finiteSchemeCoefficient_finrank pD).trans
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact Dη.property.2.2.2
      (IsLocalRing.closedPoint (cubicConfigurationBase p hp 8).functionField)
  · exact
      cubicConfigurationGenericEight_hasSurjectiveQuadraticCoordinates_of_smooth
        p hp hne D₈ a ha

/-- The generic rank-eight configuration has an explicit basis of its full
quadratic restriction kernel.  Thus the remaining proper-intersection issue
is a condition on one finite pencil, rather than a quantifier over an
unspecified space of quadrics. -/
theorem cubicConfigurationGenericEight_exists_quadraticPencilBasisData_of_smooth
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Q := cubicConfigurationBase p hp 8
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      let pD := cubicConfigurationCoefficientChangedBaseMap p hp 8 a ha
      letI : IsFinite pD := Dη.property.1
      letI := finiteSchemeCoefficientAlgebra pD
      ∃ (x : Fin 4 → Γ(Dη.val.subscheme, ⊤))
        (hx : Function.Surjective
          (eval₂Hom (algebraMap Q.functionField Γ(Dη.val.subscheme, ⊤)) x))
        (hker : Module.finrank Q.functionField (LinearMap.ker
          (homogeneousSectionRestriction (K := Q.functionField) x 2)) = 2),
        ∀ i : Fin 2,
          ((quadraticVanishingPencilBasis x hker i).1.1).IsHomogeneous 2 ∧
            (quadraticVanishingPencilBasis x hker i).1.1.eval₂
              (algebraMap Q.functionField Γ(Dη.val.subscheme, ⊤)) x = 0 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 8 a ha
  letI : IsFinite pD := Dη.property.1
  letI : IsAffine Dη.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  haveI : Module.Finite (cubicConfigurationBase p hp 8).functionField
      Γ(Dη.val.subscheme, ⊤) := finiteSchemeCoefficient_finite pD
  apply HasSurjectiveQuadraticCoordinates.exists_pencilBasis_data
  · apply (finiteSchemeCoefficient_finrank pD).trans
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
    exact Dη.property.2.2.2
      (IsLocalRing.closedPoint (cubicConfigurationBase p hp 8).functionField)
  · exact
      cubicConfigurationGenericEight_hasSurjectiveQuadraticCoordinates_of_smooth
        p hp hne D₈ a ha

/-- The generic configuration has a single normalized chart carrying the
canonical basis of its full two-dimensional quadratic pencil. -/
theorem
    cubicConfigurationGenericEight_nonempty_normalizedQuadraticPencilBasisData_of_smooth
    [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Q := cubicConfigurationBase p hp 8
      let p' := p.map a.hom
      let hp' := hp.map a.hom
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : IsFinite
          (Dη.val.subschemeι ≫ hypersurfaceToBase p' hp') := Dη.property.1
      letI := finiteSchemeCoefficientAlgebra
        (Dη.val.subschemeι ≫ hypersurfaceToBase p' hp')
      Nonempty (NormalizedQuadraticPencilBasisData
        Q.functionField Γ(Dη.val.subscheme, ⊤) p') := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  letI : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 8).toScheme :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  obtain ⟨z, hz, hno⟩ :=
    exists_orderedPointOver_genericEight_with_noCommonQuadraticEightEquation
      p hp hne (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hne)
  exact cubicConfigurationGenericEight_normalizedQuadraticPencilBasis_of_noCommon
    p hp a ha z hz hno

/-- Voisin's literal Claim 3.4 on the generic cubic: one properly
intersecting pair of quadrics through the generic rank-eight datum produces
an effective degree-four cycle there.  This statement stops before Fulton's
specialization back to the original fibre. -/
theorem
    effectiveDegreeFourCycle_on_genericCubic_of_genericDegreeEightRegularQuadricPair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightRegularQuadricPairExists
          (p.map a.hom) (hp.map a.hom) Dη →
          ∃ z : EffectiveZeroCycle
              (hypersurface (p.map a.hom) (hp.map a.hom)),
            EffectiveZeroCycle.degree
                (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hpair
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  exact exists_effectiveDegreeFourCycle_of_regularQuadricPair
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne)
    (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha) hpair

/-- Claim 3.4 with the premise stated as absence of a common curve component
in the quadratic system through the generic eight-point configuration. -/
theorem
    effectiveDegreeFourCycle_on_genericCubic_of_genericDegreeEightNoCommonCurveComponent
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightQuadraticSystemHasNoCommonCurveComponent
          (p.map a.hom) (hp.map a.hom) Dη →
          ∃ z : EffectiveZeroCycle
              (hypersurface (p.map a.hom) (hp.map a.hom)),
            EffectiveZeroCycle.degree
                (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hnofixed
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  exact
    effectiveDegreeFourCycle_on_genericCubic_of_genericDegreeEightRegularQuadricPair
      p hp hne D₈ a ha
      (hnofixed.regularPair (p.map a.hom) (hp.map a.hom)
          (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha))

/-- A prime first member of the generic quadratic system is enough for the
degree-four residual. The second member is selected algebraically from the
two-dimensional vanishing system, so this theorem isolates the remaining
geometric task in the repaired incidence proof. -/
theorem
    effectiveDegreeFourCycle_on_genericCubic_of_genericDegreeEightPrimeFirstMember
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightPrimeFirstMemberExists
          (p.map a.hom) (hp.map a.hom) Dη →
          ∃ z : EffectiveZeroCycle
              (hypersurface (p.map a.hom) (hp.map a.hom)),
            EffectiveZeroCycle.degree
                (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hfirst
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  exact
    effectiveDegreeFourCycle_on_genericCubic_of_genericDegreeEightRegularQuadricPair
      p hp hne D₈ a ha
      (DegreeEightRegularQuadricPairExists.of_prime_first_member
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha) hfirst)

/-- Hilbert-function form of Claim 3.4 on the generic cubic.  The eventual
bound for the quotient by the cubic and quadratic pencil supplies the
properly intersecting pair and hence the effective residual cycle. -/
theorem
    effectiveDegreeFourCycle_on_genericCubic_of_genericDegreeEightHilbertBound
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightQuadraticHilbertBoundPairExists
          (p.map a.hom) (hp.map a.hom) Dη →
          ∃ z : EffectiveZeroCycle
              (hypersurface (p.map a.hom) (hp.map a.hom)),
            EffectiveZeroCycle.degree
                (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hbound
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  apply effectiveDegreeFourCycle_on_genericCubic_of_genericDegreeEightRegularQuadricPair
    p hp hne D₈ a ha
  exact hbound.regularPair (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne)
    (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha)

/-- Source-faithful selected-coordinate form of Claim 3.4 on the generic
cubic.  Only the normalized pencil actually used in the residual
construction must satisfy the eventual Hilbert bound. -/
theorem
    effectiveDegreeFourCycle_on_genericCubic_of_selectedDegreeEightHilbertData
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightSelectedQuadraticHilbertData
          (p.map a.hom) (hp.map a.hom) Dη →
          ∃ z : EffectiveZeroCycle
              (hypersurface (p.map a.hom) (hp.map a.hom)),
            EffectiveZeroCycle.degree
                (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hselected
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  exact hselected.effectiveDegreeFourCycle
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne)
    (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha)

/-- A properly intersecting quadratic pair through the generic rank-eight
configuration gives the desired degree-four cycle on the original cubic.
The intermediate generic cycle may be nonreduced. -/
theorem effectiveDegreeFourCycle_of_genericDegreeEightRegularQuadricPair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightRegularQuadricPairExists
          (p.map a.hom) (hp.map a.hom) Dη →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hpair
  obtain ⟨zη, hzη⟩ :=
    effectiveDegreeFourCycle_on_genericCubic_of_genericDegreeEightRegularQuadricPair
      p hp hne D₈ a ha hpair
  exact effectiveDegreeFourCycle_of_genericEffectiveDegreeFourCycle
    p hp hne D₈ a ha zη hzη

/-- A prime first member on the generic configuration supplies the regular
pair and hence the degree-four cycle on the original cubic. This is the
end-to-end interface for the smooth-integral-member incidence proof. -/
theorem effectiveDegreeFourCycle_of_genericDegreeEightPrimeFirstMember
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightPrimeFirstMemberExists
          (p.map a.hom) (hp.map a.hom) Dη →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hfirst
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  exact effectiveDegreeFourCycle_of_genericDegreeEightRegularQuadricPair
    p hp hne D₈ a ha
    (DegreeEightRegularQuadricPairExists.of_prime_first_member
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha) hfirst)

/-- Source-faithful final form of Claim 3.4: absence of a common curve
component in the generic quadratic system produces an effective degree-four
cycle on the original cubic. -/
theorem effectiveDegreeFourCycle_of_genericDegreeEightNoCommonCurveComponent
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightQuadraticSystemHasNoCommonCurveComponent
          (p.map a.hom) (hp.map a.hom) Dη →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hnofixed
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  exact effectiveDegreeFourCycle_of_genericDegreeEightRegularQuadricPair
    p hp hne D₈ a ha
      (hnofixed.regularPair (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha))

/-- Eventual-Hilbert-bound form of Voisin's final degree-eight-to-four
specialization statement. -/
theorem effectiveDegreeFourCycle_of_genericDegreeEightHilbertBound
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightQuadraticHilbertBoundPairExists
          (p.map a.hom) (hp.map a.hom) Dη →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hbound
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  apply effectiveDegreeFourCycle_of_genericDegreeEightRegularQuadricPair
    p hp hne D₈ a ha
  exact hbound.regularPair (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne)
    (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha)

/-- Selected-coordinate eventual-Hilbert form of the final specialization
back from the generic cubic to the original cubic. -/
theorem effectiveDegreeFourCycle_of_selectedGenericDegreeEightHilbertData
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightSelectedQuadraticHilbertData
          (p.map a.hom) (hp.map a.hom) Dη →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hselected
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  obtain ⟨zη, hzη⟩ :=
    effectiveDegreeFourCycle_on_genericCubic_of_selectedDegreeEightHilbertData
      p hp hne D₈ a ha hselected
  exact effectiveDegreeFourCycle_of_genericEffectiveDegreeFourCycle
    p hp hne D₈ a ha zη hzη

/-- Final endpoint for the explicit canonical basis of one normalized
generic pencil.  Smoothness makes the coefficient-changed cubic prime, so
the only extra clause in the premise is the eventual Hilbert bound for the
two basis quadrics. -/
theorem effectiveDegreeFourCycle_of_normalizedGenericPencilBasisHilbertData
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightNormalizedPencilBasisHilbertData
          (p.map a.hom) (hp.map a.hom) Dη →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hbasis
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  have hpmap0 : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne
  have hpprime : Prime (p.map a.hom) :=
    (Ideal.span_singleton_prime hpmap0).mp
      (principalIdeal_map_prime_of_smooth_homogeneous_cubic
        a.hom p hp hne)
  exact effectiveDegreeFourCycle_of_selectedGenericDegreeEightHilbertData
    p hp hne D₈ a ha
      (hbasis.selectedHilbertData_of_prime
        (p.map a.hom) (hp.map a.hom) hpprime
        (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha))

/-- The final specialization with the remaining premise written literally as
an eventual Hilbert bound on one packaged normalized canonical pencil. -/
theorem effectiveDegreeFourCycle_of_exists_normalizedGenericPencilHilbertBound
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Q := cubicConfigurationBase p hp 8
      let p' := p.map a.hom
      let hp' := hp.map a.hom
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : IsFinite
          (Dη.val.subschemeι ≫ hypersurfaceToBase p' hp') := Dη.property.1
      letI := finiteSchemeCoefficientAlgebra
        (Dη.val.subschemeι ≫ hypersurfaceToBase p' hp')
      letI : Module.Finite Q.functionField Γ(Dη.val.subscheme, ⊤) :=
        finiteSchemeCoefficient_finite
          (Dη.val.subschemeι ≫ hypersurfaceToBase p' hp')
      (∃ d : NormalizedQuadraticPencilBasisData
          Q.functionField Γ(Dη.val.subscheme, ⊤) p',
        d.HasEventualHilbertBound) →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  letI : IsFinite
      (Dη.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := Dη.property.1
  letI := finiteSchemeCoefficientAlgebra
    (Dη.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
  haveI : Module.Finite B.functionField Γ(Dη.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (Dη.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
  intro hexists
  obtain ⟨d, hbound⟩ := hexists
  apply effectiveDegreeFourCycle_of_normalizedGenericPencilBasisHilbertData
    p hp hne D₈ a ha
  exact d.normalizedHilbertData
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha) hbound

/-- The final specialization with the remaining premise expressed as the
literal non-zero-divisor condition for the canonical pair of one normalized
generic quadratic pencil. -/
theorem effectiveDegreeFourCycle_of_exists_normalizedGenericPencilRegularPair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Q := cubicConfigurationBase p hp 8
      let p' := p.map a.hom
      let hp' := hp.map a.hom
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : IsFinite
          (Dη.val.subschemeι ≫ hypersurfaceToBase p' hp') := Dη.property.1
      letI := finiteSchemeCoefficientAlgebra
        (Dη.val.subschemeι ≫ hypersurfaceToBase p' hp')
      letI : Module.Finite Q.functionField Γ(Dη.val.subscheme, ⊤) :=
        finiteSchemeCoefficient_finite
          (Dη.val.subschemeι ≫ hypersurfaceToBase p' hp')
      (∃ d : NormalizedQuadraticPencilBasisData
          Q.functionField Γ(Dη.val.subscheme, ⊤) p',
        d.HasCanonicalRegularPair) →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  letI : IsFinite
      (Dη.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := Dη.property.1
  letI := finiteSchemeCoefficientAlgebra
    (Dη.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
  haveI : Module.Finite B.functionField Γ(Dη.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite
      (Dη.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
  intro hexists
  obtain ⟨d, hregular⟩ := hexists
  have hpmap0 : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne
  have hpprime : Prime (p.map a.hom) :=
    (Ideal.span_singleton_prime hpmap0).mp
      (principalIdeal_map_prime_of_smooth_homogeneous_cubic
        a.hom p hp hne)
  apply effectiveDegreeFourCycle_of_exists_normalizedGenericPencilHilbertBound
    p hp hne D₈ a ha
  exact ⟨d,
    (d.hasEventualHilbertBound_iff_regular
      (hp.map a.hom) hpprime).mpr hregular⟩

/-- The associated-prime avoidance form of the degree-eight input implies
Voisin's no-common-curve form as soon as a regular first quadric pair is
available.  This gives the degree-four cycle directly from the two concrete
selection interfaces. -/
theorem effectiveDegreeFourCycle_of_genericDegreeEightAvoidance_and_regularPair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightSecondQuadricAvoidsAssociatedPrimes
          (p.map a.hom) (hp.map a.hom) Dη →
      DegreeEightRegularQuadricPairExists
          (p.map a.hom) (hp.map a.hom) Dη →
      ∃ z : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro havoid hpair
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField :=
    CharZero.infinite _
  apply effectiveDegreeFourCycle_of_genericDegreeEightNoCommonCurveComponent
    p hp hne D₈ a ha
  exact DegreeEightQuadraticSystemHasNoCommonCurveComponent.of_avoidsAssociatedPrimes
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha) hpair havoid

/-- Voisin's proper-intersection argument on the generic cubic, before
specialization back to the original fibre.  The associated-prime rank drop
chooses a regular pair of quadrics through the generic rank-eight datum; the
difference of the complete-intersection and datum fundamental cycles is an
effective degree-four cycle. -/
theorem effectiveDegreeFourCycle_on_genericCubic_of_genericDegreeEightFinrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightSecondQuadricFinrankDrop
          (p.map a.hom) (hp.map a.hom) Dη →
          ∃ z : EffectiveZeroCycle
              (hypersurface (p.map a.hom) (hp.map a.hom)),
            EffectiveZeroCycle.degree
                (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hdrop
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 8 a
  exact exists_effectiveDegreeFourCycle_of_smooth_cubic_and_finrankDrop
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne)
    (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha) hdrop

/-- Compatibility form of the generic proper-intersection result with the
stronger Frobenius premise used by the scheme-theoretic residual route. -/
theorem
    effectiveDegreeFourCycle_on_genericCubic_of_genericDegreeEightFinrankDrop_and_frobenius
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightSecondQuadricFinrankDrop
          (p.map a.hom) (hp.map a.hom) Dη →
        CubicTwoQuadricRegularCompleteIntersectionsFrobenius
            (p.map a.hom) (hp.map a.hom)
            (cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne) →
          ∃ z : EffectiveZeroCycle
              (hypersurface (p.map a.hom) (hp.map a.hom)),
            EffectiveZeroCycle.degree
                (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hdrop _hfrob
  exact effectiveDegreeFourCycle_on_genericCubic_of_genericDegreeEightFinrankDrop
    p hp hne D₈ a ha hdrop

/-- Transverse quadratic complete-intersection data through the canonical
generic rank-eight configuration produces an effective degree-four cycle on
the original cubic surface. -/
theorem effectiveDegreeFourCycle_of_genericDegreeEightTransverseQuadrics
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8)
      (T : letI : CharZero
            (cubicConfigurationBase p hp 8).functionField :=
            charZero_cubicConfigurationFunctionField_of_flat p hp 8
        DegreeEightTransverseQuadricIntersectionData
          (p.map a.hom) (hp.map a.hom)
          (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha)),
      ∃ z : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha T
  letI : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left := by
    change IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 8).left
    exact
      isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  have hneη : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne
  obtain ⟨R₄, -, hEt⟩ :=
    exists_degreeFourResidualDatum_and_toBase_etale_of_transverseQuadricIntersectionData
      (p.map a.hom) (hp.map a.hom) hneη Dη T
  letI : Etale (R₄.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := hEt
  exact effectiveDegreeFourCycle_of_genericFiniteEtaleResidual
    p hp D₈ a ha R₄

/-- The generic degree-eight step with two sufficient geometric inputs
exposed separately.  The associated-prime rank drop is a uniform strengthening
of Voisin's existential no-fixed-curve assertion: it implies that assertion
on a smooth cubic, but quantifies over every admissible first quadric.  The
second premise is the Bertini transversality assertion for a regular pair
selected from that system. -/
theorem effectiveDegreeFourCycle_of_genericDegreeEightFinrankDrop_and_transverse
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightSecondQuadricFinrankDrop
          (p.map a.hom) (hp.map a.hom) Dη →
        (∀ (q r : MvPolynomial (Fin 4)
              (cubicConfigurationBase p hp 8).functionField)
          (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
          q ≠ 0 → IsRelPrime (p.map a.hom) q →
          (∀ y : MvPolynomial (Fin 4)
              (cubicConfigurationBase p hp 8).functionField,
            r * y ∈ Ideal.span
                ({p.map a.hom, q} : Set (MvPolynomial (Fin 4)
                  (cubicConfigurationBase p hp 8).functionField)) →
              y ∈ Ideal.span
                ({p.map a.hom, q} : Set (MvPolynomial (Fin 4)
                  (cubicConfigurationBase p hp 8).functionField))) →
          Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
            (p.map a.hom) q r (hp.map a.hom) hq hr))) →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hdrop htransverse
  letI : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left := by
    change IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 8).left
    exact
      isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 8 a
  let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  have hneη : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne
  obtain ⟨R₄, -, hEt, -⟩ :=
    exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_finrank_drop
      (p.map a.hom) (hp.map a.hom) hneη Dη hdrop htransverse
  letI : Etale (R₄.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := hEt
  exact effectiveDegreeFourCycle_of_genericFiniteEtaleResidual
    p hp D₈ a ha R₄

/-- The generic degree-eight specialization from the exact point-specific
last Bertini statement.  Only one second quadric, selected after the first
quadric is fixed, must be simultaneously regular and transverse. -/
theorem effectiveDegreeFourCycle_of_genericDegreeEightRegularTransverseSecondQuadric
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightRegularTransverseSecondQuadricExists
          (p.map a.hom) (hp.map a.hom) Dη →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hselect
  letI : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left := by
    change IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 8).left
    exact
      isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 8 a
  let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  have hneη : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne
  obtain ⟨R₄, -, hEt, -⟩ :=
    exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_regularTransverseSecondQuadric
      (p.map a.hom) (hp.map a.hom) hneη Dη hselect
  letI : Etale (R₄.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := hEt
  exact effectiveDegreeFourCycle_of_genericFiniteEtaleResidual
    p hp D₈ a ha R₄

/-- The generic specialization from Voisin's exact final quadratic Bertini
conclusion: the two quadrics may be chosen together. -/
theorem effectiveDegreeFourCycle_of_genericDegreeEightRegularTransverseQuadricPair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightRegularTransverseQuadricPairExists
          (p.map a.hom) (hp.map a.hom) Dη →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hpair
  letI : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left := by
    change IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 8).left
    exact
      isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 8 a
  let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  have hneη : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne
  obtain ⟨R₄, -, hEt, -⟩ :=
    exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_regularTransverseQuadricPair
      (p.map a.hom) (hp.map a.hom) hneη Dη hpair
  letI : Etale (R₄.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := hEt
  exact effectiveDegreeFourCycle_of_genericFiniteEtaleResidual
    p hp D₈ a ha R₄

/-- The generic specialization expressed through the exact universal-family
frontier: choose one first quadric whose full restriction-kernel
singular-member locus is proper. The mixed-degree étale-regularity theorem
supplies regularity of the selected second quadric automatically. -/
theorem effectiveDegreeFourCycle_of_genericDegreeEightRestrictionKernelProperPair
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightQuadraticRestrictionKernelProperPairExists
          (p.map a.hom) (hp.map a.hom) Dη →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hproper
  letI : IsIntegral
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left := by
    change IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 8).left
    exact
      isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  have hneη : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne
  obtain ⟨R₄, -, hEt, -⟩ :=
    exists_degreeFourResidualDatum_and_toBase_etale_and_disjoint_of_restrictionKernelProperPair
      (p.map a.hom) (hp.map a.hom) hneη Dη hproper
  letI : Etale (R₄.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := hEt
  exact effectiveDegreeFourCycle_of_genericFiniteEtaleResidual
    p hp D₈ a ha R₄

/-- The generic degree-eight specialization with only the genuine geometric
member condition exposed.  Smoothness of the coefficient-changed cubic
proves that the nonzero first quadric in that condition is relatively prime
to the cubic, so relative primality is no longer a premise supplied by the
fixed-component/Bertini argument. -/
theorem effectiveDegreeFourCycle_of_genericDegreeEightRestrictionKernelProperMember
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightQuadraticRestrictionKernelProperMemberExists
          (p.map a.hom) (hp.map a.hom) Dη →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro hmember
  letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite (cubicConfigurationBase p hp 8).functionField :=
    CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 8 a
  have hneη : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne
  apply effectiveDegreeFourCycle_of_genericDegreeEightRestrictionKernelProperPair
    p hp hne D₈ a ha
  exact
    DegreeEightQuadraticRestrictionKernelProperPairExists.of_smooth_cubic
      (p.map a.hom) (hp.map a.hom) hneη
      (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha) hmember

/-- A geometric restatement of the preceding theorem.  It asks directly for
Voisin's no-fixed-component assertion and for the chartwise Jacobian form of
the Bertini assertion; the already formalized selection lemmas convert these
to a regular transverse pair of quadrics. -/
theorem effectiveDegreeFourCycle_of_genericDegreeEightAvoidance_and_chartJacobian
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightSecondQuadricAvoidsAssociatedPrimes
          (p.map a.hom) (hp.map a.hom) Dη →
        CubicTwoQuadricIntersectionChartJacobianUnit
            (p.map a.hom) (hp.map a.hom) →
          ∃ z : EffectiveZeroCycle (hypersurface p hp),
            EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro havoid hjac
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  apply effectiveDegreeFourCycle_of_genericDegreeEightFinrankDrop_and_transverse
    p hp hne D₈ a ha
  · exact havoid.finrankDrop (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 8 a ha)
  · exact hjac.toTransverse (p.map a.hom) (hp.map a.hom)


/-- On Voisin's generic smooth cubic, associated-prime avoidance alone yields
an effective degree-four cycle.  Smoothness makes the cubic equation prime,
so the algebraic first-quadric selection and regular-pair construction need
no additional geometric premise. -/
theorem effectiveDegreeFourCycle_of_genericDegreeEightAvoidance
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 8 D₈
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
      let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
        charZero_cubicConfigurationFunctionField_of_flat p hp 8
      DegreeEightSecondQuadricAvoidsAssociatedPrimes
          (p.map a.hom) (hp.map a.hom) Dη →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 8 D₈
  intro a ha
  dsimp only
  intro havoid
  let B := cubicConfigurationBase p hp 8
  letI : CharZero B.functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite B.functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 8 a
  let Dη := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  have hneη : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 8 a hne
  apply effectiveDegreeFourCycle_of_genericDegreeEightNoCommonCurveComponent
    p hp hne D₈ a ha
  exact
    DegreeEightQuadraticSystemHasNoCommonCurveComponent.of_avoidsAssociatedPrimes_of_smooth_cubic
      (p.map a.hom) (hp.map a.hom) hneη Dη havoid

end PfaffianDescent
