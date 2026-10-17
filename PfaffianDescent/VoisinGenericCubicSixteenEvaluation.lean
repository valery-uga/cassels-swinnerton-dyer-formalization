import PfaffianDescent.VoisinProjectiveLinearSystem
import PfaffianDescent.VoisinGenericQuadraticDetection
import PfaffianDescent.VoisinGenericHomogeneousDetection
import PfaffianDescent.VoisinCubicSixteenFrame
import PfaffianDescent.FiniteSchemeAlgebra
import PfaffianDescent.FiniteSubschemeCompleteIntersection
import PfaffianDescent.ProjectiveChartUniversalIncidence
import PfaffianDescent.HomogeneousFrameCoordinateParameter
import AllCharacteristics.VoisinGenericCubicConfiguration
import AllCharacteristics.ProjectiveConfigurationGenericSplitFiber
import AllCharacteristics.GenericPointDominance

/-!
# Ordered lift of the generic sixteen-point cubic configuration

The generic sixteen-point incidence exclusion is stated on the unordered
configuration quotient. Its ordered lift gives a field-valued evaluation
setting for the source-faithful first residual argument.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The generic unordered length-sixteen configuration admits an ordered lift
over a residue-field extension, and every such chosen lift retains avoidance
of a fixed homogeneous frame of dimension at most sixteen.

This is the carrier-to-field-valued bridge needed to turn the existing
projective-incidence theorem into injectivity of evaluation on a
homogeneous subsystem of dimension at most sixteen. -/
theorem exists_orderedPointOver_genericSixteen_avoids_homogeneousFrameFiniteIncidence
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (hdim : Module.finrank K W ≤ 16)
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme] :
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let Q := (projectiveConfigurationQuotientOpen
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 16).toScheme
    let π := projectiveConfigurationQuotientMap
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 16
    let η := Q.fromSpecStalk (genericPoint Q)
      (IsLocalRing.closedPoint Q.functionField)
    let bad := projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 16).hom
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
      (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal cubic hcubic)) _
        (hypersurfaceToBase cubic hcubic) hsep 16
        (hypersurfaceToAmbient cubic hcubic) i)
      (homogeneousFrameToParameters d e q hqliq)
    ∃ z : O, π z = η ∧ z ∉ bad := by
  dsimp only
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 16).left
  let Q := (projectiveConfigurationQuotientOpen
    (grading (equationIdeal cubic hcubic))
    (hypersurfaceToBase cubic hcubic) 16).toScheme
  let π := projectiveConfigurationQuotientMap
    (grading (equationIdeal cubic hcubic))
    (hypersurfaceToBase cubic hcubic) 16
  let η := Q.fromSpecStalk (genericPoint Q)
    (IsLocalRing.closedPoint Q.functionField)
  let bad := projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
    (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).hom
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal cubic hcubic)) _
      (hypersurfaceToBase cubic hcubic) hsep 16
      (hypersurfaceToAmbient cubic hcubic) i)
    (homogeneousFrameToParameters d e q hqliq)
  have hav : η ∉ π '' bad := by
    exact
      genericFunctionField_closedPoint_avoids_sixteen_cubicConfigurationQuotientHomogeneousFrameFiniteIncidence_of_submodule_evaluation
        cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate hdim
          qW q hq hqli hqliq hn e
  letI : Surjective π := by
    dsimp only [π]
    exact surjective_projectiveConfigurationQuotientMap
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 16
  obtain ⟨z, hz⟩ := π.surjective η
  refine ⟨z, hz, ?_⟩
  intro hr
  apply hav
  exact ⟨z, hr, hz⟩


/-- The residue field of an ordered lift over the generic unordered
configuration receives the configuration function field. -/
noncomputable def cubicSixteenOrderedLiftFunctionFieldHom
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField)) :
    (projectiveConfigurationQuotientOpen
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField →+*
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 16).left.residueField z := by
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 16).left
  let Q := (projectiveConfigurationQuotientOpen
    (grading (equationIdeal cubic hcubic))
    (hypersurfaceToBase cubic hcubic) 16).toScheme
  let π := projectiveConfigurationQuotientMap
    (grading (equationIdeal cubic hcubic))
    (hypersurfaceToBase cubic hcubic) 16
  let r := O.fromSpecResidueField z
  have hc : (r ≫ π) (IsLocalRing.closedPoint (O.residueField z)) =
      genericPoint Q := by
    change π (r (IsLocalRing.closedPoint (O.residueField z))) = genericPoint Q
    have hr : r (IsLocalRing.closedPoint (O.residueField z)) = z := by
      exact Scheme.fromSpecResidueField_apply z _
    exact (congrArg π hr).trans (hz.trans Scheme.fromSpecStalk_closedPoint)
  exact Q.genericFieldPointRingHom (r ≫ π) hc

/-- The induced function-field homomorphism factors the ordered residue point
through the canonical generic-point morphism. -/
lemma cubicSixteenOrderedLiftFunctionFieldHom_spec
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField)) :
    Spec.map (CommRingCat.ofHom
        (cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz)) ≫
      (projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme) =
      (orderedFamilyConfigurationOver
          (hypersurfaceToBase cubic hcubic) 16).left.fromSpecResidueField z ≫
        projectiveConfigurationQuotientMap
          (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 16 := by
  unfold cubicSixteenOrderedLiftFunctionFieldHom
  apply Scheme.genericFieldPointRingHom_spec

/-- The `i`th label of an ordered generic lift gives a point of the actual
generic rank-sixteen finite scheme over the ordered residue field. -/
noncomputable def cubicSixteenOrderedLiftComponentPoint
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    (i : Fin 16) :
    Spec (.of ((orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left.residueField z)) ⟶
      (projectiveConfigurationGenericFiniteSubscheme
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).val.subscheme := by
  letI : IsSeparated
      (show Proj (grading (equationIdeal cubic hcubic)) ⟶ Spec (.of K) from
        toBase (equationIdeal cubic hcubic)) := hsep
  letI : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (toBase (equationIdeal cubic hcubic)) 16).toScheme := hint
  exact projectiveConfigurationOrderedGenericComponentPoint
    (grading (equationIdeal cubic hcubic))
    (toBase (equationIdeal cubic hcubic)) 16
    ((orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left.fromSpecResidueField z)
    (cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz)
    (cubicSixteenOrderedLiftFunctionFieldHom_spec cubic hcubic z hz) i


/-- The actual generic finite-scheme component has the ambient projective
point prescribed by its label in the ordered configuration. -/
lemma cubicSixteenOrderedLiftComponentPoint_toAmbientProjective
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    (i : Fin 16) :
    cubicSixteenOrderedLiftComponentPoint cubic hcubic z hz i ≫
      cubicConfigurationGenericAmbientMap cubic hcubic 16 =
    (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 16).left.fromSpecResidueField z ≫
      @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal cubic hcubic)) _
        (hypersurfaceToBase cubic hcubic) hsep 16
        (hypersurfaceToAmbient cubic hcubic) i := by
  letI : IsSeparated
      (show Proj (grading (equationIdeal cubic hcubic)) ⟶ Spec (.of K) from
        toBase (equationIdeal cubic hcubic)) := hsep
  letI : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (toBase (equationIdeal cubic hcubic)) 16).toScheme := hint
  have hpoint := projectiveConfigurationOrderedGenericComponentPoint_toAmbientProjective
    (grading (equationIdeal cubic hcubic)) (toBase (equationIdeal cubic hcubic)) 16
    ((orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left.fromSpecResidueField z)
    (cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz)
    (cubicSixteenOrderedLiftFunctionFieldHom_spec cubic hcubic z hz) i
  have hpoint' := congrArg
    (fun t ↦ t ≫ hypersurfaceToAmbient cubic hcubic) hpoint
  unfold cubicSixteenOrderedLiftComponentPoint
  exact hpoint'


/-- The labeled component point transported to the coefficient-changed
generic cubic used by the residual construction.  Its source field is the
same ordered residue field, while its target is now the finite subscheme on
the literal coefficient-changed cubic equation. -/
noncomputable def cubicSixteenOrderedLiftCoefficientChangedComponentPoint
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
        cubicConfigurationToBase cubic hcubic 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    (i : Fin 16) :
    Spec (.of ((orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left.residueField z)) ⟶
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 16 a ha).val.subscheme :=
  cubicSixteenOrderedLiftComponentPoint cubic hcubic z hz i ≫
    (cubicConfigurationGenericFiniteSubschemeIsoGeneric
      cubic hcubic 16 a ha).inv

/-- Transporting a labeled component to the coefficient-changed cubic does
not alter its morphism to the original ambient projective space. -/
lemma cubicSixteenOrderedLiftCoefficientChangedComponentPoint_toGenericAmbient
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
        cubicConfigurationToBase cubic hcubic 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    (i : Fin 16) :
    cubicSixteenOrderedLiftCoefficientChangedComponentPoint
        cubic hcubic a ha z hz i ≫
      cubicConfigurationCoefficientChangedAmbientMap cubic hcubic 16 a ha =
    cubicSixteenOrderedLiftComponentPoint cubic hcubic z hz i ≫
      cubicConfigurationGenericAmbientMap cubic hcubic 16 := by
  have hambient :=
    @cubicConfigurationGenericFiniteSubschemeIsoGeneric_inv_ambientMap
      K _ cubic 3 hcubic 16 hbase hsep a ha
  unfold cubicSixteenOrderedLiftCoefficientChangedComponentPoint
  calc
    (cubicSixteenOrderedLiftComponentPoint cubic hcubic z hz i ≫
          (cubicConfigurationGenericFiniteSubschemeIsoGeneric
            cubic hcubic 16 a ha).inv) ≫
        cubicConfigurationCoefficientChangedAmbientMap cubic hcubic 16 a ha =
      cubicSixteenOrderedLiftComponentPoint cubic hcubic z hz i ≫
        ((cubicConfigurationGenericFiniteSubschemeIsoGeneric
            cubic hcubic 16 a ha).inv ≫
          cubicConfigurationCoefficientChangedAmbientMap
            cubic hcubic 16 a ha) :=
      Category.assoc _ _ _
    _ = _ := congrArg
      (fun t ↦ cubicSixteenOrderedLiftComponentPoint cubic hcubic z hz i ≫ t)
      hambient

/-- The transported component on the literal coefficient-changed cubic is
the marked ambient projective point of the ordered generic configuration. -/
lemma cubicSixteenOrderedLiftCoefficientChangedComponentPoint_toAmbientProjective
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
        cubicConfigurationToBase cubic hcubic 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    (i : Fin 16) :
    cubicSixteenOrderedLiftCoefficientChangedComponentPoint
        cubic hcubic a ha z hz i ≫
      cubicConfigurationCoefficientChangedAmbientMap cubic hcubic 16 a ha =
    (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 16).left.fromSpecResidueField z ≫
      @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal cubic hcubic)) _
        (hypersurfaceToBase cubic hcubic) hsep 16
        (hypersurfaceToAmbient cubic hcubic) i := by
  calc
    _ = cubicSixteenOrderedLiftComponentPoint cubic hcubic z hz i ≫
        cubicConfigurationGenericAmbientMap cubic hcubic 16 :=
      cubicSixteenOrderedLiftCoefficientChangedComponentPoint_toGenericAmbient
        cubic hcubic a ha z hz i
    _ = _ := cubicSixteenOrderedLiftComponentPoint_toAmbientProjective
      cubic hcubic z hz i

/-- Each labeled component point lies over the function-field embedding
associated to the ordered lift. -/
lemma cubicSixteenOrderedLiftComponentPoint_toBase
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    (i : Fin 16) :
    cubicSixteenOrderedLiftComponentPoint cubic hcubic z hz i ≫
        (projectiveConfigurationGenericFiniteSubscheme
          (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 16).val.subschemeι ≫
        pullback.snd
          (pullback.snd (hypersurfaceToBase cubic hcubic)
            (projectiveConfigurationQuotientToBase
              (grading (equationIdeal cubic hcubic))
              (hypersurfaceToBase cubic hcubic) 16))
          ((projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
              (genericPoint (projectiveConfigurationQuotientOpen
                (grading (equationIdeal cubic hcubic))
                (hypersurfaceToBase cubic hcubic) 16).toScheme)) =
      Spec.map (CommRingCat.ofHom
        (cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz)) := by
  letI : IsSeparated
      (show Proj (grading (equationIdeal cubic hcubic)) ⟶ Spec (.of K) from
        toBase (equationIdeal cubic hcubic)) := hsep
  letI : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (toBase (equationIdeal cubic hcubic)) 16).toScheme := hint
  unfold cubicSixteenOrderedLiftComponentPoint
  exact projectiveConfigurationOrderedGenericComponentPoint_toBase
    (grading (equationIdeal cubic hcubic))
    (toBase (equationIdeal cubic hcubic)) 16
    ((orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left.fromSpecResidueField z)
    (cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz)
    (cubicSixteenOrderedLiftFunctionFieldHom_spec cubic hcubic z hz) i

/-- A labeled component transported to the coefficient-changed cubic remains
over the same configuration-function-field embedding. -/
lemma cubicSixteenOrderedLiftCoefficientChangedComponentPoint_toBase
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
        cubicConfigurationToBase cubic hcubic 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    (i : Fin 16) :
    cubicSixteenOrderedLiftCoefficientChangedComponentPoint
        cubic hcubic a ha z hz i ≫
      cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha =
    Spec.map (CommRingCat.ofHom
      (cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz)) := by
  have htransport :=
    @cubicConfigurationGenericFiniteSubschemeIsoGeneric_inv_toBase
      K _ cubic 3 hcubic 16 hbase hsep a ha
  have hpoint := cubicSixteenOrderedLiftComponentPoint_toBase
    cubic hcubic z hz i
  have hpoint' :
      cubicSixteenOrderedLiftComponentPoint cubic hcubic z hz i ≫
        cubicConfigurationGenericFiniteBaseMap cubic hcubic 16 =
      Spec.map (CommRingCat.ofHom
        (cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz)) := hpoint
  unfold cubicSixteenOrderedLiftCoefficientChangedComponentPoint
  have htransported :
      (cubicSixteenOrderedLiftComponentPoint cubic hcubic z hz i ≫
          (cubicConfigurationGenericFiniteSubschemeIsoGeneric
            cubic hcubic 16 a ha).inv) ≫
        cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha =
      cubicSixteenOrderedLiftComponentPoint cubic hcubic z hz i ≫
        cubicConfigurationGenericFiniteBaseMap cubic hcubic 16 := by
    calc
      (cubicSixteenOrderedLiftComponentPoint cubic hcubic z hz i ≫
            (cubicConfigurationGenericFiniteSubschemeIsoGeneric
              cubic hcubic 16 a ha).inv) ≫
          cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha =
        cubicSixteenOrderedLiftComponentPoint cubic hcubic z hz i ≫
          ((cubicConfigurationGenericFiniteSubschemeIsoGeneric
              cubic hcubic 16 a ha).inv ≫
            cubicConfigurationCoefficientChangedBaseMap
              cubic hcubic 16 a ha) := Category.assoc _ _ _
      _ = _ := congrArg
        (fun t ↦ cubicSixteenOrderedLiftComponentPoint cubic hcubic z hz i ≫ t)
        htransport
  exact htransported.trans hpoint'


/-- Pullback of global functions along the `i`th labeled component gives an
algebra embedding candidate from the generic rank-sixteen coordinate algebra
to the ordered lift's residue field. -/
noncomputable def cubicSixteenOrderedLiftComponentAlgHom
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    (i : Fin 16) :
    let f := toBase (equationIdeal cubic hcubic)
    letI : IsSeparated f := hsep
    let Q := (projectiveConfigurationQuotientOpen
      (grading (equationIdeal cubic hcubic)) f 16).toScheme
    letI : IsIntegral Q := hint
    let O := (orderedFamilyConfigurationOver f 16).left
    let D := projectiveConfigurationGenericFiniteSubscheme
      (grading (equationIdeal cubic hcubic)) f 16
    let pD := D.val.subschemeι ≫
      pullback.snd
        (pullback.snd f (projectiveConfigurationQuotientToBase
          (grading (equationIdeal cubic hcubic)) f 16))
        (Q.fromSpecStalk (genericPoint Q))
    let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z := by
  dsimp only
  letI : IsSeparated
      (show Proj (grading (equationIdeal cubic hcubic)) ⟶ Spec (.of K) from
        toBase (equationIdeal cubic hcubic)) := hsep
  letI : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (toBase (equationIdeal cubic hcubic)) 16).toScheme := hint
  let f := toBase (equationIdeal cubic hcubic)
  let Q := (projectiveConfigurationQuotientOpen
    (grading (equationIdeal cubic hcubic)) f 16).toScheme
  let O := (orderedFamilyConfigurationOver f 16).left
  let D := projectiveConfigurationGenericFiniteSubscheme
    (grading (equationIdeal cubic hcubic)) f 16
  let pD := D.val.subschemeι ≫
    pullback.snd
      (pullback.snd f (projectiveConfigurationQuotientToBase
        (grading (equationIdeal cubic hcubic)) f 16))
      (Q.fromSpecStalk (genericPoint Q))
  let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  exact finiteSchemePointAlgHom pD
    (cubicSixteenOrderedLiftComponentPoint cubic hcubic z hz i) b
    (cubicSixteenOrderedLiftComponentPoint_toBase cubic hcubic z hz i)

/-- Pullback of global functions along the transported labeled component,
now on the literal coefficient-changed cubic. -/
noncomputable def cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
        cubicConfigurationToBase cubic hcubic 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    (i : Fin 16) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap
      cubic hcubic 16 a ha
    let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 16).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  exact finiteSchemePointAlgHom pD
    (cubicSixteenOrderedLiftCoefficientChangedComponentPoint
      cubic hcubic a ha z hz i) b
    (cubicSixteenOrderedLiftCoefficientChangedComponentPoint_toBase
      cubic hcubic a ha z hz i)

/-- The algebra map of a transported labeled component recovers that
component after the canonical affine presentation and any later morphism. -/
lemma cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom_spec_comp
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
        cubicConfigurationToBase cubic hcubic 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    (i : Fin 16) {Y : Scheme.{u}}
    (j : (cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 16 a ha).val.subscheme ⟶ Y) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap
      cubic hcubic 16 a ha
    let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    Spec.map (CommRingCat.ofHom
        (cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
          cubic hcubic a ha z hz i).toRingHom) ≫
      D.val.subscheme.isoSpec.inv ≫ j =
    cubicSixteenOrderedLiftCoefficientChangedComponentPoint
      cubic hcubic a ha z hz i ≫ j := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 16).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  unfold cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
  exact finiteSchemePointAlgHom_spec_comp pD
    (cubicSixteenOrderedLiftCoefficientChangedComponentPoint
      cubic hcubic a ha z hz i) b
    (cubicSixteenOrderedLiftCoefficientChangedComponentPoint_toBase
      cubic hcubic a ha z hz i) j

/-- Any affine presentation of the transported finite scheme that recovers
its ambient immersion evaluates a labeled component at the corresponding
ordered marked projective point. -/
lemma cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom_chart_toMarkedPoint
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
        cubicConfigurationToBase cubic hcubic 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    (i : Fin 16)
    (c : Spec (.of Γ((cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 16 a ha).val.subscheme, ⊤)) ⟶
        Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let p' := cubic.map a.hom
    let hp' := hcubic.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap
      cubic hcubic 16 a ha
    let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    c = D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
          hypersurfaceToAmbient p' hp' ≫ ambientCoefficientMap a.hom →
      Spec.map (CommRingCat.ofHom
          (cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
            cubic hcubic a ha z hz i).toRingHom) ≫ c =
        (orderedFamilyConfigurationOver
            (hypersurfaceToBase cubic hcubic) 16).left.fromSpecResidueField z ≫
          @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal cubic hcubic)) _
            (hypersurfaceToBase cubic hcubic) hsep 16
            (hypersurfaceToAmbient cubic hcubic) i := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 16).left
  let p' := cubic.map a.hom
  let hp' := hcubic.map a.hom
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  intro hc
  let j := D.val.subschemeι ≫ hypersurfaceToAmbient p' hp' ≫
    ambientCoefficientMap a.hom
  have hrecover := finiteSchemePointAlgHom_spec_comp_of_eq pD
    (cubicSixteenOrderedLiftCoefficientChangedComponentPoint
      cubic hcubic a ha z hz i) b
    (cubicSixteenOrderedLiftCoefficientChangedComponentPoint_toBase
      cubic hcubic a ha z hz i) j c hc
  have hmarked :=
    cubicSixteenOrderedLiftCoefficientChangedComponentPoint_toAmbientProjective
      cubic hcubic a ha z hz i
  exact hrecover.trans hmarked


/-- The coefficient-changed generic rank-sixteen datum admits a normalized
projective chart retaining its actual immersion into the cubic. -/
theorem exists_cubicConfigurationGenericSixteen_normalizedChart
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [hinfinite : Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
        cubicConfigurationToBase cubic hcubic 16) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let p' := cubic.map a.hom
    let hp' := hcubic.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap
      cubic hcubic 16 a ha
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    ∃ (w : CoordinateRing (equationIdeal p' hp'))
      (hw : w ∈ grading (equationIdeal p' hp') 1)
      (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (he : ∀ q ∈ (equationIdeal p' hp').toIdeal,
        (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) q = 0)
      (hwOne : (Ideal.Quotient.lift (equationIdeal p' hp').toIdeal
        (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) he) w = 1),
      Function.Surjective
          (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) ∧
      p'.eval₂ (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x = 0 ∧
      linearNormalizedPointAt (equationIdeal p' hp') x he w hw hwOne =
        D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι := by
  dsimp only
  let p' := cubic.map a.hom
  let hp' := hcubic.map a.hom
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  letI : IsFinite pD := D.property.1
  letI : IsFinite
      (D.val.subschemeι ≫ hypersurfaceToBase p' hp') := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  exact cubicFiniteSubscheme_normalized_chart p' hp' D.val.subschemeι


/-- A normalized ambient chart on the coefficient-changed generic scheme
evaluates under every labeled component map at the corresponding ordered
marked point. -/
theorem cubicSixteenOrderedLift_normalizedAmbientChart_toMarkedPoint
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField)) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let p' := cubic.map a.hom
    let hp' := hcubic.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    ∀ (ell : MvPolynomial (Fin 4) Q.functionField)
      (hell : ell.IsHomogeneous 1)
      (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (he : ∀ q ∈ (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal,
        (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) q = 0)
      (hellOne : (Ideal.Quotient.lift
        (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal
        (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) he)
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal ell) = 1),
      linearNormalizedPointAt
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q.functionField))
          x he
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal ell)
          (polynomial_class_mem_grading
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField)) ell hell)
          hellOne ≫
        quotientProjMap
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q.functionField)) =
        D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
          hypersurfaceToAmbient p' hp' →
      ∀ i,
        Spec.map (CommRingCat.ofHom
            (cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
              cubic hcubic a ha z hz i).toRingHom) ≫
          linearNormalizedPointAt
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField))
            x he
            (Ideal.Quotient.mk
              (⊥ : HomogeneousIdeal
                (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal ell)
            (polynomial_class_mem_grading
              (⊥ : HomogeneousIdeal
                (homogeneousSubmodule (Fin 4) Q.functionField)) ell hell)
            hellOne ≫
          quotientProjMap
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField)) ≫
          ambientCoefficientMap a.hom =
        O.fromSpecResidueField z ≫
          @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal cubic hcubic)) _
            (hypersurfaceToBase cubic hcubic) hsep 16
            (hypersurfaceToAmbient cubic hcubic) i := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let p' := cubic.map a.hom
  let hp' := hcubic.map a.hom
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField
      ((orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 16).left.residueField z) := b.toAlgebra
  intro ell hell x he hellOne hpoint i
  let c := linearNormalizedPointAt
      (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) Q.functionField))
      x he
      (Ideal.Quotient.mk
        (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal ell)
      (polynomial_class_mem_grading
        (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) Q.functionField)) ell hell)
      hellOne ≫
    quotientProjMap
      (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) Q.functionField)) ≫
    ambientCoefficientMap a.hom
  have hc : c = D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
      hypersurfaceToAmbient p' hp' ≫ ambientCoefficientMap a.hom := by
    exact (congrArg (fun k => k ≫ ambientCoefficientMap a.hom) hpoint).trans
      (Category.assoc _ _ _)
  exact cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom_chart_toMarkedPoint
    cubic hcubic a ha z hz i c hc

/-- A fixed homogeneous frame of dimension at most sixteen has no common
residue-field equation at a chosen ordered lift of the generic sixteen-point
configuration. -/
theorem exists_orderedPointOver_genericSixteen_with_noCommonFrameEquation
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (hdim : Module.finrank K W ≤ 16)
    (qW : Fin n → W) (frame : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (frame j).1)
    (hqli : LinearIndependent K qW) (hframe : LinearIndependent K frame)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme] :
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let Q := (projectiveConfigurationQuotientOpen
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 16).toScheme
    let π := projectiveConfigurationQuotientMap
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 16
    let η := Q.fromSpecStalk (genericPoint Q)
      (IsLocalRing.closedPoint Q.functionField)
    ∃ z : O, π z = η ∧
      HomogeneousSixteenNoCommonResidueFieldEquationAt
        cubic hcubic e frame hframe z := by
  dsimp only
  obtain ⟨z, hzπ, hzbad⟩ :=
    exists_orderedPointOver_genericSixteen_avoids_homogeneousFrameFiniteIncidence
      cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate hdim
      qW frame hq hqli hframe hn e
  refine ⟨z, hzπ, ?_⟩
  unfold HomogeneousSixteenNoCommonResidueFieldEquationAt
  dsimp only
  exact
    not_exists_common_residueFieldPoints_of_not_mem_projectiveUniversalFiniteIncidenceBadLocus
      K (Fin 4) d
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 16).hom
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
      (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal cubic hcubic)) _
        (hypersurfaceToBase cubic hcubic) hsep 16
        (hypersurfaceToAmbient cubic hcubic) i)
      (homogeneousFrameToParameters d e frame hframe) hzbad

/-- On a normalized ambient chart of the generic rank-sixteen scheme,
the ordered incidence-avoidance hypothesis detects every coefficient vector
in the chosen homogeneous frame. -/
theorem cubicSixteenOrderedLift_normalizedAmbientChart_detectsFrame
    {K : Type u} [Field K]
    {d n m : ℕ}
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    (e : Fin m ≃ Monomials (Fin 4) d)
    (frame : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hframe : LinearIndependent K frame)
    (hno : HomogeneousSixteenNoCommonResidueFieldEquationAt cubic hcubic e frame hframe z) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let p' := cubic.map a.hom
    let hp' := hcubic.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    let φ : Fin 16 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
      fun i => cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i
    ∀ (ell : MvPolynomial (Fin 4) Q.functionField)
      (hell : ell.IsHomogeneous 1)
      (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (he : ∀ q ∈ (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal,
        (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) q = 0)
      (hellOne : (Ideal.Quotient.lift
        (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal
        (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) he)
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal ell) = 1),
      linearNormalizedPointAt
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q.functionField))
          x he
          (Ideal.Quotient.mk
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField)).toIdeal ell)
          (polynomial_class_mem_grading
            (⊥ : HomogeneousIdeal
              (homogeneousSubmodule (Fin 4) Q.functionField)) ell hell)
          hellOne ≫
        quotientProjMap
          (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin 4) Q.functionField)) =
        D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
          hypersurfaceToAmbient p' hp' →
      ∀ c : Fin n → Q.functionField,
        (∀ i, MvPolynomial.eval₂
          (algebraMap Q.functionField (O.residueField z))
          (fun j => φ i (x j))
          (∑ j, MvPolynomial.C (c j) * (frame j).1.map a.hom) = 0) →
        c = 0 := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 16).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  let φ : Fin 16 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
    fun i => cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
      cubic hcubic a ha z hz i
  intro ell hell x he hellOne hpoint
  let r := O.fromSpecResidueField z
  let marked : Fin 16 →
      (O ⟶ Proj (homogeneousSubmodule (Fin 4) K)) := fun i =>
    @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal cubic hcubic)) _
      (hypersurfaceToBase cubic hcubic) hsep 16
      (hypersurfaceToAmbient cubic hcubic) i
  have hrBase : r ≫ (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 16).hom =
      Spec.map (CommRingCat.ofHom (b.comp a.hom)) := by
    let f : Proj (grading (equationIdeal cubic hcubic)) ⟶ Spec (.of K) :=
      toBase (equationIdeal cubic hcubic)
    letI : IsSeparated f := hsep
    letI : IsIntegral
        (projectiveConfigurationQuotientOpen
          (grading (equationIdeal cubic hcubic)) f 16).toScheme := hint
    have ha' : Spec.map a =
        (projectiveConfigurationQuotientOpen
          (grading (equationIdeal cubic hcubic)) f 16).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen
              (grading (equationIdeal cubic hcubic)) f 16).toScheme) ≫
          projectiveConfigurationQuotientToBase
            (grading (equationIdeal cubic hcubic)) f 16 := by
      exact ha
    have hb' : Spec.map (CommRingCat.ofHom b) ≫
        (projectiveConfigurationQuotientOpen
          (grading (equationIdeal cubic hcubic)) f 16).toScheme.fromSpecStalk
            (genericPoint (projectiveConfigurationQuotientOpen
              (grading (equationIdeal cubic hcubic)) f 16).toScheme) =
        (orderedFamilyConfigurationOver f 16).left.fromSpecResidueField z ≫
          projectiveConfigurationQuotientMap
            (grading (equationIdeal cubic hcubic)) f 16 := by
      exact cubicSixteenOrderedLiftFunctionFieldHom_spec cubic hcubic z hz
    exact @projectiveConfigurationOrderedLift_toBase
      K (CoordinateRing (equationIdeal cubic hcubic)) _ _ _
      (grading (equationIdeal cubic hcubic)) _
      f 16 hsep hint a ha' z b hb'
  have hmarked := cubicSixteenOrderedLift_normalizedAmbientChart_toMarkedPoint
    cubic hcubic a ha z hz ell hell x he hellOne hpoint
  apply homogeneousFrame_detected_of_noCommonIncidence_sixteen
    a.hom b rfl e frame hframe
    (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).hom
    marked r hrBase x he ell hell hellOne φ hmarked
  exact hno

/-- A nonzero prime cubic has a sixteen-dimensional cubic subsystem whose
ordered generic marked points admit no common residue-field equation.  The
frame is constructed from the nineteen-dimensional cubic coordinate-ring
piece, so no frame-separation hypothesis remains in this statement. -/
theorem exists_orderedPointOver_genericSixteen_with_noCommonCubicEquation
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {m : ℕ} (e : Fin m ≃ Monomials (Fin 4) 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme] :
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let Q := (projectiveConfigurationQuotientOpen
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 16).toScheme
    let π := projectiveConfigurationQuotientMap
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 16
    let η := Q.fromSpecStalk (genericPoint Q)
      (IsLocalRing.closedPoint Q.functionField)
    ∃ (frame : Fin 16 → homogeneousSubmodule (Fin 4) K 3)
      (hframe : LinearIndependent K frame) (z : O),
      π z = η ∧
      HomogeneousSixteenNoCommonResidueFieldEquationAt
        cubic hcubic e frame hframe z := by
  dsimp only
  obtain ⟨frame, hframe, hdim, hhom, hseparate⟩ :=
    exists_cubicSixteenFrame_separated_submodule cubic hcubic hcubic_ne
  let W := Submodule.span K (Set.range (fun i => (frame i).1))
  letI : FiniteDimensional K W :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  let frameW : Fin 16 → W := fun i =>
    ⟨(frame i).1, Submodule.subset_span ⟨i, rfl⟩⟩
  have hpoly : LinearIndependent K (fun i => (frame i).1) := by
    exact hframe.map' (homogeneousSubmodule (Fin 4) K 3).subtype
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hframeW : LinearIndependent K frameW := by
    exact hpoly.of_comp W.subtype
  obtain ⟨z, hz, hno⟩ :=
    exists_orderedPointOver_genericSixteen_with_noCommonFrameEquation
      cubic hcubic hcubic_ne hcubic_prime (by decide) W hhom hseparate
      (le_of_eq hdim)
      frameW frame (fun _ => rfl) hframeW hframe hdim e
  exact ⟨frame, hframe, z, hz, hno⟩

/-- The generic rank-sixteen subscheme has normalized coordinates in which
its sixteen labeled residue-field evaluations detect a cubic frame. -/
theorem exists_cubicConfigurationGenericSixteen_detectingCubicFrameCoordinates_of_noCommon
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    {m : ℕ} (e : Fin m ≃ Monomials (Fin 4) 3)
    (frame : Fin 16 → homogeneousSubmodule (Fin 4) K 3)
    (hframe : LinearIndependent K frame)
    (hno : HomogeneousSixteenNoCommonResidueFieldEquationAt
      cubic hcubic e frame hframe z) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    let φ : Fin 16 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
      fun i => cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i
    Nonempty (DetectingCubicSixteenFrameCoordinates
      Q.functionField Γ(D.val.subscheme, ⊤) (O.residueField z)
      φ (fun j => (frame j).1.map a.hom)) := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 16).left
  let p' := cubic.map a.hom
  let hp' := hcubic.map a.hom
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p' hp') := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  obtain ⟨ell, hell, x, he, hellOne, hxsurj, _, hpoint⟩ :=
    cubicFiniteSubscheme_normalized_ambient_chart p' hp' D.val.subschemeι
  refine ⟨{
    x := x
    evalSurjective := hxsurj
    detects := ?_ }⟩
  exact cubicSixteenOrderedLift_normalizedAmbientChart_detectsFrame
    cubic hcubic a ha z hz e frame hframe hno
      ell hell x he hellOne hpoint

/-- The generic rank-sixteen scheme has detecting normalized coordinates
that satisfy its cubic equation. -/
theorem exists_cubicConfigurationGenericSixteen_detectingCubicFrameCoordinatesOnCubic_of_noCommon
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    {m : ℕ} (e : Fin m ≃ Monomials (Fin 4) 3)
    (frame : Fin 16 → homogeneousSubmodule (Fin 4) K 3)
    (hframe : LinearIndependent K frame)
    (hno : HomogeneousSixteenNoCommonResidueFieldEquationAt
      cubic hcubic e frame hframe z) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    let φ : Fin 16 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
      fun i => cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i
    Nonempty (DetectingCubicSixteenFrameCoordinatesOnCubic
      Q.functionField Γ(D.val.subscheme, ⊤) (O.residueField z)
      (cubic.map a.hom) φ (fun j => (frame j).1.map a.hom)) := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 16).left
  let p' := cubic.map a.hom
  let hp' := hcubic.map a.hom
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p' hp') := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  obtain ⟨ell, hell, x, he, hellOne, hxsurj, hpx, hpoint⟩ :=
    cubicFiniteSubscheme_normalized_ambient_chart p' hp' D.val.subschemeι
  refine ⟨{
    data := {
      x := x
      evalSurjective := hxsurj
      detects := ?_ },
    cubicZero := hpx }⟩
  exact cubicSixteenOrderedLift_normalizedAmbientChart_detectsFrame
    cubic hcubic a ha z hz e frame hframe hno
      ell hell x he hellOne hpoint

end PfaffianDescent
