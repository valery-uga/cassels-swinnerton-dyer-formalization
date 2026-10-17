import PfaffianDescent.VoisinGenericSelectedEightIntrinsicIdeal
import PfaffianDescent.VoisinActualCanonicalFiniteFamilySpecialization
import PfaffianDescent.VoisinSmoothGeometricCanonicalFinite

/-!
# The intrinsic generic eight-point presentation on every smooth cubic

This file combines the arbitrary-field common-chart construction with the
actual generic presentation and its intrinsic-ideal comparison.  The result
leaves no chart or coordinate hypothesis in the fixed-cubic Voisin step: the
only remaining geometric assertion is finiteness of the displayed canonical
cubic--two-quadrics intersection.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every nonzero smooth cubic with a finite etale degree-eight datum has a
compatible ordered chart on which the actual generic eight-point
presentation exists and its canonical intrinsic ideal agrees with the ideal
formed from the selected chart coordinates. -/
theorem exists_smoothCubic_actualGenericEightIntrinsicPresentation
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    ∃ w : SmoothCompatibleEightCharts p hp,
      letI : Smooth (hypersurfaceToBase p hp) := w.smooth
      letI : Etale (w.D.val.subschemeι ≫ hypersurfaceToBase p hp) := w.etale
      letI : IsIntegral (cubicConfigurationBase p hp 8) := w.baseIntegral
      letI : IsIntegral w.U := w.integralU
      letI : IsIntegral w.Q := w.integralQ
      letI : IsOpenImmersion w.i := w.openI
      letI : IsOpenImmersion w.j := w.openJ
      letI : Surjective w.r := w.surjectiveR
      ∀ (a : CommRingCat.of K ⟶ CommRingCat.of
          (cubicConfigurationBase p hp 8).functionField)
        (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
        letI : IsSeparated (hypersurfaceToBase p hp) :=
          isSeparated_homogeneousToBase (equationIdeal p hp)
        letI : IsIntegral (projectiveConfigurationQuotientOpen
          (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 8).toScheme :=
          isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
            p hp w.hpne 8 w.D
        letI : IsIntegral (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).left :=
          isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
            p hp w.hpne 8 w.D
        ∃ hz : configurationQuotientMap (equationIdeal p hp) 8
            (w.i (genericPoint w.U)) =
          (cubicConfigurationBase p hp 8).fromSpecStalk
            (genericPoint (cubicConfigurationBase p hp 8))
            (IsLocalRing.closedPoint
              (cubicConfigurationBase p hp 8).functionField),
          ∃ v : ActualGenericEightPresentation p hp a ha w.i hz,
            let Q := cubicConfigurationBase p hp 8
            let O := (orderedFamilyConfigurationOver
              (hypersurfaceToBase p hp) 8).left
            let bCan := quadraticOrderedLiftFunctionFieldHom p hp
              (w.i (genericPoint w.U)) hz
            let bSel : K →+* O.residueField (w.i (genericPoint w.U)) :=
              (Spec.preimage (openImmersion_genericResidueLift w.i ≫ w.i ≫
                (orderedFamilyConfigurationOver
                  (hypersurfaceToBase p hp) 8).hom)).hom
            letI : Algebra Q.functionField
                (O.residueField (w.i (genericPoint w.U))) := bCan.toAlgebra
            letI : Algebra K
                (O.residueField (w.i (genericPoint w.U))) := bSel.toAlgebra
            intrinsicEightPointTripleHomogeneousIdeal
              (p.map bSel) (hp.map bSel)
              (v.canonicalVectors p hp a ha w.i hz) =
            intrinsicEightPointTripleHomogeneousIdeal
              (p.map bSel) (hp.map bSel)
              (v.selectedVectors p hp a ha w.i hz) := by
  obtain ⟨w⟩ := exists_smoothCompatibleEightCharts p hp hpne D
  refine ⟨w, ?_⟩
  letI : Smooth (hypersurfaceToBase p hp) := w.smooth
  letI : Etale (w.D.val.subschemeι ≫ hypersurfaceToBase p hp) := w.etale
  letI : IsIntegral (cubicConfigurationBase p hp 8) := w.baseIntegral
  letI : IsIntegral w.U := w.integralU
  letI : IsIntegral w.Q := w.integralQ
  letI : IsOpenImmersion w.i := w.openI
  letI : IsOpenImmersion w.j := w.openJ
  letI : Surjective w.r := w.surjectiveR
  exact w.exists_intrinsicIdealEquality p hp

/-- The canonical cubic--two-quadrics family is finite at the generic
eight-point configuration of a nonzero smooth cubic.  The selected affine
neighborhood is part of the witness; no degree-eight subscheme over the
ground field is asserted or required here. -/
def SmoothCubicCanonicalGenericEightFinite
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)] : Prop :=
  ∃ d : SelectedActualFiniteNeighborhoodData p hp,
    letI : IsIntegral (cubicConfigurationBase p hp 8) := d.baseIntegral
    letI : IsIntegral d.U := d.integralU
    letI : IsIntegral d.Q := d.integralQ
    letI : IsOpenImmersion d.i := d.openI
    letI : IsOpenImmersion d.j := d.openJ
    letI : Surjective d.s := d.surjectiveS
    letI : IsSeparated (hypersurfaceToBase p hp) :=
      isSeparated_homogeneousToBase (equationIdeal p hp)
    letI : IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme :=
      isIntegral_cubicConfigurationBase_of_smooth p hp hpne
    letI : IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left :=
      isIntegral_orderedCubicConfiguration_of_smooth p hp hpne
    ActualCanonicalFiniteFamily p hp d.i

/-- The residue-field finite specialization constructed from the explicit
smooth-cubic witness proves canonical generic-eight finiteness over the
original ground field. -/
theorem smoothCubicCanonicalGenericEightFinite_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (cubic : Cubic K 4) (hcubic : cubic.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    SmoothCubicCanonicalGenericEightFinite F hF hF0 := by
  simpa only [SmoothCubicCanonicalGenericEightFinite] using
    exists_actualCanonicalFiniteFamily_of_smooth
      F hF hF0 cubic hcubic

/-- Once the canonical generic eight-point triple is finite, the already
checked residual and specialization chain produces an effective degree-four
cycle on the original smooth cubic. -/
theorem SmoothCubicCanonicalGenericEightFinite.exists_effectiveDegreeFourCycle
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (h : SmoothCubicCanonicalGenericEightFinite p hp hpne)
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth p hp hpne
    ∀ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
        cubicConfigurationToBase p hp 8),
      ∃ z : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth p hp hpne
  intro a ha
  obtain ⟨d, hfamily⟩ := h
  letI : IsIntegral (cubicConfigurationBase p hp 8) := d.baseIntegral
  letI : IsIntegral d.U := d.integralU
  letI : IsIntegral d.Q := d.integralQ
  letI : IsOpenImmersion d.i := d.openI
  letI : IsOpenImmersion d.j := d.openJ
  letI : Surjective d.s := d.surjectiveS
  exact exists_effectiveDegreeFourCycle_of_actualCanonicalFiniteFamily
    p hp hpne D₈ d.i hfamily a ha

/-- A finite étale degree-eight subscheme on a nonzero smooth cubic produces
an effective degree-four cycle.  This is the ground-field degree-eight end of
Voisin's argument, with the cubic tensor and generic configuration map both
constructed internally. -/
theorem exists_effectiveDegreeFourCycle_of_smoothCubic_and_etaleDegreeEight
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  obtain ⟨cubic, hcubic⟩ := homogeneous_cubic_has_tensor p hp
  have hfinite : SmoothCubicCanonicalGenericEightFinite p hp hpne :=
    smoothCubicCanonicalGenericEightFinite_of_smooth
      p hp hpne cubic hcubic
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth p hp hpne
  obtain ⟨a, ha⟩ := exists_cubicConfigurationGenericBaseMap p hp 8
  exact hfinite.exists_effectiveDegreeFourCycle p hp hpne D₈ a ha

end PfaffianDescent
