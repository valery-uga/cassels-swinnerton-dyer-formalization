import PfaffianDescent.VoisinSmoothResidueFiniteNeighborhood
import PfaffianDescent.VoisinSelectedFiniteActualPresentation
import PfaffianDescent.VoisinCanonicalFiniteFamilyDegreeFour

/-!
# Canonical generic-eight finiteness from the geometric selected witness

The selected finite neighborhood constructed from the arbitrary quadratic
pair is converted to the actual canonical finite-family interface.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem SelectedActualFiniteNeighborhoodData.actualCanonicalFiniteFamily
    {L : Type u} [Field L] [CharZero L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (d : SelectedActualFiniteNeighborhoodData p hp) :
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
      isIntegral_cubicConfigurationBase_of_smooth p hp hp0
    letI : IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left :=
      isIntegral_orderedCubicConfiguration_of_smooth p hp hp0
    ActualCanonicalFiniteFamily p hp d.i := by
  rcases d with ⟨hInt, U, Q, hU, hQ, i, j, s, hi, hj, hsurjs,
    hcomm, c, m, t, x, hx, ht, hdet, V, hV, hfin⟩
  subst x
  dsimp only
  letI : IsIntegral (cubicConfigurationBase p hp 8) := hInt
  letI : IsIntegral U := hU
  letI : IsIntegral Q := hQ
  letI : IsOpenImmersion i := hi
  letI : IsOpenImmersion j := hj
  letI : Surjective s := hsurjs
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  letI : IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme :=
    isIntegral_cubicConfigurationBase_of_smooth p hp hp0
  letI : IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left :=
    isIntegral_orderedCubicConfiguration_of_smooth p hp hp0
  intro a ha
  let hz := selectedOrderedChart_genericPoint_over_cubicGenericBase
    p hp i j s hcomm
  have hgood : ∃ w : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left,
      w ∉ quadraticEightFixedFrameBadLocus p hp :=
    exists_smoothCubic_orderedEight_goodPoint p hp hp0
  have hno : QuadraticEightNoCommonResidueFieldEquationAt
      p hp (i (genericPoint U)) :=
    quadraticEightNoCommon_at_every_generic_ordered_lift_of_goodPoint
      p hp hgood (i (genericPoint U)) hz
  have hres := exists_actualCanonicalIntrinsicFinite_of_selectedFiniteNeighborhood
    p hp hp0 a ha i j s hcomm
    (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
    t ht hno m
  exact hres hdet V hV hfin

/-- Every nonzero smooth cubic has a selected neighborhood over its original
ground field on which the actual canonical generic eight-point family is
finite.  The algebraic-closure witness is used only to find a residue-field
specialization; `nonempty_selectedActualFiniteNeighborhoodData_of_residue`
spreads that specialization back over the original configuration space. -/
theorem exists_actualCanonicalFiniteFamily_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (cubic : Cubic K 4) (hcubic : cubic.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    ∃ (d : SelectedActualFiniteNeighborhoodData F hF),
      letI : IsIntegral (cubicConfigurationBase F hF 8) := d.baseIntegral
      letI : IsIntegral d.U := d.integralU
      letI : IsIntegral d.Q := d.integralQ
      letI : IsOpenImmersion d.i := d.openI
      letI : IsOpenImmersion d.j := d.openJ
      letI : Surjective d.s := d.surjectiveS
      letI : IsSeparated (hypersurfaceToBase F hF) :=
        isSeparated_homogeneousToBase (equationIdeal F hF)
      letI : IsIntegral (projectiveConfigurationQuotientOpen
        (grading (equationIdeal F hF))
        (hypersurfaceToBase F hF) 8).toScheme :=
        isIntegral_cubicConfigurationBase_of_smooth F hF hF0
      letI : IsIntegral (orderedFamilyConfigurationOver
        (hypersurfaceToBase F hF) 8).left :=
        isIntegral_orderedCubicConfiguration_of_smooth F hF hF0
      ActualCanonicalFiniteFamily F hF d.i := by
  obtain ⟨z, hz⟩ :=
    exists_smoothCubic_residueSelectedPairFinite F hF hF0 cubic hcubic
  obtain ⟨d⟩ :=
    nonempty_selectedActualFiniteNeighborhoodData_of_residue F hF hF0 z hz
  exact ⟨d, d.actualCanonicalFiniteFamily F hF hF0⟩

/-- Over the algebraic closure, every nonzero smooth cubic has an actual
canonical finite family at the generic eight-point configuration. -/
theorem exists_geometric_actualCanonicalFiniteFamily_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (cubic : Cubic K 4) (hcubic : cubic.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    let L := AlgebraicClosure K
    let p := (cubic.map (algebraMap K L)).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      (cubic.map (algebraMap K L))
    ∃ (d : SelectedActualFiniteNeighborhoodData p hp)
      (hsmooth : Smooth (hypersurfaceToBase p hp))
      (hProj : IsIntegral (projectiveConfigurationQuotientOpen
        (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 8).toScheme)
      (hOrdered : IsIntegral (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left),
      letI : Smooth (hypersurfaceToBase p hp) := hsmooth
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
        (hypersurfaceToBase p hp) 8).toScheme := hProj
      letI : IsIntegral (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left := hOrdered
      ActualCanonicalFiniteFamily p hp d.i := by
  dsimp only
  let L : Type u := AlgebraicClosure K
  let b : K →+* L := algebraMap K L
  let p : MvPolynomial (Fin 4) L := (cubic.map b).toMvPolynomial
  let hp : p.IsHomogeneous 3 :=
    cubic_toMvPolynomial_isHomogeneous_three (cubic.map b)
  have hpEq : F.map b = p := by
    dsimp only [p]
    rw [← hcubic, cubic_toMvPolynomial_map]
  have hp0 : p ≠ 0 := by
    rw [← hpEq]
    simpa only [map_zero] using
      (MvPolynomial.map_injective b (RingHom.injective b)).ne hF0
  letI : Smooth (hypersurfaceToBase p hp) := by
    letI : Smooth (hypersurfaceToBase (F.map b) (hF.map b)) :=
      smooth_hypersurfaceToBase_map b F hF
    exact smooth_hypersurfaceToBase_of_polynomial_eq
      (F.map b) p (hF.map b) hp hpEq
  obtain ⟨d⟩ := nonempty_geometricSelectedActualFiniteNeighborhood_of_smooth
    F hF hF0 cubic hcubic
  let hProj : IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme :=
    isIntegral_cubicConfigurationBase_of_smooth p hp hp0
  let hOrdered : IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left :=
    isIntegral_orderedCubicConfiguration_of_smooth p hp hp0
  exact ⟨d, inferInstance, hProj, hOrdered,
    d.actualCanonicalFiniteFamily p hp hp0⟩

end PfaffianDescent
