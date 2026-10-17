import Mathlib.Algebra.CharZero.Infinite
import AllCharacteristics.VoisinGenericCubicConfiguration
import AllCharacteristics.ProjectiveConfigurationClosedPointIntegrality
import AllCharacteristics.ProjectiveFiniteEtaleConfiguration
import AllCharacteristics.ProjectiveConfigurationGenericSpecialization
import PfaffianDescent.CubicFiniteSubschemeHyperplane
import PfaffianDescent.VoisinFiniteSubschemeDatumResidual
import PfaffianDescent.VoisinDegreeTenSmoothStart
import PfaffianDescent.VoisinDegreeTenRestrictionKernelEtale
import PfaffianDescent.VoisinProjectiveLinearSystem

/-!
# Voisin's first residual from the generic cubic configuration

The coefficient-changed generic degree-ten configuration is finite étale.
Its degree-sixteen completion is fed to the first residual theorem,
leaving only the selected-prime and transversality inputs from Voisin's
geometric argument explicit.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A smooth nonempty cubic is geometrically integral as soon as its equation
is nonzero.  Every coefficient-field change remains smooth and has prime
equation ideal; the base-change isomorphism then transfers integrality back
to the categorical fiber product. -/
theorem geometricallyIntegral_hypersurfaceToBase_of_smooth
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Nonempty (hypersurface p hp)] [Smooth (hypersurfaceToBase p hp)] :
    GeometricallyIntegral (hypersurfaceToBase p hp) := by
  rw [GeometricallyIntegral.eq_geometrically]
  intro L _ y Z fst snd h
  obtain ⟨f, rfl⟩ := Spec.map_surjective y
  let PB : Scheme := Limits.pullback (hypersurfaceToBase p hp)
    (Spec.map (CommRingCat.ofHom f.hom))
  letI : Nonempty PB := inferInstance
  let e := hypersurfaceBaseChangeIso f.hom p hp
  letI : Nonempty (hypersurface (p.map f.hom) (hp.map f.hom)) :=
    ⟨e.inv (Nonempty.some inferInstance)⟩
  letI : Smooth (hypersurfaceToBase (p.map f.hom) (hp.map f.hom)) :=
    smooth_hypersurfaceToBase_map f.hom p hp
  letI : IsIntegral (hypersurface (p.map f.hom) (hp.map f.hom)) :=
    isIntegral_hypersurface_of_smooth_of_principalIdeal_prime
      (p.map f.hom) (hp.map f.hom)
      (principalIdeal_map_prime_of_smooth_homogeneous_cubic f.hom p hp hp0)
  letI : IsIntegral PB := IsIntegral.of_isIso e.hom
  exact IsIntegral.of_isIso h.isoPullback.inv

/-- Over an algebraically closed coefficient field, a nonzero smooth cubic is
automatically nonempty.  The rank-three line-section construction supplies the
point needed by the geometric-integrality argument, so callers need not
provide a separate `Nonempty (hypersurface p hp)` instance. -/
theorem geometricallyIntegral_hypersurfaceToBase_of_smooth_of_algClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    GeometricallyIntegral (hypersurfaceToBase p hp) := by
  letI : Infinite K := inferInstance
  letI : Nonempty (hypersurface p hp) :=
    nonempty_hypersurface_of_nonzero_homogeneous_cubic_equation
      (by decide : 2 ≤ (4 : ℕ)) p hp hp0
  exact geometricallyIntegral_hypersurfaceToBase_of_smooth p hp hp0

/-- The same nonemptiness reduction works over any infinite coefficient field,
without requiring algebraic closedness. -/
theorem geometricallyIntegral_hypersurfaceToBase_of_smooth_of_infinite
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    GeometricallyIntegral (hypersurfaceToBase p hp) := by
  letI : Nonempty (hypersurface p hp) :=
    nonempty_hypersurface_of_nonzero_homogeneous_cubic_equation
      (by decide : 2 ≤ (4 : ℕ)) p hp hp0
  exact geometricallyIntegral_hypersurfaceToBase_of_smooth p hp hp0

/-- The generic ten-point configuration base of an algebraically closed smooth
cubic is integral without separately supplied geometric hypotheses. -/
theorem isIntegral_ten_cubicConfigurationBase_of_smooth_of_algClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    IsIntegral (cubicConfigurationBase p hp 10) := by
  letI : GeometricallyIntegral (toBase (equationIdeal p hp)) :=
    geometricallyIntegral_hypersurfaceToBase_of_smooth_of_algClosed p hp hp0
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : UniversallyOpen (toBase (equationIdeal p hp)) := inferInstance
  letI : LocallyOfFiniteType (toBase (equationIdeal p hp)) := inferInstance
  exact isIntegral_ten_cubicConfigurationQuotientOpen_of_geometricallyIntegral
    p hp hp0 (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)

/-- The generic eleven-point configuration base of an algebraically closed
smooth cubic is integral without separately supplied geometric hypotheses. -/
theorem isIntegral_eleven_cubicConfigurationBase_of_smooth_of_algClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    IsIntegral (cubicConfigurationBase p hp 11) := by
  letI : GeometricallyIntegral (toBase (equationIdeal p hp)) :=
    geometricallyIntegral_hypersurfaceToBase_of_smooth_of_algClosed p hp hp0
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : UniversallyOpen (toBase (equationIdeal p hp)) := inferInstance
  letI : LocallyOfFiniteType (toBase (equationIdeal p hp)) := inferInstance
  exact isIntegral_eleven_cubicConfigurationQuotientOpen_of_geometricallyIntegral
    p hp hp0 (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)

/-- The generic sixteen-point configuration base of an algebraically closed
smooth cubic is integral without separately supplied geometric hypotheses. -/
theorem isIntegral_sixteen_cubicConfigurationBase_of_smooth_of_algClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    IsIntegral (cubicConfigurationBase p hp 16) := by
  letI : GeometricallyIntegral (toBase (equationIdeal p hp)) :=
    geometricallyIntegral_hypersurfaceToBase_of_smooth_of_algClosed p hp hp0
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : UniversallyOpen (toBase (equationIdeal p hp)) := inferInstance
  letI : LocallyOfFiniteType (toBase (equationIdeal p hp)) := inferInstance
  exact isIntegral_sixteen_cubicConfigurationQuotientOpen_of_geometricallyIntegral
    p hp hp0 (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)

/-- A degree-`n` closed point on a smooth cubic makes the degree-`n` generic
configuration base integral.  This combines the internal geometric
integrality proof with the Galois-orbit configuration construction, so no
separate integrality hypothesis remains at this stage. -/
theorem isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp)) (n : ℕ)
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = n) :
    IsIntegral (cubicConfigurationBase p hp n) := by
  letI : Nonempty (hypersurface p hp) := ⟨x.1⟩
  letI : GeometricallyIntegral (hypersurfaceToBase p hp) :=
    geometricallyIntegral_hypersurfaceToBase_of_smooth p hp hp0
  apply @isIntegral_projectiveConfigurationQuotientOpen_of_closedPoint _ _ _ _ _
    (grading (equationIdeal p hp)) _ K _ _ (hypersurfaceToBase p hp) ?_ ?_ ?_ x n hx
  · exact @IsProper.toIsSeparated _ _ _ (isProper_hypersurfaceToBase p hp)
  · exact ‹Smooth (hypersurfaceToBase p hp)›
  · exact geometricallyIntegral_hypersurfaceToBase_of_smooth p hp hp0

/-- A finite étale rank-`n` subscheme on a smooth cubic supplies the
nonemptiness needed to make the ordered degree-`n` configuration space
integral.  This applies to disconnected finite étale data as well as to a
single closed point of degree `n`. -/
theorem isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (n : ℕ) (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) n)
    [Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    IsIntegral
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) n).left := by
  letI : Infinite K := CharZero.infinite K
  letI : IsSeparated (toBase (equationIdeal p hp)) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  letI : GeometricallyIntegral (toBase (equationIdeal p hp)) :=
    geometricallyIntegral_hypersurfaceToBase_of_smooth_of_infinite p hp hp0
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : UniversallyOpen (toBase (equationIdeal p hp)) := inferInstance
  letI : LocallyOfFiniteType (toBase (equationIdeal p hp)) := inferInstance
  have hEtale : Etale
      (D.val.subschemeι ≫ toBase (equationIdeal p hp)) := by
    change Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    infer_instance
  letI : Nonempty
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) n).left :=
    @nonempty_orderedFamilyConfigurationOver_of_finiteEtaleSubscheme
      _ _ _ _ _ (grading (equationIdeal p hp)) _ K _ _
      (toBase (equationIdeal p hp))
      (isSeparated_homogeneousToBase (equationIdeal p hp)) n D hEtale
  exact isIntegral_orderedFamilyConfigurationOver_of_geometricallyIntegral
    (toBase (equationIdeal p hp)) n

/-- A finite étale rank-`n` subscheme also makes the unordered generic
configuration base integral. -/
theorem isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (n : ℕ) (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) n)
    [Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    IsIntegral (cubicConfigurationBase p hp n) := by
  letI : Infinite K := CharZero.infinite K
  letI : IsSeparated (toBase (equationIdeal p hp)) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  letI : GeometricallyIntegral (toBase (equationIdeal p hp)) :=
    geometricallyIntegral_hypersurfaceToBase_of_smooth_of_infinite p hp hp0
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : UniversallyOpen (toBase (equationIdeal p hp)) := inferInstance
  letI : LocallyOfFiniteType (toBase (equationIdeal p hp)) := inferInstance
  have hEtale : Etale
      (D.val.subschemeι ≫ toBase (equationIdeal p hp)) := by
    change Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    infer_instance
  letI : Nonempty
      (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) n).left :=
    @nonempty_orderedFamilyConfigurationOver_of_finiteEtaleSubscheme
      _ _ _ _ _ (grading (equationIdeal p hp)) _ K _ _
      (toBase (equationIdeal p hp))
      (isSeparated_homogeneousToBase (equationIdeal p hp)) n D hEtale
  exact isIntegral_cubicConfigurationBase_of_geometricallyIntegral p hp n

/-- A point constructed over the generic degree-`n` configuration of a smooth
cubic specializes back to the ground field when a degree-`n` closed point is
available.  This is the specialization half of the generic-configuration
strategy: the closed point supplies both the integral parameter space and a
ground-field configuration at which properness specializes the generic point. -/
theorem exists_section_of_smooth_cubicConfiguration_functionField_point_of_closedPoint
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp)) (n : ℕ)
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = n) :
    letI : IsIntegral (cubicConfigurationBase p hp n) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x n hx
    ∀ (s : Spec (.of (cubicConfigurationBase p hp n).functionField) ⟶
        hypersurface p hp),
      s ≫ hypersurfaceToBase p hp =
        cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n →
      ∃ q : Spec (.of K) ⟶ hypersurface p hp,
        q ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  letI : IsIntegral (cubicConfigurationBase p hp n) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x n hx
  intro s hs
  letI : IsProper (hypersurfaceToBase p hp) := isProper_hypersurfaceToBase p hp
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    @IsProper.toIsSeparated _ _ _ (isProper_hypersurfaceToBase p hp)
  obtain ⟨c, hc⟩ := @exists_projectiveConfigurationPoint_of_closedPoint
    _ _ _ _ _ (grading (equationIdeal p hp)) _ K _ _ (hypersurfaceToBase p hp)
    (@IsProper.toIsSeparated _ _ _ (isProper_hypersurfaceToBase p hp))
    (@IsProper.toLocallyOfFiniteType _ _ _ (isProper_hypersurfaceToBase p hp)) x n hx
  exact @proper_point_of_projectiveConfiguration_functionField_point
    _ _ _ _ _ (grading (equationIdeal p hp)) _ K _ (hypersurfaceToBase p hp)
    (isProper_hypersurfaceToBase p hp) ‹Smooth (hypersurfaceToBase p hp)› n
    (isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x n hx) c hc s hs

/-- The generic degree-ten configuration attached to Coray's closed point can
be completed by two successive avoiding line sections after coefficient
change.  Thus Voisin's first length-sixteen datum is constructed over the
degree-ten configuration function field, while retaining the original
degree-ten generic subscheme as a distinguished component. -/
theorem exists_degreeTenGenericConfiguration_rankSixteenCompletion_of_smooth_cubic_of_closedPoint
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10) :
    letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
    ∃ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      Nonempty {C : DegreeTenRankSixteenCompletion
          (p.map a.hom) (hp.map a.hom)
          (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) //
        finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) C.datum =
          finiteSubschemeDatumCycle
            (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
            (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) +
          finiteSubschemeDatumCycle
            (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) C.first +
          finiteSubschemeDatumCycle
            (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) C.second} := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  obtain ⟨a, ha⟩ := exists_cubicConfigurationGenericBaseMap p hp 10
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  obtain ⟨C⟩ := nonempty_degreeTenRankSixteenCompletion_of_smooth_cubic_of_field
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
    (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)
  exact ⟨a, ha, ⟨C, C.datum_cycle⟩⟩

/-- Coray's degree-ten point produces, over the function field of its generic
configuration, the complete first-section datum in Voisin's construction.
Thus the line-section completion, normalized coordinates, and a regular
auxiliary cubic no longer remain external inputs in the degree-ten branch.
The only omitted property of that cubic is the genuinely geometric assertion
that its intersection with the surface is integral. -/
theorem exists_degreeTenGenericConfiguration_regularCubicSectionData_of_smooth_cubic_of_closedPoint
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10) :
    letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
    ∃ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      Nonempty (DegreeTenRegularCubicSectionData
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)) := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  obtain ⟨a, ha⟩ := exists_cubicConfigurationGenericBaseMap p hp 10
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  exact ⟨a, ha,
    nonempty_degreeTenRegularCubicSectionData_of_smooth_cubic
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)⟩

/-- The generic length-sixteen configuration already has all section data
needed for Voisin's first residual once the coefficient-changed cubic is
prime. Normalization, incidence on the configuration, and a nonzero cubic
regular modulo the surface equation are therefore formal consequences of the
finite configuration. The remaining first-section condition is primeness of
the intermediate cubic--cubic curve. -/
theorem exists_genericConfiguration_regular_cubic_section_of_prime_surface
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 16 ≫ cubicConfigurationToBase p hp 16)
    [Infinite (cubicConfigurationBase p hp 16).functionField]
    (hne : p ≠ 0)
    (hprime : (Ideal.span ({p.map a.hom} : Set
      (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 16).functionField))).IsPrime) :
    let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
    letI : IsFinite (D.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := D.property.1
    letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
    ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (ell q : MvPolynomial (Fin 4)
        (cubicConfigurationBase p hp 16).functionField),
      Function.Surjective (eval₂Hom
        (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x) ∧
      ell.IsHomogeneous 1 ∧ ell.eval₂
        (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x = 1 ∧
      (p.map a.hom).eval₂
        (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x = 0 ∧
      q.IsHomogeneous 3 ∧ q.eval₂
        (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x = 0 ∧
      q ≠ 0 ∧ IsRelPrime (p.map a.hom) q := by
  let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
  letI : IsFinite (D.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫
    hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
  exact cubicFiniteSubscheme_degree_sixteen_regular_cubic_section_of_prime_surface
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationCoefficientChange_ne_zero p hp 16 a hne)
    D.val.subschemeι
    (AllCharacteristics.finiteSubschemeDatum_finiteSchemeRank
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) D)
    hprime

/-- In Voisin's characteristic-zero situation the configuration function
field is automatically infinite. Thus the preceding selection is available
without a separate infinitude hypothesis. -/
theorem exists_genericConfiguration_regular_cubic_section_of_prime_surface_of_charZero
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 16 ≫ cubicConfigurationToBase p hp 16)
    [CharZero K]
    [Flat (toBase (equationIdeal p hp))]
    (hne : p ≠ 0)
    (hprime : (Ideal.span ({p.map a.hom} : Set
      (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 16).functionField))).IsPrime) :
    let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
    letI : IsFinite (D.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := D.property.1
    letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
    ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (ell q : MvPolynomial (Fin 4)
        (cubicConfigurationBase p hp 16).functionField),
      Function.Surjective (eval₂Hom
        (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x) ∧
      ell.IsHomogeneous 1 ∧ ell.eval₂
        (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x = 1 ∧
      (p.map a.hom).eval₂
        (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x = 0 ∧
      q.IsHomogeneous 3 ∧ q.eval₂
        (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x = 0 ∧
      q ≠ 0 ∧ IsRelPrime (p.map a.hom) q := by
  letI : CharZero (cubicConfigurationBase p hp 16).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 16
  letI : Infinite (cubicConfigurationBase p hp 16).functionField :=
    CharZero.infinite _
  exact exists_genericConfiguration_regular_cubic_section_of_prime_surface
    p hp a ha hne hprime

/-- For a smooth cubic in characteristic zero, the generic length-sixteen
configuration has a nonzero regular cubic section without separately assuming
that the coefficient-changed surface equation is prime.  Smoothness gives
that primeness after the change to the configuration function field.  The
remaining first-residual condition is only primeness of the selected
intermediate cubic--cubic curve. -/
theorem exists_genericConfiguration_regular_cubic_section_of_smooth_surface_of_charZero
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 16 ≫ cubicConfigurationToBase p hp 16)
    [CharZero K]
    [Flat (toBase (equationIdeal p hp))]
    (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
    letI : IsFinite (D.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := D.property.1
    letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
    ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (ell q : MvPolynomial (Fin 4)
        (cubicConfigurationBase p hp 16).functionField),
      Function.Surjective (eval₂Hom
        (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x) ∧
      ell.IsHomogeneous 1 ∧ ell.eval₂
        (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x = 1 ∧
      (p.map a.hom).eval₂
        (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x = 0 ∧
      q.IsHomogeneous 3 ∧ q.eval₂
        (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x = 0 ∧
      q ≠ 0 ∧ IsRelPrime (p.map a.hom) q := by
  exact exists_genericConfiguration_regular_cubic_section_of_prime_surface_of_charZero
    p hp a ha hne
    (principalIdeal_map_prime_of_smooth_homogeneous_cubic a.hom p hp hne)

/-- A specified transverse three-cubic complete intersection through the
generic length-sixteen configuration has a finite étale rank-eleven residual.
This is the direct geometric interface for Voisin's first residual step: it
needs no prime-intermediate or uniform-transversality strengthening. -/
theorem exists_genericConfiguration_residual_and_toBase_etale_of_selected_coordinates
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 16 ≫ cubicConfigurationToBase p hp 16)
    [CharZero K]
    [Flat (toBase (equationIdeal p hp))]
    (hne : p ≠ 0)
    (q r : MvPolynomial (Fin 4) (cubicConfigurationBase p hp 16).functionField)
    (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hrel : IsRelPrime (p.map a.hom) q)
    (hregular : ∀ y : MvPolynomial (Fin 4) (cubicConfigurationBase p hp 16).functionField,
      r * y ∈ Ideal.span ({p.map a.hom, q} : Set
        (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 16).functionField)) →
        y ∈ Ideal.span ({p.map a.hom, q} : Set
          (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 16).functionField)))
    (coordinates : let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
      letI : IsFinite (D.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
        (ell : MvPolynomial (Fin 4)
          (cubicConfigurationBase p hp 16).functionField),
        Function.Surjective (eval₂Hom
          (algebraMap (cubicConfigurationBase p hp 16).functionField
            Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x = 1 ∧
        (p.map a.hom).eval₂
          (algebraMap (cubicConfigurationBase p hp 16).functionField
            Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x = 0)
    (htransverse : Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map a.hom) q r (hp.map a.hom) hq hr))) :
    ∃ R : FiniteSubschemeDatum
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11,
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := by
  have hpmap : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 16 a hne
  have hq0 : q ≠ 0 :=
    isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree (hp.map a.hom) (by decide) hrel
  let _ : CharZero (cubicConfigurationBase p hp 16).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 16
  let _ : Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map a.hom) q r (hp.map a.hom) hq hr)) := htransverse
  let R := finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates
    (p.map a.hom) q r (hp.map a.hom) hq hr
    hpmap hq0 hrel hregular
    (cubicConfigurationGenericFiniteSubscheme p hp 16 a ha) coordinates
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_⟩
  exact finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates_toBase_etale
    (p.map a.hom) q r (hp.map a.hom) hq hr
    hpmap hq0 hrel hregular
    (cubicConfigurationGenericFiniteSubscheme p hp 16 a ha) coordinates

/-- The scheme-level version of the first generic residual.  An actual
closed immersion of the generic length-sixteen configuration into the
selected complete intersection gives both the finite étale rank-eleven
residual and its support separation from the configuration.  This is the
interface needed for the first pencil, without passing through a
coordinate-only presentation of containment. -/
theorem exists_genericConfiguration_residual_and_toBase_etale_and_disjoint_of_completeIntersectionEmbedding
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 16 ≫ cubicConfigurationToBase p hp 16)
    [CharZero K]
    [Flat (toBase (equationIdeal p hp))]
    (hne : p ≠ 0)
    (q r : MvPolynomial (Fin 4) (cubicConfigurationBase p hp 16).functionField)
    (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hrel : IsRelPrime (p.map a.hom) q)
    (hregular : ∀ y : MvPolynomial (Fin 4) (cubicConfigurationBase p hp 16).functionField,
      r * y ∈ Ideal.span ({p.map a.hom, q} : Set
        (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 16).functionField)) →
        y ∈ Ideal.span ({p.map a.hom, q} : Set
          (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 16).functionField)))
    (j : (cubicConfigurationGenericFiniteSubscheme p hp 16 a ha).val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal
        (p.map a.hom) q r (hp.map a.hom) hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface
      (p.map a.hom) q r (hp.map a.hom) hq hr =
      (cubicConfigurationGenericFiniteSubscheme p hp 16 a ha).val.subschemeι)
    [Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map a.hom) q r (hp.map a.hom) hq hr))] :
    ∃ R : FiniteSubschemeDatum
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11,
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
          (cubicConfigurationGenericFiniteSubscheme p hp 16 a ha)))
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R)) := by
  have hpmap : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 16 a hne
  have hq0 : q ≠ 0 :=
    isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree
      (hp.map a.hom) (by decide) hrel
  letI : CharZero (cubicConfigurationBase p hp 16).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 16
  let R := finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding
    (p.map a.hom) q r (hp.map a.hom) hq hr hpmap hq0 hrel hregular
    (cubicConfigurationGenericFiniteSubscheme p hp 16 a ha) j hj
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_, ?_⟩
  · exact finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding_toBase_etale
      (p.map a.hom) q r (hp.map a.hom) hq hr hpmap hq0 hrel hregular
      (cubicConfigurationGenericFiniteSubscheme p hp 16 a ha) j hj
  · exact (disjoint_finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding
      (p.map a.hom) q r (hp.map a.hom) hq hr hpmap hq0 hrel hregular
      (cubicConfigurationGenericFiniteSubscheme p hp 16 a ha) j hj).symm

/-- Conditional first residual for Voisin's generic length-sixteen cubic
configuration.  The remaining inputs are precisely the selected prime
intermediate cubic and transversality of the resulting complete intersection. -/
theorem exists_genericConfiguration_residual_and_toBase_etale_of_selected_prime_intermediate
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 16)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 16).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 16 ≫ cubicConfigurationToBase p hp 16)
    [CharZero K]
    [Flat (toBase (equationIdeal p hp))]
    (hne : p ≠ 0)
    (hselected : let D := cubicConfigurationGenericFiniteSubscheme p hp 16 a ha
      letI : IsFinite (D.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
        (ell q : MvPolynomial (Fin 4)
          (cubicConfigurationBase p hp 16).functionField),
        Function.Surjective (eval₂Hom
          (algebraMap (cubicConfigurationBase p hp 16).functionField
            Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧
        ell.eval₂ (algebraMap (cubicConfigurationBase p hp 16).functionField
          Γ(D.val.subscheme, ⊤)) x = 1 ∧
        (p.map a.hom).eval₂
          (algebraMap (cubicConfigurationBase p hp 16).functionField
            Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.IsHomogeneous 3 ∧ q.eval₂
          (algebraMap (cubicConfigurationBase p hp 16).functionField
            Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q ≠ 0 ∧ IsRelPrime (p.map a.hom) q ∧
        (Ideal.span ({p.map a.hom, q} : Set
          (MvPolynomial (Fin 4)
            (cubicConfigurationBase p hp 16).functionField))).IsPrime)
    (htransverse : ∀
      (q r : MvPolynomial (Fin 4) (cubicConfigurationBase p hp 16).functionField)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime (p.map a.hom) q →
      (∀ y : MvPolynomial (Fin 4) (cubicConfigurationBase p hp 16).functionField,
        r * y ∈ Ideal.span ({p.map a.hom, q} : Set
          (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 16).functionField)) →
          y ∈ Ideal.span ({p.map a.hom, q} : Set
            (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 16).functionField))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map a.hom) q r (hp.map a.hom) hq hr))) :
    ∃ R : FiniteSubschemeDatum
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11,
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := by
  letI : CharZero (cubicConfigurationBase p hp 16).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 16
  exact exists_finiteSubschemeDatum_degree_sixteen_residual_and_toBase_etale_of_selected_prime_intermediate
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationCoefficientChange_ne_zero p hp 16 a hne)
    (cubicConfigurationGenericFiniteSubscheme p hp 16 a ha) hselected htransverse

/-- The generic-configuration form of the associated-component avoidance
condition in Voisin's Lemma 3.3.  It is deliberately stated as
noncontainment on every associated component, rather than as the auxiliary
finite-rank inequality consumed by the residual construction. -/
def GenericDegreeTenThirdCubicAvoidance
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 10)] : Prop :=
  ∀ (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 10).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
    (C : DegreeTenRankSixteenCompletion (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)),
    DegreeTenCompletionThirdCubicAvoidsAssociatedPrimes
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) C

/-- The finite-rank condition used by the residual calculation is the linear
algebra form of generic associated-component avoidance. -/
theorem GenericDegreeTenThirdCubicAvoidance.finrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    [Infinite (cubicConfigurationBase p hp 10).functionField]
    (havoid : GenericDegreeTenThirdCubicAvoidance p hp) :
    ∀ (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
      (C : DegreeTenRankSixteenCompletion (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)),
      DegreeTenCompletionThirdCubicFinrankDrop
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) C := by
  intro a ha C
  exact (havoid a ha C).finrankDrop

/- The generic formulation is equivalent to its finite-rank version as well:
   the converse is obtained pointwise from the associated-prime linear
   algebra equivalence.  This lets later geometric arguments prove either
   form without carrying an artificial choice of formulation. -/
theorem GenericDegreeTenThirdCubicAvoidance.of_finrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    [Infinite (cubicConfigurationBase p hp 10).functionField]
    (hdrop : ∀ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
      (C : DegreeTenRankSixteenCompletion (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)),
      DegreeTenCompletionThirdCubicFinrankDrop
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) C) :
    GenericDegreeTenThirdCubicAvoidance p hp := by
  intro a ha C
  exact DegreeTenCompletionThirdCubicAvoidsAssociatedPrimes.of_finrankDrop
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) C (hdrop a ha C)

/-- The uniform Lemma 3.3 avoidance condition immediately specializes to
the selected regular cubic retained by the residual construction.  This
forgets the unused completion-wide quantifier while preserving the actual
chart and embedding carried by S. -/
theorem GenericDegreeTenThirdCubicAvoidance.selectedAvoidance
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    [Infinite (cubicConfigurationBase p hp 10).functionField]
    (havoid : GenericDegreeTenThirdCubicAvoidance p hp)
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 10).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)) :
    DegreeTenRegularCubicSectionSelectedAvoidance
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S := by
  exact DegreeTenRegularCubicSectionSelectedAvoidance.ofCompletionAvoidance
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S
    (havoid a ha S.completion)

/-- The generic degree-ten configuration attached to Coray's closed point
carries Voisin's first finite étale residual once the explicit base-locus
rank-drop and transverse-complete-intersection assertions are established
there.  The completion by two line sections is constructed internally, so
these are precisely the remaining Lemma 3.3 and Bertini inputs. -/
theorem exists_degreeTenGenericConfiguration_residual_and_toBase_etale_of_smooth_cubic_of_closedPoint
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    : letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
    (∀
      (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
      (C : DegreeTenRankSixteenCompletion (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)),
      DegreeTenCompletionThirdCubicFinrankDrop
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) C) →
    (∀
      (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (_ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      CubicTripleIntersectionTransverse (p.map a.hom) (hp.map a.hom)) →
    ∃ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
      (C : DegreeTenRankSixteenCompletion (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha))
      (R : FiniteSubschemeDatum
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11),
      DegreeTenCompletionThirdCubicFinrankDrop
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) C ∧
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  intro hdrop htransverse
  obtain ⟨a, ha⟩ := exists_cubicConfigurationGenericBaseMap p hp 10
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  obtain ⟨C⟩ := nonempty_degreeTenRankSixteenCompletion_of_smooth_cubic_of_field
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
    (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)
  obtain ⟨R, hRdegree, hRetale⟩ :=
    exists_degreeTenResidualDatum_and_toBase_etale_of_smooth_cubic_of_completion_and_finrank_drop
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) C
      (hdrop a ha C) (htransverse a ha)
  exact ⟨a, ha, C, R, hdrop a ha C, hRdegree, hRetale⟩

/-! The algebraically closed characteristic-zero branch does not need Coray's
   degree-ten closed point merely to obtain an integral configuration base:
   smoothness and the explicit ten-point interpolation witness already give
   that instance. -/
theorem exists_degreeTenGenericConfiguration_residual_and_toBase_etale_of_smooth_cubic_of_algClosed
    [CharZero K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    : letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_ten_cubicConfigurationBase_of_smooth_of_algClosed p hp hp0
    (∀
      (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
      (C : DegreeTenRankSixteenCompletion (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)),
      DegreeTenCompletionThirdCubicFinrankDrop
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) C) →
    (∀
      (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (_ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      CubicTripleIntersectionTransverse (p.map a.hom) (hp.map a.hom)) →
    ∃ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
      (C : DegreeTenRankSixteenCompletion (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha))
      (R : FiniteSubschemeDatum
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11),
      DegreeTenCompletionThirdCubicFinrankDrop
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) C ∧
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_ten_cubicConfigurationBase_of_smooth_of_algClosed p hp hp0
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  intro hdrop htransverse
  obtain ⟨a, ha⟩ := exists_cubicConfigurationGenericBaseMap p hp 10
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  obtain ⟨C⟩ := nonempty_degreeTenRankSixteenCompletion_of_smooth_cubic_of_field
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
    (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)
  obtain ⟨R, hRdegree, hRetale⟩ :=
    exists_degreeTenResidualDatum_and_toBase_etale_of_smooth_cubic_of_completion_and_finrank_drop
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) C
      (hdrop a ha C) (htransverse a ha)
  exact ⟨a, ha, C, R, hdrop a ha C, hRdegree, hRetale⟩

/-- The generic first residual stated with the geometric content of Voisin's
Lemma 3.3: the cubic system through the completed configuration avoids every
associated component of every relevant cubic--cubic intersection.  The
finite-rank formulation is derived internally. -/
theorem exists_degreeTenGenericConfiguration_residual_and_toBase_etale_of_smooth_cubic_of_closedPoint_and_avoidsAssociatedPrimes
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    : letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
    GenericDegreeTenThirdCubicAvoidance p hp →
    (∀
      (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (_ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      CubicTripleIntersectionTransverse (p.map a.hom) (hp.map a.hom)) →
    ∃ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
      (C : DegreeTenRankSixteenCompletion (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha))
      (R : FiniteSubschemeDatum
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11),
      DegreeTenCompletionThirdCubicAvoidsAssociatedPrimes
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) C ∧
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  intro havoid htransverse
  obtain ⟨a, ha, C, R, _hdrop, hRdegree, hRetale⟩ :=
    exists_degreeTenGenericConfiguration_residual_and_toBase_etale_of_smooth_cubic_of_closedPoint
      p hp hp0 x hx havoid.finrankDrop htransverse
  exact ⟨a, ha, C, R, havoid a ha C, hRdegree, hRetale⟩

/- The transversality premise in the preceding theorem can be supplied by the
   chartwise Jacobian criterion.  This keeps the remaining Bertini input in
   the explicit form used by `TripleCompleteIntersectionJacobian`, rather than
   hiding it behind an abstract finite-etale assertion. -/
theorem exists_degreeTenGenericConfiguration_residual_and_toBase_etale_of_smooth_cubic_of_closedPoint_and_avoidsAssociatedPrimes_of_chartJacobianUnit
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    : letI : IsIntegral (cubicConfigurationBase p hp 10) :=
        isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
      GenericDegreeTenThirdCubicAvoidance p hp →
      (∀
        (a : CommRingCat.of K ⟶
          CommRingCat.of (cubicConfigurationBase p hp 10).functionField)
        (_ha : Spec.map a =
          cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
        CubicTripleIntersectionChartJacobianUnit
          (p.map a.hom) (hp.map a.hom)) →
      ∃ (a : CommRingCat.of K ⟶
          CommRingCat.of (cubicConfigurationBase p hp 10).functionField)
        (ha : Spec.map a =
          cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
        (C : DegreeTenRankSixteenCompletion (p.map a.hom) (hp.map a.hom)
          (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha))
        (R : FiniteSubschemeDatum
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11),
      DegreeTenCompletionThirdCubicAvoidsAssociatedPrimes
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) C ∧
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  intro havoid hjacobian
  exact exists_degreeTenGenericConfiguration_residual_and_toBase_etale_of_smooth_cubic_of_closedPoint_and_avoidsAssociatedPrimes
    p hp hp0 x hx havoid (fun a ha ↦
      CubicTripleIntersectionChartJacobianUnit.toTransverse
        (p.map a.hom) (hp.map a.hom) (hjacobian a ha))

/-- A selected regular first cubic at the generic degree-ten configuration
produces Voisin's finite étale degree-eleven residual, disjoint from the
actual degree-sixteen completion.  This records the strong residual output
in the generic-configuration setting once Lemma 3.3 supplies the selected
rank-drop. -/
theorem exists_degreeTenResidual_and_toBase_etale_and_disjoint_at_genericConfiguration
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    [Smooth (hypersurfaceToBase p hp)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 10).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha))
    (hdrop : DegreeTenCompletionThirdCubicFinrankDrop
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S.completion)
    (htransverse : CubicTripleIntersectionTransverse (p.map a.hom) (hp.map a.hom)) :
    ∃ R : FiniteSubschemeDatum
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11,
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R)) := by
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  exact
    exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_regularCubicSectionEmbeddingData_and_finrank_drop
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S hdrop htransverse

/-- At a fixed generic configuration, Voisin's associated-component
avoidance statement supplies the rank-eleven residual directly. -/
theorem exists_degreeTenResidual_and_toBase_etale_and_disjoint_at_genericConfiguration_of_avoidsAssociatedPrimes
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    [Smooth (hypersurfaceToBase p hp)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 10).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha))
    (havoid : DegreeTenCompletionThirdCubicAvoidsAssociatedPrimes
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S.completion)
    (htransverse : CubicTripleIntersectionTransverse (p.map a.hom) (hp.map a.hom)) :
    ∃ R : FiniteSubschemeDatum
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11,
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R)) := by
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  exact exists_degreeTenResidual_and_toBase_etale_and_disjoint_at_genericConfiguration
    p hp hp0 a ha S havoid.finrankDrop htransverse

/-- At a fixed generic configuration, the selected-cubic form of Lemma 3.3
is sufficient.  The associated-component condition is imposed only on the
actual first cubic and normalized chart retained by `S`, and the Bertini
condition only on the resulting regular third cubic. -/
theorem exists_degreeTenResidual_and_toBase_etale_and_disjoint_at_genericConfiguration_of_selectedAvoidance
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    [Smooth (hypersurfaceToBase p hp)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 10).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha))
    (havoid : DegreeTenRegularCubicSectionSelectedAvoidance
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S)
    (htransverse : ∀ (r : MvPolynomial (Fin 4)
        (cubicConfigurationBase p hp 10).functionField)
      (hr : r.IsHomogeneous 3),
      (∀ y : MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField,
        r * y ∈ Ideal.span ({p.map a.hom, S.q} : Set
          (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField)) →
          y ∈ Ideal.span ({p.map a.hom, S.q} : Set
            (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map a.hom) S.q r (hp.map a.hom) S.hq hr))) :
    ∃ R : FiniteSubschemeDatum
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11,
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R)) := by
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  exact
    exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_regularCubicSectionEmbeddingData_of_selectedAvoidance
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S havoid htransverse

/-- A prime selected cubic--cubic curve is a sufficient geometric substitute
for the selected associated-component statement.  The section-space proof of
`DegreeTenRegularCubicSectionSelectedAvoidance.ofPrimeIntermediate` supplies
the regular third cubic internally, so this branch asks only for primality of
the one curve actually used and transversality of the resulting triple. -/
theorem exists_degreeTenResidual_and_toBase_etale_and_disjoint_at_genericConfiguration_of_primeIntermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    [Smooth (hypersurfaceToBase p hp)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 10).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha))
    (hprime : (Ideal.span ({p.map a.hom, S.q} : Set
      (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField))).IsPrime)
    (htransverse : ∀ (r : MvPolynomial (Fin 4)
      (cubicConfigurationBase p hp 10).functionField) (hr : r.IsHomogeneous 3),
      (∀ y : MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField,
        r * y ∈ Ideal.span ({p.map a.hom, S.q} : Set
          (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField)) →
          y ∈ Ideal.span ({p.map a.hom, S.q} : Set
            (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map a.hom) S.q r (hp.map a.hom) S.hq hr))) :
    ∃ R : FiniteSubschemeDatum
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11,
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R)) := by
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  exact
    exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_regularCubicSectionEmbeddingData_of_selectedAvoidance
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S
      (DegreeTenRegularCubicSectionSelectedAvoidance.ofPrimeIntermediate
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S hprime)
      htransverse

theorem exists_degreeTenResidual_and_toBase_etale_and_disjoint_at_genericConfiguration_of_selectedFinrankDrop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    [Smooth (hypersurfaceToBase p hp)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 10).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha))
    (hdrop : DegreeTenRegularCubicSectionSelectedFinrankDrop
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S)
    (htransverse : ∀ (r : MvPolynomial (Fin 4)
        (cubicConfigurationBase p hp 10).functionField)
      (hr : r.IsHomogeneous 3),
      (∀ y : MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField,
        r * y ∈ Ideal.span ({p.map a.hom, S.q} : Set
          (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField)) →
          y ∈ Ideal.span ({p.map a.hom, S.q} : Set
            (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map a.hom) S.q r (hp.map a.hom) S.hq hr))) :
    ∃ R : FiniteSubschemeDatum
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11,
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R)) := by
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  exact
    exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_regularCubicSectionEmbeddingData_of_selectedFinrankDrop
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S hdrop htransverse

/-- The strong first-residual output at one generic degree-ten configuration:
the completed degree-sixteen datum and the finite étale degree-eleven
residual are retained together with their scheme-theoretic disjointness. -/
def DegreeTenGenericFirstResidualGeometry
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 10).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10) : Prop :=
  ∃ (C : DegreeTenRankSixteenCompletion (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha))
    (R : FiniteSubschemeDatum
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11),
    EffectiveZeroCycle.degree
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
      (finiteSubschemeDatumCycle
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
    Etale (R.val.subschemeι ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) ∧
    Disjoint
      (Set.range (finiteSubschemeDatumSpecMap
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) C.datum))
      (Set.range (finiteSubschemeDatumSpecMap
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R))

/-- The proper singular locus for cubics through one completed generic
degree-ten configuration gives the strong first residual directly.  The
restriction-kernel selector supplies the transverse cubic, so this entry
point needs no universal transversality assertion or prime intermediate
curve. -/
theorem degreeTenGenericFirstResidualGeometry_of_restrictionKernelProperChart
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    [Smooth (hypersurfaceToBase p hp)]
    [Infinite (cubicConfigurationBase p hp 10).functionField]
    (a : CommRingCat.of K ⟶
      CommRingCat.of (cubicConfigurationBase p hp 10).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha))
    (hproper : DegreeTenRegularCubicSectionRestrictionKernelProperChart
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S) :
    DegreeTenGenericFirstResidualGeometry p hp a ha := by
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  obtain ⟨R, hdegree, hetale, hdisjoint⟩ :=
    exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_restrictionKernelProperChart
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S hproper
  exact ⟨S.completion, R, hdegree, hetale, hdisjoint⟩

/-- Coray's degree-ten point supplies the integral generic configuration
base.  Once Lemma 3.3 gives the selected-cubic rank drop and Bertini gives
transversality there, the generic configuration has the full strong first
residual geometry needed by Voisin's first pencil. -/
theorem exists_degreeTenGenericFirstResidualGeometry_of_smooth_cubic_of_closedPoint
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    : letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
    (∀
      (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
      (S : DegreeTenRegularCubicSectionEmbeddingData (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)),
      DegreeTenCompletionThirdCubicFinrankDrop
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S.completion) →
    (∀
      (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (_ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      CubicTripleIntersectionTransverse (p.map a.hom) (hp.map a.hom)) →
    ∃ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      DegreeTenGenericFirstResidualGeometry p hp a ha := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  intro hdrop htransverse
  obtain ⟨a, ha⟩ := exists_cubicConfigurationGenericBaseMap p hp 10
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  obtain ⟨C, R, hRdegree, hRetale, hdisjoint⟩ :=
    exists_degreeTenCompletion_and_residualDatum_and_toBase_etale_and_disjoint_of_smooth_cubic_and_finrank_drop
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)
      (hdrop a ha) (htransverse a ha)
  exact ⟨a, ha, C, R, hRdegree, hRetale, hdisjoint⟩

/-- The same strong generic residual geometry follows from Lemma 3.3 in its
natural form.  This is the version used by the remaining geometric work:
associated-component avoidance is the only base-locus input, and its
finite-rank reformulation never becomes an additional assumption. -/
theorem exists_degreeTenGenericFirstResidualGeometry_of_smooth_cubic_of_closedPoint_and_avoidsAssociatedPrimes
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    : letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
    GenericDegreeTenThirdCubicAvoidance p hp →
    (∀
      (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (_ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      CubicTripleIntersectionTransverse (p.map a.hom) (hp.map a.hom)) →
    ∃ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      DegreeTenGenericFirstResidualGeometry p hp a ha := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  intro havoid htransverse
  have hdrop := GenericDegreeTenThirdCubicAvoidance.finrankDrop p hp havoid
  exact exists_degreeTenGenericFirstResidualGeometry_of_smooth_cubic_of_closedPoint
    p hp hp0 x hx (fun a ha S => hdrop a ha S.completion) htransverse

/- The same first-residual conclusion with transversality exposed through the
   chartwise Jacobian units.  This is the direct interface for a concrete
   Bertini/Jacobian computation on the coefficient-changed generic cubic. -/
theorem exists_degreeTenGenericFirstResidualGeometry_of_smooth_cubic_of_closedPoint_and_avoidsAssociatedPrimes_of_chartJacobianUnit
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    : letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
    GenericDegreeTenThirdCubicAvoidance p hp →
    (∀
      (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (_ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      CubicTripleIntersectionChartJacobianUnit
        (p.map a.hom) (hp.map a.hom)) →
    ∃ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      DegreeTenGenericFirstResidualGeometry p hp a ha := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  intro havoid hjacobian
  exact exists_degreeTenGenericFirstResidualGeometry_of_smooth_cubic_of_closedPoint_and_avoidsAssociatedPrimes
    p hp hp0 x hx havoid (fun a ha ↦
      CubicTripleIntersectionChartJacobianUnit.toTransverse
        (p.map a.hom) (hp.map a.hom) (hjacobian a ha))

/-- The first generic residual needs Lemma 3.3 only for the regular cubic
that is actually selected, and Bertini only for the third cubic subsequently
selected from that one system.  This is the existential, selected-section
form of the remaining first-residual geometry. -/
theorem exists_degreeTenGenericFirstResidualGeometry_of_smooth_cubic_of_closedPoint_of_selectedAvoidance
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    : letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
    (∀
      (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      ∃ S : DegreeTenRegularCubicSectionEmbeddingData
          (p.map a.hom) (hp.map a.hom)
          (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha),
        DegreeTenRegularCubicSectionSelectedAvoidance
          (p.map a.hom) (hp.map a.hom)
          (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S ∧
        ∀ (r : MvPolynomial (Fin 4)
          (cubicConfigurationBase p hp 10).functionField) (hr : r.IsHomogeneous 3),
          (∀ y : MvPolynomial (Fin 4)
            (cubicConfigurationBase p hp 10).functionField,
            r * y ∈ Ideal.span ({p.map a.hom, S.q} : Set
              (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField)) →
              y ∈ Ideal.span ({p.map a.hom, S.q} : Set
                (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField))) →
          Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
            (p.map a.hom) S.q r (hp.map a.hom) S.hq hr))) →
    ∃ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      DegreeTenGenericFirstResidualGeometry p hp a ha := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  intro hselected
  obtain ⟨a, ha⟩ := exists_cubicConfigurationGenericBaseMap p hp 10
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  obtain ⟨S, havoid, htransverse⟩ := hselected a ha
  obtain ⟨R, hRdegree, hRetale, hdisjoint⟩ :=
    exists_degreeTenResidual_and_toBase_etale_and_disjoint_at_genericConfiguration_of_selectedAvoidance
      p hp hp0 a ha S havoid htransverse
  exact ⟨a, ha, S.completion, R, hRdegree, hRetale, hdisjoint⟩

/-- The uniform associated-prime hypothesis can be combined with the
selected-section Bertini input without first postulating a separate selected
avoidance certificate.  The former is specialized to the actual retained
completion by `selectedAvoidance`, and the latter supplies only the transverse
third-cubic intersections used by the residual calculation. -/
theorem exists_degreeTenGenericFirstResidualGeometry_of_smooth_cubic_of_closedPoint_of_avoidsAssociatedPrimes_and_selectedSectionData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    : letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
    GenericDegreeTenThirdCubicAvoidance p hp →
    (∀
      (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      ∃ S : DegreeTenRegularCubicSectionEmbeddingData
          (p.map a.hom) (hp.map a.hom)
          (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha),
        ∀ (r : MvPolynomial (Fin 4)
          (cubicConfigurationBase p hp 10).functionField) (hr : r.IsHomogeneous 3),
          (∀ y : MvPolynomial (Fin 4)
            (cubicConfigurationBase p hp 10).functionField,
            r * y ∈ Ideal.span ({p.map a.hom, S.q} : Set
              (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField)) →
              y ∈ Ideal.span ({p.map a.hom, S.q} : Set
                (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField))) →
          Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
            (p.map a.hom) S.q r (hp.map a.hom) S.hq hr))) →
    ∃ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      DegreeTenGenericFirstResidualGeometry p hp a ha := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  intro havoid hselected
  exact exists_degreeTenGenericFirstResidualGeometry_of_smooth_cubic_of_closedPoint_of_selectedAvoidance
    p hp hp0 x hx (fun a ha => by
      obtain ⟨S, htransverse⟩ := hselected a ha
      exact ⟨S, GenericDegreeTenThirdCubicAvoidance.selectedAvoidance
        p hp havoid a ha S, htransverse⟩)

theorem exists_degreeTenGenericFirstResidualGeometry_of_smooth_cubic_of_closedPoint_of_selectedFinrankDrop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    : letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
    (∀
      (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      ∃ S : DegreeTenRegularCubicSectionEmbeddingData
          (p.map a.hom) (hp.map a.hom)
          (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha),
        DegreeTenRegularCubicSectionSelectedFinrankDrop
          (p.map a.hom) (hp.map a.hom)
          (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S ∧
        ∀ (r : MvPolynomial (Fin 4)
          (cubicConfigurationBase p hp 10).functionField) (hr : r.IsHomogeneous 3),
          (∀ y : MvPolynomial (Fin 4)
            (cubicConfigurationBase p hp 10).functionField,
            r * y ∈ Ideal.span ({p.map a.hom, S.q} : Set
              (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField)) →
              y ∈ Ideal.span ({p.map a.hom, S.q} : Set
                (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField))) →
          Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
            (p.map a.hom) S.q r (hp.map a.hom) S.hq hr))) →
    ∃ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      DegreeTenGenericFirstResidualGeometry p hp a ha := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  intro hselected
  obtain ⟨a, ha⟩ := exists_cubicConfigurationGenericBaseMap p hp 10
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  obtain ⟨S, hdrop, htransverse⟩ := hselected a ha
  obtain ⟨R, hRdegree, hRetale, hdisjoint⟩ :=
    exists_degreeTenResidual_and_toBase_etale_and_disjoint_at_genericConfiguration_of_selectedFinrankDrop
      p hp hp0 a ha S hdrop htransverse
  exact ⟨a, ha, S.completion, R, hRdegree, hRetale, hdisjoint⟩

/-- The first generic residual needs the base-locus estimate only for the
regular cubic section selected from the smooth surface.  Combining that
estimate with the transverse-complete-intersection assertion produces the
selected three-cubic datum internally, before taking the degree-eleven
residual. -/
theorem exists_degreeTenGenericConfiguration_residual_and_toBase_etale_of_regularCubicSectionData_and_finrank_drop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    : letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
    (∀
      (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
      (S : DegreeTenRegularCubicSectionData (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)),
      DegreeTenCompletionThirdCubicFinrankDrop
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S.completion) →
    (∀
      (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (_ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      CubicTripleIntersectionTransverse (p.map a.hom) (hp.map a.hom)) →
    ∃ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
      (R : FiniteSubschemeDatum
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11),
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  intro hdrop htransverse
  obtain ⟨a, ha⟩ := exists_cubicConfigurationGenericBaseMap p hp 10
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  obtain ⟨S⟩ := nonempty_degreeTenRegularCubicSectionData_of_smooth_cubic
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
    (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)
  obtain ⟨T⟩ :=
    nonempty_degreeTenTransverseCubicIntersectionData_of_regularCubicSectionData_of_finrank_drop
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S
      (hdrop a ha S) (htransverse a ha)
  obtain ⟨R, hRdegree, hRetale⟩ :=
    exists_degreeTenResidualDatum_and_toBase_etale_of_transverseCubicIntersectionData
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) T
  exact ⟨a, ha, R, hRdegree, hRetale⟩

/-- A selected transverse three-cubic datum gives the generic first residual
without requiring a uniform transversality assertion for every possible
third cubic.  This is the exact existential form of the Bertini output used
in Voisin's argument: the datum retains the two cubics, their regularity,
their vanishing on the completed degree-sixteen scheme, and the étaleness of
the one resulting complete intersection. -/
theorem exists_degreeTenGenericConfiguration_residual_and_toBase_etale_of_selected_transverse_data
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    : letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
    (∀
      (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
      Nonempty (DegreeTenTransverseCubicIntersectionData
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha))) →
    ∃ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
      (R : FiniteSubschemeDatum
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11),
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  intro hselected
  obtain ⟨a, ha⟩ := exists_cubicConfigurationGenericBaseMap p hp 10
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  obtain ⟨T⟩ := hselected a ha
  obtain ⟨R, hRdegree, hRetale⟩ :=
    exists_degreeTenResidualDatum_and_toBase_etale_of_transverseCubicIntersectionData
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) T
  exact ⟨a, ha, R, hRdegree, hRetale⟩


theorem exists_degreeTenResidual_and_toBase_etale_and_disjoint_at_genericConfiguration_of_selectedThirdCubicData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    [Smooth (hypersurfaceToBase p hp)]
    (a : CommRingCat.of K ⟶
      CommRingCat.of (cubicConfigurationBase p hp 10).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
    : letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
      charZero_cubicConfigurationFunctionField_of_flat p hp 10
    letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
    ∀ (S : DegreeTenRegularCubicSectionEmbeddingData
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha))
    (T : DegreeTenRegularCubicSectionSelectedThirdCubicData
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S),
    ∃ R : FiniteSubschemeDatum
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11,
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R)) := by
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  intro S T
  exact exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_selectedThirdCubicData
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
    (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S T

/-- For the generic degree-ten configuration, an integral intersection of
the first two cubics and one chosen transverse third cubic already produce
the finite-etale degree-eleven residual.  This is the direct first-residual
form of Voisin's selected Bertini input: it does not require transversality
for every regular member of the cubic system. -/
theorem exists_degreeTenResidual_and_toBase_etale_and_disjoint_at_genericConfiguration_of_primeIntermediate_and_selectedThirdCubic
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    [Smooth (hypersurfaceToBase p hp)]
    (a : CommRingCat.of K ⟶
      CommRingCat.of (cubicConfigurationBase p hp 10).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
    (S : DegreeTenRegularCubicSectionEmbeddingData
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha))
    (hprime : (Ideal.span ({p.map a.hom, S.q} : Set
      (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField))).IsPrime)
    (r : MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField)
    (hr : r.IsHomogeneous 3)
    (hrnot : r ∉ Ideal.span ({p.map a.hom, S.q} : Set
      (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField)))
    (chart : DegreeTenRegularCubicSectionSelectedThirdCubicChart
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S r)
    (htransverse : Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map a.hom) S.q r (hp.map a.hom) S.hq hr))) :
    ∃ R : FiniteSubschemeDatum
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) 11,
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
        (finiteSubschemeDatumCycle
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R) = 11 ∧
      Etale (R.val.subschemeι ≫
        hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) S.completion.datum))
        (Set.range (finiteSubschemeDatumSpecMap
          (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R)) := by
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  let T := DegreeTenRegularCubicSectionSelectedThirdCubicData.ofPrimeIntermediate
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S hprime r hr hrnot chart htransverse
  exact exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_selectedThirdCubicData
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
    (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S T

/-- The concrete generic first-residual input supplied by Voisin's Lemma 3.3
and Bertini: one regular first cubic, an integral intermediate curve, and
one reduced third-cubic complete intersection through the completed
degree-sixteen datum.  Regularity makes this intersection finite, and in
characteristic zero reducedness then yields the étaleness used by the
residual calculation. -/
def DegreeTenGenericSelectedThirdCubicPrimeGeometry
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    (a : CommRingCat.of K ⟶
      CommRingCat.of (cubicConfigurationBase p hp 10).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10) : Prop :=
  ∃ S : DegreeTenRegularCubicSectionEmbeddingData
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha),
    (Ideal.span ({p.map a.hom, S.q} : Set
      (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField))).IsPrime ∧
    ∃ (r : MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField)
      (hr : r.IsHomogeneous 3),
      r ∉ Ideal.span ({p.map a.hom, S.q} : Set
        (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField)) ∧
      DegreeTenRegularCubicSectionSelectedThirdCubicChart
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S r ∧
      AlgebraicGeometry.IsReduced
        (scheme (tripleCompleteIntersectionHomogeneousIdeal
          (p.map a.hom) S.q r (hp.map a.hom) S.hq hr))

/-- The intrinsic version of the generic selected-cubic Bertini input.  Its
prime condition lives in the coordinate ring of the smooth cubic surface,
rather than in the ambient polynomial ring. -/
def DegreeTenGenericSelectedThirdCubicQuotientPrimeGeometry
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    (a : CommRingCat.of K ⟶
      CommRingCat.of (cubicConfigurationBase p hp 10).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10) : Prop :=
  ∃ S : DegreeTenRegularCubicSectionEmbeddingData
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha),
    Prime (Ideal.Quotient.mk
      (Ideal.span ({p.map a.hom} : Set
        (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField))) S.q) ∧
    ∃ (r : MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField)
      (hr : r.IsHomogeneous 3),
      r ∉ Ideal.span ({p.map a.hom, S.q} : Set
        (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField)) ∧
      DegreeTenRegularCubicSectionSelectedThirdCubicChart
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S r ∧
      AlgebraicGeometry.IsReduced
        (scheme (tripleCompleteIntersectionHomogeneousIdeal
          (p.map a.hom) S.q r (hp.map a.hom) S.hq hr))

/-- The prime-and-selected-cubic version of Voisin's first geometric input
already has the strong residual form used by the later two pencil steps. -/
theorem degreeTenGenericFirstResidualGeometry_of_primeSelectedThirdCubicGeometry
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    [Smooth (hypersurfaceToBase p hp)]
    (a : CommRingCat.of K ⟶
      CommRingCat.of (cubicConfigurationBase p hp 10).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
    (hgeometry : DegreeTenGenericSelectedThirdCubicPrimeGeometry p hp a ha) :
    DegreeTenGenericFirstResidualGeometry p hp a ha := by
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  obtain ⟨S, hprime, r, hr, hrnot, chart, hreduce⟩ := hgeometry
  have hregular : ∀ y : MvPolynomial (Fin 4)
      (cubicConfigurationBase p hp 10).functionField,
      r * y ∈ Ideal.span ({p.map a.hom, S.q} : Set
        (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField)) →
        y ∈ Ideal.span ({p.map a.hom, S.q} : Set
          (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField)) := by
    exact regular_mod_prime_ideal_of_not_mem
      (Ideal.span ({p.map a.hom, S.q} : Set
        (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField)))
      hprime hrnot
  let T := DegreeTenRegularCubicSectionSelectedThirdCubicData.ofReduced
    (p.map a.hom) (hp.map a.hom)
    (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S r hr hregular chart hreduce
  obtain ⟨R, hdegree, hetale, hdisjoint⟩ :=
    exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_selectedThirdCubicData
      (p.map a.hom) (hp.map a.hom)
      (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0)
      (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S T
  exact ⟨S.completion, R, hdegree, hetale, hdisjoint⟩

/-- The intrinsic coordinate-ring form of the selected Bertini conclusion
also gives the generic first residual.  Primality of the original cubic is
supplied by smoothness, and the quotient criterion reconstructs the prime
ambient cubic--cubic ideal used by the residual calculation. -/
theorem degreeTenGenericFirstResidualGeometry_of_quotientPrimeSelectedThirdCubicGeometry
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsIntegral (cubicConfigurationBase p hp 10)]
    [Smooth (hypersurfaceToBase p hp)]
    (a : CommRingCat.of K ⟶
      CommRingCat.of (cubicConfigurationBase p hp 10).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10)
    (hgeometry : DegreeTenGenericSelectedThirdCubicQuotientPrimeGeometry p hp a ha) :
    DegreeTenGenericFirstResidualGeometry p hp a ha := by
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  obtain ⟨S, hqprime, r, hr, hrnot, chart, hreduce⟩ := hgeometry
  have hpprime : (Ideal.span ({p.map a.hom} : Set
      (MvPolynomial (Fin 4) (cubicConfigurationBase p hp 10).functionField))).IsPrime :=
    principalIdeal_prime_of_irreducible_cubic (p.map a.hom)
      (irreducible_of_smooth_homogeneous_cubic_of_field (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationCoefficientChange_ne_zero p hp 10 a hp0))
  exact degreeTenGenericFirstResidualGeometry_of_primeSelectedThirdCubicGeometry
    p hp hp0 a ha
    ⟨S, ideal_span_pair_isPrime_of_quotient_mk_prime
      (p.map a.hom) S.q hpprime hqprime, r, hr, hrnot, chart, hreduce⟩

/- A point-specific wrapper for the quotient-prime selected Bertini input. -/
theorem exists_degreeTenGenericFirstResidualGeometry_of_smooth_cubic_of_closedPoint_of_quotientPrimeSelectedThirdCubicGeometry
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    : letI : IsIntegral (cubicConfigurationBase p hp 10) :=
        isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
      (∀ (a : CommRingCat.of K ⟶
          CommRingCat.of (cubicConfigurationBase p hp 10).functionField)
        (ha : Spec.map a =
          cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
        DegreeTenGenericSelectedThirdCubicQuotientPrimeGeometry p hp a ha) →
      ∃ (a : CommRingCat.of K ⟶
          CommRingCat.of (cubicConfigurationBase p hp 10).functionField)
        (ha : Spec.map a =
          cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
        DegreeTenGenericFirstResidualGeometry p hp a ha := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  intro hgeometry
  obtain ⟨a, ha⟩ := exists_cubicConfigurationGenericBaseMap p hp 10
  obtain ⟨S, hqprime, r, hr, hrnot, chart, _hred⟩ := hgeometry a ha
  exact ⟨a, ha,
    degreeTenGenericFirstResidualGeometry_of_quotientPrimeSelectedThirdCubicGeometry
      p hp hp0 a ha (hgeometry a ha)⟩

/-- Once Coray has supplied a degree-ten point, the selected prime cubic
geometry at its generic configuration supplies the strong first residual
needed by Voisin's remaining two pencil constructions. -/
theorem exists_degreeTenGenericFirstResidualGeometry_of_smooth_cubic_of_closedPoint_of_primeSelectedThirdCubicGeometry
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    : letI : IsIntegral (cubicConfigurationBase p hp 10) :=
        isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
      (∀ (a : CommRingCat.of K ⟶
          CommRingCat.of (cubicConfigurationBase p hp 10).functionField)
        (ha : Spec.map a =
          cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
        DegreeTenGenericSelectedThirdCubicPrimeGeometry p hp a ha) →
      ∃ (a : CommRingCat.of K ⟶
          CommRingCat.of (cubicConfigurationBase p hp 10).functionField)
        (ha : Spec.map a =
          cubicConfigurationGenericBaseMap p hp 10 ≫ cubicConfigurationToBase p hp 10),
        DegreeTenGenericFirstResidualGeometry p hp a ha := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_closedPoint p hp hp0 x 10 hx
  letI : Flat (toBase (equationIdeal p hp)) := inferInstance
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField := CharZero.infinite _
  intro hgeometry
  obtain ⟨a, ha⟩ := exists_cubicConfigurationGenericBaseMap p hp 10
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  exact ⟨a, ha,
    degreeTenGenericFirstResidualGeometry_of_primeSelectedThirdCubicGeometry
      p hp hp0 a ha (hgeometry a ha)⟩

end PfaffianDescent
