import PfaffianDescent.VoisinFlatGradedFibreIncidence
import PfaffianDescent.GrassmannianFrameProjectiveChartMember
import PfaffianDescent.VoisinDegreeEightFixedCurveScheme
import PfaffianDescent.VoisinRegularSequenceCriteria
import AllCharacteristics.ProjectiveClassifyingScalar

/-!
# Projective equation points on arbitrary flat-model fibres

The reverse incidence theorem for the global projective-frame family,
combined with the flat model's algebraic fibre incidence, shows that a
field-valued projective-family point represents an equation vanishing on
the corresponding base-changed model fibre.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K R S : Type u} [Field K] [CommRing R] [IsDomain R]
  [IsNoetherianRing R] [Algebra K R]
  [Field S] [Algebra R S] [Algebra K S] [IsScalarTower K R S]
  (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
  [Module.Flat R (CoordinateRing J)]
  (d r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) d)
  (hRank : ∀ x : PrimeSpectrum R,
    Module.rankAtStalk (grading J d) x = q)

omit [IsDomain R] [Algebra K R] [IsScalarTower K R S] in
/-- Every field-valued member of the specialized projective equation
family is a nonzero equation in the coefficient extension of the model
ideal. -/
theorem flatGradedProjectiveFibre_point_mem_extendedIdeal
    (t : let W := (grassmannianQuotientMap (algebraMap R S)
        (flatGradedGrassmannian J d r q e hRank))
      Spec (.of S) ⟶ grassmannianFrameProjectiveFamilyPullback K d e
        (grassmannianQuotientMorphism K W))
    (ht : let W := (grassmannianQuotientMap (algebraMap R S)
        (flatGradedGrassmannian J d r q e hRank))
      t ≫ grassmannianFrameProjectiveFamilyPullbackToBase K d e
        (grassmannianQuotientMorphism K W) = 𝟙 _) :
    let W := (grassmannianQuotientMap (algebraMap R S)
      (flatGradedGrassmannian J d r q e hRank))
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous d) (hp0 : p ≠ 0),
      p ∈ Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal ∧
      t ≫ grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e
          (grassmannianQuotientMorphism K W) =
        projectiveClassifyingMap p hp hp0 (RingHom.id S) ≫
          projectiveParametersCoefficientMap d (algebraMap K S) := by
  let W := grassmannianQuotientMap (algebraMap R S)
    (flatGradedGrassmannian J d r q e hRank)
  obtain ⟨p, hp, hp0, hmem, hparam⟩ :=
    exists_grassmannianFrameProjectiveFamilyPullback_equation e W t ht
  let E := grassmannianChartHomogeneousCoordinateEquiv (R := S) d e
  change (⟨p, hp⟩ : homogeneousSubmodule (Fin 4) S d) ∈
    W.toSubmodule.map E.toLinearMap at hmem
  obtain ⟨x, hx, hpx⟩ := hmem
  have hxIdeal := flatGradedGrassmannian_quotientMap_mem_extendedIdeal
    J d r q e hRank x hx
  have hpIdeal : p ∈
      Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal := by
    have heq : (E x).1 = p := congrArg Subtype.val hpx
    rw [← heq]
    exact hxIdeal
  exact ⟨p, hp, hp0, hpIdeal, hparam⟩

omit [IsDomain R] in
/-- Every field-valued point of an arbitrary fibre of the original flat
projective equation family represents a nonzero equation in the extended
model ideal. -/
theorem flatGradedProjectiveFamily_fibrePoint_mem_extendedIdeal
    (t : let W := flatGradedGrassmannian J d r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      Spec (.of S) ⟶ pullback
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g)
    (ht : let W := flatGradedGrassmannian J d r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      t ≫ pullback.snd
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g = 𝟙 _) :
    let W := flatGradedGrassmannian J d r q e hRank
    let f := grassmannianQuotientMorphism K W
    let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous d) (hp0 : p ≠ 0),
      p ∈ Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal ∧
      t ≫ pullback.fst
          (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g ≫
          grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e f =
        projectiveClassifyingMap p hp hp0 (RingHom.id S) ≫
          projectiveParametersCoefficientMap d (algebraMap K S) := by
  let W := flatGradedGrassmannian J d r q e hRank
  let f := grassmannianQuotientMorphism K W
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let V := grassmannianQuotientMap (algebraMap R S) W
  have hgeneric : g ≫ f = grassmannianQuotientMorphism K V := by
    exact grassmannianQuotientMorphism_naturality K W
      (IsScalarTower.toAlgHom K R S)
  let B := grassmannianFrameProjectiveFamilyPullback_baseChangeIso K d e f g
  let sRaw := t ≫ B.hom
  let s := grassmannianFrameProjectiveFamilyPullbackPointCast
    K d e hgeneric sRaw
  have hsBase : s ≫ grassmannianFrameProjectiveFamilyPullbackToBase K d e
      (grassmannianQuotientMorphism K V) = 𝟙 _ := by
    calc
      s ≫ grassmannianFrameProjectiveFamilyPullbackToBase K d e
          (grassmannianQuotientMorphism K V) =
        sRaw ≫ grassmannianFrameProjectiveFamilyPullbackToBase K d e
          (g ≫ f) :=
        grassmannianFrameProjectiveFamilyPullbackPointCast_toBase
          K d e hgeneric sRaw
      _ = t ≫ pullback.snd
          (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g := by
        change (t ≫ B.hom) ≫ _ = _
        rw [Category.assoc]
        exact congrArg (fun z => t ≫ z)
          (pullbackLeftPullbackSndIso_hom_snd
            (grassmannianFrameProjectiveToGrassmannian K d e) f g)
      _ = 𝟙 _ := ht
  obtain ⟨p, hp, hp0, hpIdeal, hparam⟩ :=
    flatGradedProjectiveFibre_point_mem_extendedIdeal
      (K := K) J d r q e hRank s hsBase
  refine ⟨p, hp, hp0, hpIdeal, ?_⟩
  have hBParam : B.hom ≫
      grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e
        (g ≫ f) =
      pullback.fst (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g ≫
        grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e f :=
    grassmannianFrameProjectiveFamilyPullback_baseChangeIso_toGlobalParameters
      K d e f g
  calc
    t ≫ pullback.fst
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g ≫
        grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e f =
      t ≫ (B.hom ≫
        grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e
          (g ≫ f)) := by rw [hBParam]
    _ = sRaw ≫ grassmannianFrameProjectiveFamilyPullbackToGlobalParameters
          K d e (g ≫ f) := (Category.assoc _ _ _).symm
    _ = s ≫ grassmannianFrameProjectiveFamilyPullbackToGlobalParameters
          K d e (grassmannianQuotientMorphism K V) :=
      (grassmannianFrameProjectiveFamilyPullbackPointCast_toGlobalParameters
        K d e hgeneric sRaw).symm
    _ = _ := hparam

omit [IsDomain R] in
/-- If the extended model ideal defines the chosen fibre, every point of
its projective equation family represents a nonzero equation of that
fibre. -/
theorem flatGradedProjectiveFamily_fibrePoint_mem_fibreIdeal
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hmap : Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal = C.toIdeal)
    (t : let W := flatGradedGrassmannian J d r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      Spec (.of S) ⟶ pullback
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g)
    (ht : let W := flatGradedGrassmannian J d r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      t ≫ pullback.snd
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g = 𝟙 _) :
    let W := flatGradedGrassmannian J d r q e hRank
    let f := grassmannianQuotientMorphism K W
    let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous d) (hp0 : p ≠ 0),
      p ∈ C.toIdeal ∧
      t ≫ pullback.fst
          (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g ≫
          grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e f =
        projectiveClassifyingMap p hp hp0 (RingHom.id S) ≫
          projectiveParametersCoefficientMap d (algebraMap K S) := by
  obtain ⟨p, hp, hp0, hpIdeal, hparam⟩ :=
    flatGradedProjectiveFamily_fibrePoint_mem_extendedIdeal
      (K := K) J d r q e hRank t ht
  exact ⟨p, hp, hp0, hmap ▸ hpIdeal, hparam⟩

omit [IsDomain R] in
/-- The equation represented by a projective-family point contains the
chosen fibre as an actual closed projective subscheme. Its ambient map is
the canonical projective realization of the fibre. -/
theorem flatGradedProjectiveFamily_fibrePoint_closedIntoMember
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hmap : Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal = C.toIdeal)
    (t : let W := flatGradedGrassmannian J d r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      Spec (.of S) ⟶ pullback
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g)
    (ht : let W := flatGradedGrassmannian J d r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      t ≫ pullback.snd
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g = 𝟙 _) :
    let W := flatGradedGrassmannian J d r q e hRank
    let f := grassmannianQuotientMorphism K W
    let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous d) (hp0 : p ≠ 0)
      (j : scheme C ⟶ hypersurface p hp),
      IsClosedImmersion j ∧
      j ≫ hypersurfaceToAmbient p hp = quotientProjMap C ∧
      t ≫ pullback.fst
          (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g ≫
          grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e f =
        projectiveClassifyingMap p hp hp0 (RingHom.id S) ≫
          projectiveParametersCoefficientMap d (algebraMap K S) := by
  obtain ⟨p, hp, hp0, hpC, hparam⟩ :=
    flatGradedProjectiveFamily_fibrePoint_mem_fibreIdeal
      (K := K) J d r q e hRank C hmap t ht
  let j := homogeneousFixedCurveToHypersurface p hp C hpC
  exact ⟨p, hp, hp0, j,
    homogeneousFixedCurveToHypersurface_closedImmersion p hp C hpC,
    homogeneousFixedCurveToHypersurface_comp_hypersurfaceToAmbient p hp C hpC,
    hparam⟩

omit [IsDomain R] in
/-- On an integral cubic surface, every represented fibre equation either
vanishes identically on the surface or is a non-zero-divisor in the
surface's homogeneous coordinate ring. The latter is the algebraic
regularity condition required for its hypersurface section to be a
Cartier divisor. -/
theorem flatGradedProjectiveFamily_fibrePoint_regularOrSurfaceEquation
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hmap : Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal = C.toIdeal)
    (a : MvPolynomial (Fin 4) S)
    (haPrime : (Ideal.span ({a} : Set (MvPolynomial (Fin 4) S))).IsPrime)
    (t : let W := flatGradedGrassmannian J d r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      Spec (.of S) ⟶ pullback
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g)
    (ht : let W := flatGradedGrassmannian J d r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      t ≫ pullback.snd
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g = 𝟙 _) :
    let W := flatGradedGrassmannian J d r q e hRank
    let f := grassmannianQuotientMorphism K W
    let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous d) (hp0 : p ≠ 0),
      p ∈ C.toIdeal ∧
      (p ∈ Ideal.span ({a} : Set (MvPolynomial (Fin 4) S)) ∨
        ∀ x : MvPolynomial (Fin 4) S,
          p * x ∈ Ideal.span ({a} : Set (MvPolynomial (Fin 4) S)) →
          x ∈ Ideal.span ({a} : Set (MvPolynomial (Fin 4) S))) ∧
      t ≫ pullback.fst
          (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g ≫
          grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e f =
        projectiveClassifyingMap p hp hp0 (RingHom.id S) ≫
          projectiveParametersCoefficientMap d (algebraMap K S) := by
  obtain ⟨p, hp, hp0, hpC, hparam⟩ :=
    flatGradedProjectiveFamily_fibrePoint_mem_fibreIdeal
      (K := K) J d r q e hRank C hmap t ht
  refine ⟨p, hp, hp0, hpC, ?_, hparam⟩
  by_cases htrivial : p ∈ Ideal.span ({a} : Set (MvPolynomial (Fin 4) S))
  · exact Or.inl htrivial
  · exact Or.inr (regular_mod_ideal_of_isPrime_not_mem
      (Ideal.span ({a} : Set (MvPolynomial (Fin 4) S))) haPrime htrivial)

omit [IsDomain R] in
/-- Smoothness of the cubic surface supplies the prime-ideal hypothesis
in the regular-or-trivial alternative for every field-valued fibre point. -/
theorem flatGradedProjectiveFamily_fibrePoint_regularOrSurfaceEquation_of_smooth
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hmap : Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal = C.toIdeal)
    (a : MvPolynomial (Fin 4) S) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase a ha)]
    (t : let W := flatGradedGrassmannian J d r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      Spec (.of S) ⟶ pullback
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g)
    (ht : let W := flatGradedGrassmannian J d r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      t ≫ pullback.snd
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g = 𝟙 _) :
    let W := flatGradedGrassmannian J d r q e hRank
    let f := grassmannianQuotientMorphism K W
    let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous d) (hp0 : p ≠ 0),
      p ∈ C.toIdeal ∧
      (p ∈ Ideal.span ({a} : Set (MvPolynomial (Fin 4) S)) ∨
        ∀ x : MvPolynomial (Fin 4) S,
          p * x ∈ Ideal.span ({a} : Set (MvPolynomial (Fin 4) S)) →
          x ∈ Ideal.span ({a} : Set (MvPolynomial (Fin 4) S))) ∧
      t ≫ pullback.fst
          (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g ≫
          grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e f =
        projectiveClassifyingMap p hp hp0 (RingHom.id S) ≫
          projectiveParametersCoefficientMap d (algebraMap K S) := by
  exact flatGradedProjectiveFamily_fibrePoint_regularOrSurfaceEquation
    (K := K) J d r q e hRank C hmap a
    (principalIdeal_prime_of_smooth_homogeneous_cubic a ha ha0) t ht

set_option backward.isDefEq.respectTransparency false

omit [IsDomain R] in
/-- Nontriviality can be stated intrinsically in ambient projective
parameter space: a point whose parameter differs from the class of the
surface equation represents a regular equation modulo the surface ideal.
This avoids a choice of polynomial representative in the hypothesis. -/
theorem flatGradedProjectiveFamily_fibrePoint_regular_of_parameter_ne_surface
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
    (hmap : Ideal.map (MvPolynomial.map (algebraMap R S)) J.toIdeal = C.toIdeal)
    (a : MvPolynomial (Fin 4) S) (ha : a.IsHomogeneous d) (ha0 : a ≠ 0)
    (haPrime : (Ideal.span ({a} : Set (MvPolynomial (Fin 4) S))).IsPrime)
    (t : let W := flatGradedGrassmannian J d r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      Spec (.of S) ⟶ pullback
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g)
    (ht : let W := flatGradedGrassmannian J d r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      t ≫ pullback.snd
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g = 𝟙 _)
    (hnontrivial : let W := flatGradedGrassmannian J d r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
      t ≫ pullback.fst
          (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g ≫
          grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e f ≠
        projectiveClassifyingMap a ha ha0 (RingHom.id S) ≫
          projectiveParametersCoefficientMap d (algebraMap K S)) :
    let W := flatGradedGrassmannian J d r q e hRank
    let f := grassmannianQuotientMorphism K W
    let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
    ∃ (p : MvPolynomial (Fin 4) S) (hp : p.IsHomogeneous d) (hp0 : p ≠ 0),
      p ∈ C.toIdeal ∧
      (∀ x : MvPolynomial (Fin 4) S,
        p * x ∈ Ideal.span ({a} : Set (MvPolynomial (Fin 4) S)) →
        x ∈ Ideal.span ({a} : Set (MvPolynomial (Fin 4) S))) ∧
      t ≫ pullback.fst
          (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g ≫
          grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e f =
        projectiveClassifyingMap p hp hp0 (RingHom.id S) ≫
          projectiveParametersCoefficientMap d (algebraMap K S) := by
  obtain ⟨p, hp, hp0, hpC, hchoice, hparam⟩ :=
    flatGradedProjectiveFamily_fibrePoint_regularOrSurfaceEquation
      (K := K) J d r q e hRank C hmap a haPrime t ht
  refine ⟨p, hp, hp0, hpC, ?_, hparam⟩
  rcases hchoice with htrivial | hregular
  · obtain ⟨c, hc⟩ := homogeneous_dvd_same_degree_eq_smul
      ha hp ha0 hp0 (Ideal.mem_span_singleton.mp htrivial)
    have hc0 : c ≠ 0 := by
      intro hc0
      apply hp0
      rw [hc, hc0, zero_smul]
    have hclass : projectiveClassifyingMap p hp hp0 (RingHom.id S) =
        projectiveClassifyingMap a ha ha0 (RingHom.id S) := by
      have hscale : p = MvPolynomial.C c * a := by
        simpa only [smul_eq_C_mul] using hc
      have hscaled0 : MvPolynomial.C c * a ≠ 0 := by
        simpa only [smul_eq_C_mul] using (hscale ▸ hp0)
      have hscaledClass :=
        projectiveClassifyingMap_C_mul (RingHom.id S) a c hc0 ha ha0 hscaled0
      simpa only [hscale] using hscaledClass
    exact False.elim (hnontrivial (hparam.trans
      (congrArg (fun z => z ≫ projectiveParametersCoefficientMap d
        (algebraMap K S)) hclass)))
  · exact hregular

end PfaffianDescent
