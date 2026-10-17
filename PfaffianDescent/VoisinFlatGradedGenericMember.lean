import PfaffianDescent.VoisinFlatGradedGrassmannian
import PfaffianDescent.GrassmannianFrameProjectiveFieldPoint
import PfaffianDescent.GrassmannianFrameProjectiveChartMember

/-!
# Generic members of the flat projective equation family

A nonzero homogeneous equation of the prescribed function-field curve is
represented by a field-valued point of the generic fibre of the flat
model's projective equation family.  The ambient projective parameter of
that point represents a nonzero scalar multiple of the equation, so it
still belongs to the curve's homogeneous ideal.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

private theorem projectiveFamilyBaseChangeIso_inv_toBase
    {K : Type u} [CommRing K] {m n : ℕ}
    {τ : Type} [Finite τ] (d : ℕ)
    (e : Fin (m + n) ≃ Monomials τ d)
    {X Y : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) (g : Y ⟶ X) :
    (grassmannianFrameProjectiveFamilyPullback_baseChangeIso K d e f g).inv ≫
      pullback.snd
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g =
      grassmannianFrameProjectiveFamilyPullbackToBase K d e (g ≫ f) := by
  change (pullbackLeftPullbackSndIso
      (grassmannianFrameProjectiveToGrassmannian K d e) f g).inv ≫
      pullback.snd _ _ = pullback.snd _ _
  exact pullbackLeftPullbackSndIso_inv_snd_snd
    (grassmannianFrameProjectiveToGrassmannian K d e) f g

variable {K R F : Type u} [Field K] [CommRing R] [IsDomain R]
  [IsNoetherianRing R] [Algebra K R] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra K F]
  [IsScalarTower K R F]
  (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
  [Module.Flat R (CoordinateRing J)]
  (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
  (hJ : J.toIdeal =
    Ideal.comap (MvPolynomial.map (algebraMap R F)) C.toIdeal)
  (d : ℕ)

include hJ in
/-- A nonzero generic equation is represented by an actual point of the
generic fibre of the flat model's projective equation family.  The point's
ambient polynomial remains in the generic ideal. -/
theorem exists_flatGradedProjectiveFamily_genericMember
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J d) x =
        Module.finrank F (grading C d))
    (v : homogeneousIdealPiece C d) (hv : v ≠ 0) :
    let r := Module.finrank F (homogeneousIdealPiece C d)
    let q := Module.finrank F (grading C d)
    let e := fixedCurveGraded_monomialEquiv d C
    let W := flatGradedGrassmannian J d r q e hRank
    let f := grassmannianQuotientMorphism K W
    let g := Spec.map (CommRingCat.ofHom (algebraMap R F))
    ∃ (t : Spec (.of F) ⟶ pullback
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g)
      (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous d)
      (hp0 : p ≠ 0) (alpha : F),
      alpha ≠ 0 ∧ p = MvPolynomial.C alpha * v.1.1 ∧
      p ∈ C.toIdeal ∧
      t ≫ pullback.snd
          (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g = 𝟙 _ ∧
      t ≫ pullback.fst
          (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g ≫
          grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e f =
        projectiveClassifyingMap p hp hp0 (RingHom.id F) ≫
          projectiveParametersCoefficientMap d (algebraMap K F) := by
  let r := Module.finrank F (homogeneousIdealPiece C d)
  let q := Module.finrank F (grading C d)
  let e := fixedCurveGraded_monomialEquiv d C
  let W := flatGradedGrassmannian J d r q e hRank
  let f := grassmannianQuotientMorphism K W
  let g := Spec.map (CommRingCat.ofHom (algebraMap R F))
  let V := fixedCurveGradedGrassmannian d r q e C rfl
  have hvCoord :
      (grassmannianChartHomogeneousCoordinateEquiv (R := F) d e).symm v.1 ∈
        V.toSubmodule := by
    change (grassmannianChartHomogeneousCoordinateEquiv (R := F) d e)
      ((grassmannianChartHomogeneousCoordinateEquiv (R := F) d e).symm v.1) ∈
        homogeneousIdealPiece C d
    simpa using v.2
  have hv0 : (v.1 : homogeneousSubmodule (Fin 4) F d) ≠ 0 := by
    intro h
    apply hv
    exact Subtype.ext h
  obtain ⟨s, p, hp, hp0, alpha, halpha, hscale, hsbase, hsparam⟩ :=
    exists_grassmannianFrameProjectiveFamilyPullback_point_of_mem
      (K := K) e V v.1 hvCoord hv0
  have hgeneric : g ≫ f = grassmannianQuotientMorphism K V :=
    flatGradedGrassmannianMorphism_generic_eq_fixedCurve
      J d r q e C hJ hRank rfl
  let B := grassmannianFrameProjectiveFamilyPullback_baseChangeIso K d e f g
  let sRaw := grassmannianFrameProjectiveFamilyPullbackPointCast
    K d e hgeneric.symm s
  let t := sRaw ≫ B.inv
  have hpC : p ∈ C.toIdeal := by
    rw [hscale]
    have hvC : v.1.1 ∈ C.toIdeal :=
      (mem_homogeneousIdealPiece_iff C d v.1).mp v.2
    exact C.toIdeal.mul_mem_left _ hvC
  have htbase : t ≫ pullback.snd
      (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g = 𝟙 _ := by
    calc
      t ≫ pullback.snd
          (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g =
        sRaw ≫ grassmannianFrameProjectiveFamilyPullbackToBase K d e
          (g ≫ f) := by
            change (sRaw ≫ B.inv) ≫ _ = _
            rw [Category.assoc,
              projectiveFamilyBaseChangeIso_inv_toBase d e f g]
      _ = s ≫ grassmannianFrameProjectiveFamilyPullbackToBase K d e
          (grassmannianQuotientMorphism K V) :=
        grassmannianFrameProjectiveFamilyPullbackPointCast_toBase
          K d e hgeneric.symm s
      _ = 𝟙 _ := hsbase
  refine ⟨t, p, hp, hp0, alpha, halpha, hscale, hpC, htbase, ?_⟩
  have hparam : B.hom ≫
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
      t ≫ (pullback.fst
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g ≫
        grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e f) :=
          Category.assoc _ _ _
    _ = t ≫ (B.hom ≫
        grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e
          (g ≫ f)) := by rw [hparam]
    _ = sRaw ≫ grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e
          (g ≫ f) := by
        rw [← Category.assoc]
        simpa only [t] using congrArg
          (fun z => z ≫ grassmannianFrameProjectiveFamilyPullbackToGlobalParameters
            K d e (g ≫ f)) (by simp : (sRaw ≫ B.inv) ≫ B.hom = sRaw)
    _ = s ≫ grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e
          (grassmannianQuotientMorphism K V) :=
      grassmannianFrameProjectiveFamilyPullbackPointCast_toGlobalParameters
        K d e hgeneric.symm s
    _ = _ := hsparam

include hJ in
/-- Every field-valued point of the generic fibre of the flat model's
projective equation family represents a nonzero equation of the prescribed
function-field curve. -/
theorem flatGradedProjectiveFamily_genericPoint_mem_ideal
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J d) x =
        Module.finrank F (grading C d))
    (t : let r := Module.finrank F (homogeneousIdealPiece C d)
      let q := Module.finrank F (grading C d)
      let e := fixedCurveGraded_monomialEquiv d C
      let W := flatGradedGrassmannian J d r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R F))
      Spec (.of F) ⟶ pullback
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g)
    (ht : let r := Module.finrank F (homogeneousIdealPiece C d)
      let q := Module.finrank F (grading C d)
      let e := fixedCurveGraded_monomialEquiv d C
      let W := flatGradedGrassmannian J d r q e hRank
      let f := grassmannianQuotientMorphism K W
      let g := Spec.map (CommRingCat.ofHom (algebraMap R F))
      t ≫ pullback.snd
        (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g = 𝟙 _) :
    let r := Module.finrank F (homogeneousIdealPiece C d)
    let q := Module.finrank F (grading C d)
    let e := fixedCurveGraded_monomialEquiv d C
    let W := flatGradedGrassmannian J d r q e hRank
    let f := grassmannianQuotientMorphism K W
    let g := Spec.map (CommRingCat.ofHom (algebraMap R F))
    ∃ (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous d) (hp0 : p ≠ 0),
      p ∈ C.toIdeal ∧
      t ≫ pullback.fst
          (grassmannianFrameProjectiveFamilyPullbackToBase K d e f) g ≫
          grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e f =
        projectiveClassifyingMap p hp hp0 (RingHom.id F) ≫
          projectiveParametersCoefficientMap d (algebraMap K F) := by
  let r := Module.finrank F (homogeneousIdealPiece C d)
  let q := Module.finrank F (grading C d)
  let e := fixedCurveGraded_monomialEquiv d C
  let W := flatGradedGrassmannian J d r q e hRank
  let f := grassmannianQuotientMorphism K W
  let g := Spec.map (CommRingCat.ofHom (algebraMap R F))
  let V := fixedCurveGradedGrassmannian d r q e C rfl
  have hgeneric : g ≫ f = grassmannianQuotientMorphism K V :=
    flatGradedGrassmannianMorphism_generic_eq_fixedCurve
      J d r q e C hJ hRank rfl
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
  obtain ⟨p, hp, hp0, hmem, hparam⟩ :=
    exists_grassmannianFrameProjectiveFamilyPullback_equation e V s hsBase
  have hpC : p ∈ C.toIdeal := by
    change (⟨p, hp⟩ : homogeneousSubmodule (Fin 4) F d) ∈
      ((homogeneousIdealPiece C d).comap
        (grassmannianChartHomogeneousCoordinateEquiv (R := F) d e).toLinearMap).map
        (grassmannianChartHomogeneousCoordinateEquiv (R := F) d e).toLinearMap at hmem
    rw [Submodule.map_comap_eq_of_surjective
      (grassmannianChartHomogeneousCoordinateEquiv (R := F) d e).surjective] at hmem
    exact (mem_homogeneousIdealPiece_iff C d _).mp hmem
  refine ⟨p, hp, hp0, hpC, ?_⟩
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

end PfaffianDescent
