import PfaffianDescent.VoisinFlatQuadraticGrassmannian
import PfaffianDescent.VoisinPolynomialGenericSpreading
import PfaffianDescent.GrassmannianQuotientNaturality

/-!
# Generic fibre of the homogeneous equation modules

Clearing denominators identifies the fraction-field span of the equations
of a contracted homogeneous model with the equations of its generic fibre,
degree by degree.
-/

namespace PfaffianDescent

open MvPolynomial
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {R F : Type u} [CommRing R] [IsDomain R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
  (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
  (hJ : J.toIdeal =
    Ideal.comap (MvPolynomial.map (algebraMap R F)) C.toIdeal)
  (n : ℕ)

/-- Map a homogeneous equation over the model base to the corresponding
homogeneous polynomial over the fraction field. -/
noncomputable def genericIdealPiecePolynomialMap
    (x : homogeneousModelIdealPiece J n) :
    homogeneousSubmodule (Fin 4) F n :=
  ⟨MvPolynomial.map (algebraMap R F) x.1.1, x.1.2.map _⟩

include hJ in
/-- The degree-`n` equations of the generic curve are exactly the
fraction-field span of the degree-`n` equations of the contracted model. -/
theorem genericIdealPiece_span_eq :
    Submodule.span F
      (Set.range (genericIdealPiecePolynomialMap (F := F) J n)) =
      homogeneousModelIdealPiece C n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    apply (mem_homogeneousModelIdealPiece_iff C n _).mpr
    change MvPolynomial.map (algebraMap R F) x.1.1 ∈ C.toIdeal
    have hxJ : x.1.1 ∈ J.toIdeal :=
      (mem_homogeneousModelIdealPiece_iff J n x.1).mp x.2
    rw [hJ] at hxJ
    exact hxJ
  · intro y hy
    have hyC : y.1 ∈ C.toIdeal :=
      (mem_homogeneousModelIdealPiece_iff C n y).mp hy
    obtain ⟨d, g, hd, hg⟩ :=
      exists_polynomial_denominator_clear (A := R) (F := F) y.1
    have hgHom : g.IsHomogeneous n :=
      polynomial_denominator_clear_isHomogeneous y.1 g d n y.2 hg
    have hgJ : g ∈ J.toIdeal := by
      rw [hJ]
      change MvPolynomial.map (algebraMap R F) g ∈ C.toIdeal
      rw [hg]
      exact C.toIdeal.mul_mem_left _ hyC
    let x : homogeneousModelIdealPiece J n :=
      ⟨⟨g, hgHom⟩,
        (mem_homogeneousModelIdealPiece_iff J n ⟨g, hgHom⟩).mpr hgJ⟩
    have hxspan : genericIdealPiecePolynomialMap (F := F) J n x ∈
        Submodule.span F (Set.range (genericIdealPiecePolynomialMap (F := F) J n)) :=
      Submodule.subset_span ⟨x, rfl⟩
    have hdF : algebraMap R F d ≠ 0 := by
      simpa using (IsFractionRing.injective R F).ne hd
    have hyx : y = (algebraMap R F d)⁻¹ •
        genericIdealPiecePolynomialMap (F := F) J n x := by
      apply Subtype.ext
      change y.1 = (algebraMap R F d)⁻¹ •
        MvPolynomial.map (algebraMap R F) g
      rw [hg, ← MvPolynomial.smul_eq_C_mul, smul_smul,
        inv_mul_cancel₀ hdF, one_smul]
    rw [hyx]
    exact Submodule.smul_mem _ _ hxspan

include hJ in
/-- The generic fibre of the flat quadratic Grassmannian submodule is the
original curve's quadratic equation space in the same monomial coordinates. -/
theorem flatQuadraticGrassmannian_generic_submodule
    [IsNoetherianRing R] [Module.Flat R (CoordinateRing J)]
    (r : ℕ) (hr : r ≤ 10)
    (hRank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (grading J 2) p = 10 - r) :
    let e := quadraticGrassmannianMonomialEquiv r hr
    grassmannianSubmoduleBaseChange (algebraMap R F)
      (flatQuadraticGrassmannian J r hr hRank).toSubmodule =
      (homogeneousModelIdealPiece C 2).comap
        (grassmannianChartHomogeneousCoordinateEquiv (R := F) 2 e).toLinearMap := by
  let e := quadraticGrassmannianMonomialEquiv r hr
  let ER := grassmannianChartHomogeneousCoordinateEquiv (R := R) 2 e
  let EF := grassmannianChartHomogeneousCoordinateEquiv (R := F) 2 e
  let W := flatQuadraticGrassmannian J r hr hRank
  have hW : W.toSubmodule =
      (homogeneousModelIdealPiece J 2).comap ER.toLinearMap :=
    flatQuadraticGrassmannian_toSubmodule J r hr hRank
  have hgenericMap (x : homogeneousModelIdealPiece J 2) :
      homogeneousSubmoduleBaseChange 2 (algebraMap R F) x.1 =
        genericIdealPiecePolynomialMap (F := F) J 2 x := rfl
  have hset : EF '' (graphCoefficientMap (algebraMap R F) ''
      (W.toSubmodule : Set ((Fin r → R) × (Fin (10 - r) → R)))) =
      Set.range (genericIdealPiecePolynomialMap (F := F) J 2) := by
    ext z
    constructor
    · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
      have hwJ : ER w ∈ homogeneousModelIdealPiece J 2 := by
        rw [hW] at hw
        exact hw
      let x : homogeneousModelIdealPiece J 2 := ⟨ER w, hwJ⟩
      refine ⟨x, ?_⟩
      change genericIdealPiecePolynomialMap (F := F) J 2 x =
        EF (graphCoefficientMap (algebraMap R F) w)
      rw [← hgenericMap x]
      exact grassmannianChartHomogeneousCoordinateEquiv_baseChange
        (R := R) 2 (algebraMap R F) e w
    · rintro ⟨x, rfl⟩
      let w := ER.symm x.1
      have hw : w ∈ W.toSubmodule := by
        rw [hW]
        change ER w ∈ homogeneousModelIdealPiece J 2
        simpa only [w, ER.apply_symm_apply] using x.2
      refine ⟨graphCoefficientMap (algebraMap R F) w,
        ⟨w, hw, rfl⟩, ?_⟩
      change EF (graphCoefficientMap (algebraMap R F) w) =
        genericIdealPiecePolynomialMap (F := F) J 2 x
      rw [← grassmannianChartHomogeneousCoordinateEquiv_baseChange
        (R := R) 2 (algebraMap R F) e w]
      rw [show ER w = x.1 from ER.apply_symm_apply x.1]
      exact hgenericMap x
  have hmap : (grassmannianSubmoduleBaseChange (algebraMap R F)
      W.toSubmodule).map EF.toLinearMap = homogeneousModelIdealPiece C 2 := by
    rw [grassmannianSubmoduleBaseChange, Submodule.map_span]
    change Submodule.span F (EF ''
      (graphCoefficientMap (algebraMap R F) ''
        (W.toSubmodule : Set ((Fin r → R) × (Fin (10 - r) → R))))) = _
    rw [hset]
    exact genericIdealPiece_span_eq J C hJ 2
  have h := congrArg (fun S : Submodule F
      (homogeneousSubmodule (Fin 4) F 2) => S.comap EF.toLinearMap) hmap
  simpa only [Submodule.comap_map_eq_of_injective EF.injective] using h

/-- For a homogeneous ideal over a field, the kernel description of its
equation piece agrees with the direct ideal-intersection description. -/
theorem homogeneousModelIdealPiece_eq_homogeneousIdealPiece
    (D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) (m : ℕ) :
    homogeneousModelIdealPiece D m = homogeneousIdealPiece D m := by
  ext x
  rw [mem_homogeneousModelIdealPiece_iff, mem_homogeneousIdealPiece_iff]

/-- The dimensions of the quadratic equations and their quotient add to
the ten-dimensional ambient quadratic space. -/
theorem homogeneousIdealPiece_quadratic_finrank_eq_complement
    (D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) :
    Module.finrank F (homogeneousIdealPiece D 2) =
      10 - Module.finrank F (grading D 2) := by
  let H := homogeneousSubmodule (Fin 4) F 2
  let q := homogeneousCoordinateQuotientMap D 2
  letI : Module.Finite F H :=
    Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg (Fin 4) F 2)
  have hquot : Module.finrank F (H ⧸ q.ker) =
      Module.finrank F (grading D 2) :=
    (q.quotKerEquivOfSurjective
      (homogeneousCoordinateQuotientMap_surjective D 2)).finrank_eq
  have hadd := q.ker.finrank_quotient_add_finrank
  have hamb : Module.finrank F H = 10 := by
    rw [four_variable_homogeneous_finrank]
    decide
  have hsum : Module.finrank F (grading D 2) + Module.finrank F q.ker = 10 := by
    rw [← hquot, ← hamb]
    exact hadd
  rw [← homogeneousModelIdealPiece_eq_homogeneousIdealPiece D 2]
  change Module.finrank F q.ker = 10 - Module.finrank F (grading D 2)
  omega

include hJ in
/-- After base change to the fraction field, the Grassmannian point of
the flat quadratic model is literally the point of the original generic
curve's quadratic system. -/
theorem flatQuadraticGrassmannian_generic_eq_fixedCurve
    [IsNoetherianRing R] [Module.Flat R (CoordinateRing J)]
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (grading J 2) p =
        10 - Module.finrank F (homogeneousIdealPiece C 2)) :
    let r := Module.finrank F (homogeneousIdealPiece C 2)
    let hr := quadraticSubmodule_finrank_le_ten F (homogeneousIdealPiece C 2)
    grassmannianQuotientMap (algebraMap R F)
      (flatQuadraticGrassmannian J r hr hrank) =
      fixedCurveQuadraticGrassmannian F C := by
  let r := Module.finrank F (homogeneousIdealPiece C 2)
  let hr := quadraticSubmodule_finrank_le_ten F (homogeneousIdealPiece C 2)
  let E := grassmannianChartHomogeneousCoordinateEquiv (R := F) 2
    (quadraticGrassmannianMonomialEquiv r hr)
  apply Module.Grassmannian.ext
  rw [grassmannianQuotientMap_submodule]
  rw [flatQuadraticGrassmannian_generic_submodule J C hJ r hr hrank]
  rw [homogeneousModelIdealPiece_eq_homogeneousIdealPiece C 2]
  change (homogeneousIdealPiece C 2).comap E.toLinearMap =
    (homogeneousIdealPiece C 2).map E.symm.toLinearMap
  exact Submodule.comap_equiv_eq_map_symm E (homogeneousIdealPiece C 2)

include hJ in
/-- The generic-fibre equality needs no separate rank hypothesis when
the model ideal extends to the prescribed generic ideal. -/
theorem flatQuadraticGrassmannian_generic_eq_fixedCurve_of_extendedIdeal
    [IsNoetherianRing R] [Module.Flat R (CoordinateRing J)]
    (hmap : Ideal.map (MvPolynomial.map (algebraMap R F)) J.toIdeal = C.toIdeal) :
    let r := Module.finrank F (homogeneousIdealPiece C 2)
    let hr := quadraticSubmodule_finrank_le_ten F (homogeneousIdealPiece C 2)
    grassmannianQuotientMap (algebraMap R F)
      (flatQuadraticGrassmannian J r hr (by
        intro p
        have hdim : Module.finrank F (grading C 2) ≤ 10 := by
          letI : Module.Finite F (homogeneousSubmodule (Fin 4) F 2) :=
            Module.Finite.iff_fg.mpr
              (MvPolynomial.homogeneousSubmodule_fg (Fin 4) F 2)
          calc
            Module.finrank F (grading C 2) ≤
                Module.finrank F (homogeneousSubmodule (Fin 4) F 2) :=
              LinearMap.finrank_le_finrank_of_surjective
                (homogeneousCoordinateQuotientMap_surjective C 2)
            _ = 10 := by rw [four_variable_homogeneous_finrank]; decide
        rw [homogeneousPiece_rank_eq_genericCurve_finrank J C hmap 2 p]
        have hcomp := homogeneousIdealPiece_quadratic_finrank_eq_complement C
        omega)) = fixedCurveQuadraticGrassmannian F C := by
  apply flatQuadraticGrassmannian_generic_eq_fixedCurve J C hJ

include hJ in
/-- The generic fibre of the actual Grassmannian-valued morphism is the
morphism classified by the prescribed function-field quadratic system. -/
theorem flatQuadraticGrassmannianMorphism_generic_eq_fixedCurve
    {K : Type u} [Field K] [Algebra K R] [Algebra K F]
    [IsScalarTower K R F]
    [IsNoetherianRing R] [Module.Flat R (CoordinateRing J)]
    (hrank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (grading J 2) p =
        10 - Module.finrank F (homogeneousIdealPiece C 2)) :
    let r := Module.finrank F (homogeneousIdealPiece C 2)
    let hr := quadraticSubmodule_finrank_le_ten F (homogeneousIdealPiece C 2)
    Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫
      flatQuadraticGrassmannianMorphism (K := K) J r hr hrank =
      grassmannianQuotientMorphism K (fixedCurveQuadraticGrassmannian F C) := by
  let r := Module.finrank F (homogeneousIdealPiece C 2)
  let hr := quadraticSubmodule_finrank_le_ten F (homogeneousIdealPiece C 2)
  change Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫
      grassmannianQuotientMorphism K (flatQuadraticGrassmannian J r hr hrank) = _
  have hφ : (IsScalarTower.toAlgHom K R F).toRingHom = algebraMap R F := by
    ext x
    rfl
  rw [← hφ]
  rw [grassmannianQuotientMorphism_naturality K
    (flatQuadraticGrassmannian J r hr hrank)
    (IsScalarTower.toAlgHom K R F)]
  exact congrArg (grassmannianQuotientMorphism K)
    (flatQuadraticGrassmannian_generic_eq_fixedCurve J C hJ hrank)

/-- For the actual principal-open model of a generic curve, its quadratic
Grassmannian quotient has the prescribed generic fibre. -/
theorem exists_contractedQuadraticGrassmannian_with_generic_fixedCurve
    {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [Algebra A F] [IsFractionRing A F]
    (e : A) (he : e ≠ 0)
    (φ : Localization.Away e →+* F)
    (hcomp : ∀ a : A, φ (algebraMap A (Localization.Away e) a) =
      algebraMap A F a)
    (J : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (Localization.Away e)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hJ : J.toIdeal = Ideal.comap (MvPolynomial.map φ) C.toIdeal)
    (hflat : Module.Flat (Localization.Away e) (CoordinateRing J)) :
    let r := Module.finrank F (homogeneousIdealPiece C 2)
    ∃ W : Module.Grassmannian (Localization.Away e)
      ((Fin r → Localization.Away e) ×
        (Fin (10 - r) → Localization.Away e)) (10 - r),
      grassmannianQuotientMap φ W = fixedCurveQuadraticGrassmannian F C := by
  letI : IsDomain (Localization.Away e) := Localization.Away.isDomain he
  letI : Algebra (Localization.Away e) F := φ.toAlgebra
  letI : IsScalarTower A (Localization.Away e) F :=
    IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  letI : IsFractionRing (Localization.Away e) F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers e) (Localization.Away e) F
  letI : Module.Flat (Localization.Away e) (CoordinateRing J) := hflat
  let r := Module.finrank F (homogeneousIdealPiece C 2)
  let hr := quadraticSubmodule_finrank_le_ten F (homogeneousIdealPiece C 2)
  have hd : Module.finrank F (grading C 2) ≤ 10 := by
    letI : Module.Finite F (homogeneousSubmodule (Fin 4) F 2) :=
      Module.Finite.iff_fg.mpr
        (MvPolynomial.homogeneousSubmodule_fg (Fin 4) F 2)
    calc
      Module.finrank F (grading C 2) ≤
          Module.finrank F (homogeneousSubmodule (Fin 4) F 2) :=
        LinearMap.finrank_le_finrank_of_surjective
          (homogeneousCoordinateQuotientMap_surjective C 2)
      _ = 10 := by rw [four_variable_homogeneous_finrank]; decide
  have hRank : ∀ p : PrimeSpectrum (Localization.Away e),
      Module.rankAtStalk (grading J 2) p = 10 - r := by
    intro p
    rw [homogeneousPiece_rank_eq_contractedGenericCurve_finrank
      e he φ hcomp J C hJ 2 p]
    have hdim := homogeneousIdealPiece_quadratic_finrank_eq_complement C
    omega
  refine ⟨flatQuadraticGrassmannian J r hr hRank, ?_⟩
  exact flatQuadraticGrassmannian_generic_eq_fixedCurve J C hJ hRank

end PfaffianDescent
