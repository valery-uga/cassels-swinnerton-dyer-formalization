import PfaffianDescent.VoisinFlatIdealPieceBaseChange
import PfaffianDescent.GrassmannianFrameProjectiveProper

/-!
# Grassmannian families of flat homogeneous equation spaces

The quadratic construction extends degree by degree.  A flat homogeneous
coordinate ring gives a finite projective quotient of each homogeneous
polynomial module.  In fixed monomial coordinates this is a Grassmannian
point, and its generic-fibre submodule is the original ideal's equation
space in that degree.
-/

namespace PfaffianDescent

open MvPolynomial Module
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
  [Module.Flat R (CoordinateRing J)]
  (d r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) d)

/-- The flat degree-`d` quotient in fixed monomial coordinates, with its
constant stalk rank supplied by the generic Hilbert function. -/
noncomputable def flatGradedGrassmannian
    (hRank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (grading J d) p = q) :
    Module.Grassmannian R ((Fin r → R) × (Fin q → R)) q := by
  let E := grassmannianChartHomogeneousCoordinateEquiv (R := R) d e
  let L : ((Fin r → R) × (Fin q → R)) →ₗ[R] grading J d :=
    (homogeneousCoordinateQuotientMap J d).comp E.toLinearMap
  have hL : Function.Surjective L :=
    (homogeneousCoordinateQuotientMap_surjective J d).comp E.surjective
  let ε : (((Fin r → R) × (Fin q → R)) ⧸ L.ker) ≃ₗ[R] grading J d :=
    L.quotKerEquivOfSurjective hL
  letI : Module.Finite R (grading J d) :=
    coordinateRing_homogeneousPiece_finite J d
  letI : Module.Projective R (grading J d) :=
    coordinateRing_homogeneousPiece_projective J d
  exact
    { toSubmodule := L.ker
      finite_quotient := Module.Finite.equiv ε.symm
      projective_quotient := Module.Projective.of_equiv ε.symm
      rankAtStalk_eq := by
        intro p
        exact (congrFun (Module.rankAtStalk_eq_of_equiv ε) p).trans (hRank p) }

omit [IsDomain R] in
/-- The underlying submodule consists exactly of the model's degree-`d`
equations, written in the chosen monomial coordinates. -/
theorem flatGradedGrassmannian_toSubmodule
    (hRank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (grading J d) p = q) :
    (flatGradedGrassmannian J d r q e hRank).toSubmodule =
      (homogeneousModelIdealPiece J d).comap
        (grassmannianChartHomogeneousCoordinateEquiv (R := R) d e).toLinearMap := by
  change ((homogeneousCoordinateQuotientMap J d).comp
      (grassmannianChartHomogeneousCoordinateEquiv (R := R) d e).toLinearMap).ker = _
  exact LinearMap.ker_comp _ _

variable {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F]
  (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
  (hJ : J.toIdeal =
    Ideal.comap (MvPolynomial.map (algebraMap R F)) C.toIdeal)

include hJ in
/-- In every degree, the generic fibre of the flat Grassmannian submodule
is the original generic ideal's equation space, in the same coordinates. -/
theorem flatGradedGrassmannian_generic_submodule
    (hRank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (grading J d) p = q) :
    grassmannianSubmoduleBaseChange (algebraMap R F)
      (flatGradedGrassmannian J d r q e hRank).toSubmodule =
      (homogeneousModelIdealPiece C d).comap
        (grassmannianChartHomogeneousCoordinateEquiv (R := F) d e).toLinearMap := by
  let ER := grassmannianChartHomogeneousCoordinateEquiv (R := R) d e
  let EF := grassmannianChartHomogeneousCoordinateEquiv (R := F) d e
  let W := flatGradedGrassmannian J d r q e hRank
  have hW : W.toSubmodule =
      (homogeneousModelIdealPiece J d).comap ER.toLinearMap :=
    flatGradedGrassmannian_toSubmodule J d r q e hRank
  have hgenericMap (x : homogeneousModelIdealPiece J d) :
      homogeneousSubmoduleBaseChange d (algebraMap R F) x.1 =
        genericIdealPiecePolynomialMap (F := F) J d x := rfl
  have hset : EF '' (graphCoefficientMap (algebraMap R F) ''
      (W.toSubmodule : Set ((Fin r → R) × (Fin q → R)))) =
      Set.range (genericIdealPiecePolynomialMap (F := F) J d) := by
    ext z
    constructor
    · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
      have hwJ : ER w ∈ homogeneousModelIdealPiece J d := by
        rw [hW] at hw
        exact hw
      let x : homogeneousModelIdealPiece J d := ⟨ER w, hwJ⟩
      refine ⟨x, ?_⟩
      rw [← hgenericMap x]
      exact grassmannianChartHomogeneousCoordinateEquiv_baseChange
        (R := R) d (algebraMap R F) e w
    · rintro ⟨x, rfl⟩
      let w := ER.symm x.1
      have hw : w ∈ W.toSubmodule := by
        rw [hW]
        change ER w ∈ homogeneousModelIdealPiece J d
        simpa only [w, ER.apply_symm_apply] using x.2
      refine ⟨graphCoefficientMap (algebraMap R F) w,
        ⟨w, hw, rfl⟩, ?_⟩
      rw [← grassmannianChartHomogeneousCoordinateEquiv_baseChange
        (R := R) d (algebraMap R F) e w]
      rw [show ER w = x.1 from ER.apply_symm_apply x.1]
      exact hgenericMap x
  have hmap : (grassmannianSubmoduleBaseChange (algebraMap R F)
      W.toSubmodule).map EF.toLinearMap = homogeneousModelIdealPiece C d := by
    rw [grassmannianSubmoduleBaseChange, Submodule.map_span]
    change Submodule.span F (EF ''
      (graphCoefficientMap (algebraMap R F) ''
        (W.toSubmodule : Set ((Fin r → R) × (Fin q → R))))) = _
    rw [hset]
    exact genericIdealPiece_span_eq J C hJ d
  have h := congrArg (fun S : Submodule F
      (homogeneousSubmodule (Fin 4) F d) => S.comap EF.toLinearMap) hmap
  simpa only [Submodule.comap_map_eq_of_injective EF.injective] using h

/-- The function-field point associated to a degree-`d` equation space,
using the same coordinate split as its flat model. -/
noncomputable def fixedCurveGradedGrassmannian
    (hr : Module.finrank F (homogeneousIdealPiece C d) = r) :
    Module.Grassmannian F ((Fin r → F) × (Fin q → F)) q := by
  let E := grassmannianChartHomogeneousCoordinateEquiv (R := F) d e
  let W := (homogeneousIdealPiece C d).comap E.toLinearMap
  have hW : Module.finrank F W = r := by
    change Module.finrank F ((homogeneousIdealPiece C d).comap E.toLinearMap) = r
    rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
    exact hr
  apply fieldSubmoduleGrassmannian F W
  rw [Submodule.finrank_quotient, hW]
  simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
  omega

include hJ in
/-- The base-changed flat degree-`d` quotient is literally the point
associated to the prescribed generic equation space. -/
theorem flatGradedGrassmannian_generic_eq_fixedCurve
    (hRank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (grading J d) p = q)
    (hr : Module.finrank F (homogeneousIdealPiece C d) = r) :
    grassmannianQuotientMap (algebraMap R F)
      (flatGradedGrassmannian J d r q e hRank) =
      fixedCurveGradedGrassmannian d r q e C hr := by
  apply Module.Grassmannian.ext
  rw [grassmannianQuotientMap_submodule]
  rw [flatGradedGrassmannian_generic_submodule J d r q e C hJ hRank]
  rw [homogeneousModelIdealPiece_eq_homogeneousIdealPiece C d]
  rfl

include hJ in
/-- The actual scheme morphism of the flat degree-`d` system specializes to
the morphism classified by the generic equation space. -/
theorem flatGradedGrassmannianMorphism_generic_eq_fixedCurve
    {K : Type u} [Field K] [Algebra K R] [Algebra K F]
    [IsScalarTower K R F]
    (hRank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (grading J d) p = q)
    (hr : Module.finrank F (homogeneousIdealPiece C d) = r) :
    Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫
      grassmannianQuotientMorphism K
        (flatGradedGrassmannian J d r q e hRank) =
      grassmannianQuotientMorphism K
        (fixedCurveGradedGrassmannian d r q e C hr) := by
  have hφ : (IsScalarTower.toAlgHom K R F).toRingHom = algebraMap R F := by
    ext x
    rfl
  rw [← hφ]
  rw [grassmannianQuotientMorphism_naturality K
    (flatGradedGrassmannian J d r q e hRank)
    (IsScalarTower.toAlgHom K R F)]
  exact congrArg (grassmannianQuotientMorphism K)
    (flatGradedGrassmannian_generic_eq_fixedCurve J d r q e C hJ hRank hr)

omit [IsDomain R] in
/-- The projective family of degree-`d` equations of a flat model is proper
over the model's coefficient base. -/
theorem flatGradedProjectiveFamily_isProper
    {K : Type u} [Field K] [IsNoetherianRing K] [Algebra K R]
    (hRank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (grading J d) p = q) :
    IsProper (grassmannianFrameProjectiveFamilyPullbackToBase K d e
      (grassmannianQuotientMorphism K
        (flatGradedGrassmannian J d r q e hRank))) := by
  change IsProper (pullback.snd (grassmannianFrameProjectiveToGrassmannian K d e)
    (grassmannianQuotientMorphism K
      (flatGradedGrassmannian J d r q e hRank)))
  infer_instance

include hJ in
/-- The generic fibre of the proper projective equation family is the
projective linear system of the prescribed function-field curve. -/
noncomputable def flatGradedProjectiveFamily_genericFiberIso
    {K : Type u} [Field K] [Algebra K R] [Algebra K F]
    [IsScalarTower K R F]
    (hRank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (grading J d) p = q)
    (hr : Module.finrank F (homogeneousIdealPiece C d) = r) :
    pullback
      (grassmannianFrameProjectiveFamilyPullbackToBase K d e
        (grassmannianQuotientMorphism K
          (flatGradedGrassmannian J d r q e hRank)))
      (Spec.map (CommRingCat.ofHom (algebraMap R F))) ≅
    grassmannianFrameProjectiveFamilyPullback K d e
      (grassmannianQuotientMorphism K
        (fixedCurveGradedGrassmannian d r q e C hr)) := by
  let f := grassmannianQuotientMorphism K
    (flatGradedGrassmannian J d r q e hRank)
  have hgeneric : Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ f =
      grassmannianQuotientMorphism K
        (fixedCurveGradedGrassmannian d r q e C hr) :=
    flatGradedGrassmannianMorphism_generic_eq_fixedCurve
      J d r q e C hJ hRank hr
  rw [← hgeneric]
  exact grassmannianFrameProjectiveFamilyPullback_baseChangeIso K d e f
    (Spec.map (CommRingCat.ofHom (algebraMap R F)))

/-- The dimensions of the generic equation and quotient spaces give the
cardinality of the degree-`d` monomial basis. -/
theorem fixedCurveGraded_monomials_card :
    Module.finrank F (homogeneousIdealPiece C d) +
      Module.finrank F (grading C d) =
      Fintype.card (Monomials (Fin 4) d) := by
  rw [finrank_homogeneousIdealPiece_add_finrank_grading]
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact Module.finrank_eq_card_basis
    (MvPolynomial.basisRestrictSupport F {a | a.degree = d})

/-- Canonical finite monomial coordinates for the equation/quotient split
dictated by the generic curve. -/
noncomputable def fixedCurveGraded_monomialEquiv :
    Fin (Module.finrank F (homogeneousIdealPiece C d) +
      Module.finrank F (grading C d)) ≃ Monomials (Fin 4) d :=
  (finCongr (fixedCurveGraded_monomials_card d C)).trans
    (Fintype.equivFin _).symm

/-- Every flat contracted model yields a degree-`d` Grassmannian point
whose generic fibre is exactly the prescribed curve's equation system. -/
theorem exists_contractedGradedGrassmannian_with_generic_fixedCurve
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Algebra A F] [IsFractionRing A F]
    (a : A) (ha : a ≠ 0)
    (φ : Localization.Away a →+* F)
    (hcomp : ∀ b : A,
      φ (algebraMap A (Localization.Away a) b) = algebraMap A F b)
    (J₀ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (Localization.Away a)))
    (hJ₀ : J₀.toIdeal = Ideal.comap (MvPolynomial.map φ) C.toIdeal)
    (hflat : Module.Flat (Localization.Away a) (CoordinateRing J₀)) :
    let r := Module.finrank F (homogeneousIdealPiece C d)
    let q := Module.finrank F (grading C d)
    let e := fixedCurveGraded_monomialEquiv d C
    ∃ W : Module.Grassmannian (Localization.Away a)
        ((Fin r → Localization.Away a) ×
          (Fin q → Localization.Away a)) q,
      grassmannianQuotientMap φ W =
        fixedCurveGradedGrassmannian d r q e C rfl := by
  letI : IsDomain (Localization.Away a) := Localization.Away.isDomain ha
  letI : Algebra (Localization.Away a) F := φ.toAlgebra
  letI : IsScalarTower A (Localization.Away a) F :=
    IsScalarTower.of_algebraMap_eq fun b => (hcomp b).symm
  letI : IsFractionRing (Localization.Away a) F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers a) (Localization.Away a) F
  letI : Module.Flat (Localization.Away a) (CoordinateRing J₀) := hflat
  let r := Module.finrank F (homogeneousIdealPiece C d)
  let q := Module.finrank F (grading C d)
  let e := fixedCurveGraded_monomialEquiv d C
  have hRank : ∀ p : PrimeSpectrum (Localization.Away a),
      Module.rankAtStalk (grading J₀ d) p = q := by
    intro p
    exact homogeneousPiece_rank_eq_contractedGenericCurve_finrank
      a ha φ hcomp J₀ C hJ₀ d p
  refine ⟨flatGradedGrassmannian J₀ d r q e hRank, ?_⟩
  exact flatGradedGrassmannian_generic_eq_fixedCurve
    J₀ d r q e C hJ₀ hRank rfl

end PfaffianDescent
