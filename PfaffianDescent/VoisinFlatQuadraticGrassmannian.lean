import PfaffianDescent.VoisinFlatIdealPiece
import PfaffianDescent.VoisinGenericGrassmannianSpread
import PfaffianDescent.GrassmannianQuotientMorphism

/-!
# Grassmannian point of a flat quadratic equation system

The degree-two quotient of a flat homogeneous coordinate algebra is a
finite projective quotient of the fixed ten-dimensional quadratic module.
It therefore determines a Grassmannian point over the coefficient ring.
-/

namespace PfaffianDescent

open MvPolynomial Module
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
  [Module.Flat R (CoordinateRing J)]

/-- The quotient Grassmannian point defined by a flat family of quadratic
equations, with a supplied constant rank for its quotient. -/
noncomputable def flatQuadraticGrassmannian
    (r : ℕ) (hr : r ≤ 10)
    (hRank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (grading J 2) p = 10 - r) :
    Module.Grassmannian R
      ((Fin r → R) × (Fin (10 - r) → R)) (10 - r) := by
  let E : ((Fin r → R) × (Fin (10 - r) → R)) ≃ₗ[R]
      homogeneousSubmodule (Fin 4) R 2 :=
    grassmannianChartHomogeneousCoordinateEquiv (R := R) 2
      (quadraticGrassmannianMonomialEquiv r hr)
  let q : ((Fin r → R) × (Fin (10 - r) → R)) →ₗ[R] grading J 2 :=
    (homogeneousCoordinateQuotientMap J 2).comp E.toLinearMap
  have hq : Function.Surjective q :=
    (homogeneousCoordinateQuotientMap_surjective J 2).comp E.surjective
  let ε : (((Fin r → R) × (Fin (10 - r) → R)) ⧸ q.ker) ≃ₗ[R]
      grading J 2 := q.quotKerEquivOfSurjective hq
  letI : Module.Finite R (grading J 2) :=
    coordinateRing_homogeneousPiece_finite J 2
  letI : Module.Projective R (grading J 2) :=
    coordinateRing_homogeneousPiece_projective J 2
  exact
    { toSubmodule := q.ker
      finite_quotient := Module.Finite.equiv ε.symm
      projective_quotient := Module.Projective.of_equiv ε.symm
      rankAtStalk_eq := by
        intro p
        calc
          Module.rankAtStalk
              (((Fin r → R) × (Fin (10 - r) → R)) ⧸ q.ker) p =
              Module.rankAtStalk (grading J 2) p :=
            congrFun (Module.rankAtStalk_eq_of_equiv ε) p
          _ = 10 - r := hRank p }

/-- The Grassmannian submodule is precisely the quadratic equation module
written in the fixed monomial coordinates. -/
theorem flatQuadraticGrassmannian_toSubmodule
    (r : ℕ) (hr : r ≤ 10)
    (hRank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (grading J 2) p = 10 - r) :
    (flatQuadraticGrassmannian J r hr hRank).toSubmodule =
      (homogeneousModelIdealPiece J 2).comap
        (grassmannianChartHomogeneousCoordinateEquiv (R := R) 2
          (quadraticGrassmannianMonomialEquiv r hr)).toLinearMap := by
  change ((homogeneousCoordinateQuotientMap J 2).comp
      (grassmannianChartHomogeneousCoordinateEquiv (R := R) 2
        (quadraticGrassmannianMonomialEquiv r hr)).toLinearMap).ker = _
  exact LinearMap.ker_comp _ _

/-- The flat quadratic system has a Grassmannian point of the rank dictated
by the quadratic Hilbert function of its prescribed generic curve. -/
noncomputable def genericCurveQuadraticGrassmannian
    [IsDomain R]
    {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F))
    (hJC : Ideal.map (MvPolynomial.map (algebraMap R F)) J.toIdeal = C.toIdeal) :
    let d := Module.finrank F (grading C 2)
    Module.Grassmannian R
      ((Fin (10 - d) → R) × (Fin d → R)) d := by
  let d := Module.finrank F (grading C 2)
  letI : Module.Finite F (homogeneousSubmodule (Fin 4) F 2) :=
    Module.Finite.iff_fg.mpr
      (MvPolynomial.homogeneousSubmodule_fg (Fin 4) F 2)
  have hd : d ≤ 10 := by
    have h := LinearMap.finrank_le_finrank_of_surjective
      (homogeneousCoordinateQuotientMap_surjective C 2)
    calc
      d ≤ Module.finrank F (homogeneousSubmodule (Fin 4) F 2) := h
      _ = 10 := by rw [four_variable_homogeneous_finrank]; decide
  let r := 10 - d
  have hr : r ≤ 10 := Nat.sub_le 10 d
  have hdim : 10 - r = d := by omega
  let W := flatQuadraticGrassmannian J r hr (by
    intro p
    rw [homogeneousPiece_rank_eq_genericCurve_finrank J C hJC 2 p]
    exact hdim.symm)
  change Module.Grassmannian R ((Fin r → R) × (Fin d → R)) d
  exact hdim ▸ W

/-- The flat quadratic quotient gives an actual Grassmannian-valued map on
the affine coefficient base. -/
noncomputable def flatQuadraticGrassmannianMorphism
    {K : Type u} [Field K] [Algebra K R]
    (r : ℕ) (hr : r ≤ 10)
    (hRank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (grading J 2) p = 10 - r) :
    Spec (.of R) ⟶ grassmannianScheme K r (10 - r) :=
  grassmannianQuotientMorphism K
    (flatQuadraticGrassmannian J r hr hRank)

theorem flatQuadraticGrassmannianMorphism_toBase
    {K : Type u} [Field K] [Algebra K R]
    (r : ℕ) (hr : r ≤ 10)
    (hRank : ∀ p : PrimeSpectrum R,
      Module.rankAtStalk (grading J 2) p = 10 - r) :
    flatQuadraticGrassmannianMorphism J r hr hRank ≫
      grassmannianToBase K r (10 - r) =
      Spec.map (CommRingCat.ofHom (algebraMap K R)) :=
  grassmannianQuotientMorphism_toBase K
    (flatQuadraticGrassmannian J r hr hRank)

end PfaffianDescent
