import PfaffianDescent.SerreActualProjectiveBasisParameter
import PfaffianDescent.LinearNormalizedProjectivePoint

/-! Actual homogeneous evaluation commutes with the actual matrix
substitution used by a change of global-section basis. -/
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def projectiveMatrixVectorEquations
    {K L : Type u} [Field K] [CommRing L] [Algebra K L] {n : ℕ}
    (x : Fin n → L) :
    ∀ p ∈ (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)).toIdeal,
      p.eval₂ (algebraMap K L) x = 0 := by
  intro p hp
  have hp0 : p = 0 := by simpa using hp
  subst p
  simp

def projectiveMatrixVectorEvaluation
    {K L : Type u} [Field K] [CommRing L] [Algebra K L] {n : ℕ}
    (x : Fin n → L) :
    CoordinateRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) →+* L :=
  Ideal.Quotient.lift _ (eval₂Hom (algebraMap K L) x) (projectiveMatrixVectorEquations x)

def projectiveMatrixGradingMap
    {K : Type u} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) →+*ᵍ
      grading (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) :=
  polynomialQuotientGradingMap _ _ (rectangularSubstitution M) bot_le
    (fun _ _ hp => rectangularSubstitution_homogeneous M hp)

theorem projectiveMatrixVectorEvaluation_coordinate
    {K L : Type u} [Field K] [CommRing L] [Algebra K L] {n : ℕ}
    (x : Fin n → L) (i : Fin n) :
    projectiveMatrixVectorEvaluation x
      (coordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i) = x i := by
  change eval₂Hom (algebraMap K L) x (X i) = x i
  exact eval₂Hom_X' _ _ _

theorem projectiveMatrixVectorEvaluation_comp
    {K L : Type u} [Field K] [CommRing L] [Algebra K L] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (x : Fin n → L) :
    (projectiveMatrixVectorEvaluation x).comp (projectiveMatrixGradingMap M).toRingHom =
      projectiveMatrixVectorEvaluation ((M.map (algebraMap K L)).mulVec x) := by
  have hpoly : (eval₂Hom (algebraMap K L) x).comp (rectangularSubstitution M).toRingHom =
      eval₂Hom (algebraMap K L) ((M.map (algebraMap K L)).mulVec x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [rectangularSubstitution]
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, rectangularSubstitution_X, eval₂Hom_X']
      exact eval₂_rectangularLinearCoordinate M i (algebraMap K L) x
  apply RingHom.ext
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  change eval₂Hom (algebraMap K L) x (rectangularSubstitution M p) =
    eval₂Hom (algebraMap K L) ((M.map (algebraMap K L)).mulVec x) p
  exact RingHom.congr_fun hpoly p

end PfaffianDescent
