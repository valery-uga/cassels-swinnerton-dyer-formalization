import PfaffianDescent.GrassmannianHomogeneousFrame
import PfaffianDescent.PolynomialProjectiveMap
import PfaffianDescent.RectangularSubstitution

/-!
# Relative projective linear systems

The ordinary projective-linear-system API is field based.  This file gives
the corresponding construction over an arbitrary commutative ring, which is
what a Grassmannian chart supplies as its coordinate ring.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable {R : Type u} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The relative projective parameter scheme of a finite system with the
given coordinate type. -/
noncomputable abbrev relativeProjectiveLinearSystemParameters : Scheme.{u} :=
  scheme (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule τ R))

/-- A surjective homogeneous substitution presents a relative projective
linear system as a closed subsystem of the relative equation space. -/
noncomputable def relativeProjectiveLinearSystemToParameters
    (g : MvPolynomial (Monomials σ d) R →ₐ[R] MvPolynomial τ R)
    (hdeg : ∀ (r : ℕ) (p : MvPolynomial (Monomials σ d) R),
      p.IsHomogeneous r → (g p).IsHomogeneous r)
    (hsurj : Function.Surjective g) :
    relativeProjectiveLinearSystemParameters (R := R) (τ := τ) ⟶
      projectiveParameters R σ d :=
  polynomialProjectiveMap (ParameterIdeal R σ d)
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule τ R)) g bot_le hdeg hsurj

instance relativeProjectiveLinearSystemToParameters_isClosedImmersion
    (g : MvPolynomial (Monomials σ d) R →ₐ[R] MvPolynomial τ R)
    (hdeg : ∀ (r : ℕ) (p : MvPolynomial (Monomials σ d) R),
      p.IsHomogeneous r → (g p).IsHomogeneous r)
    (hsurj : Function.Surjective g) :
    IsClosedImmersion (relativeProjectiveLinearSystemToParameters d g hdeg hsurj) := by
  unfold relativeProjectiveLinearSystemToParameters
  exact polynomialProjectiveMap_isClosedImmersion _ _ _ _ _ _

/-- The relative projective linear-system morphism is over the coefficient
ring's spectrum. -/
theorem relativeProjectiveLinearSystemToParameters_toBase
    (g : MvPolynomial (Monomials σ d) R →ₐ[R] MvPolynomial τ R)
    (hdeg : ∀ (r : ℕ) (p : MvPolynomial (Monomials σ d) R),
      p.IsHomogeneous r → (g p).IsHomogeneous r)
    (hsurj : Function.Surjective g) :
    relativeProjectiveLinearSystemToParameters d g hdeg hsurj ≫
      projectiveParametersToBase R σ d =
        toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule τ R)) := by
  exact polynomialProjectiveMap_toBase _ _ _ _ _ _

/-- A relative projective linear system is proper over its coefficient base.
This records the properness needed when the local systems are assembled over
the Grassmannian atlas. -/
instance relativeProjectiveLinearSystemToParameters_toBase_isProper
    (g : MvPolynomial (Monomials σ d) R →ₐ[R] MvPolynomial τ R)
    (hdeg : ∀ (r : ℕ) (p : MvPolynomial (Monomials σ d) R),
      p.IsHomogeneous r → (g p).IsHomogeneous r)
    (hsurj : Function.Surjective g) :
    IsProper (relativeProjectiveLinearSystemToParameters d g hdeg hsurj ≫
      projectiveParametersToBase R σ d) := by
  rw [relativeProjectiveLinearSystemToParameters_toBase]
  exact isProper_toBase _

/-- Matrix-defined homogeneous substitution over an arbitrary coordinate
ring. -/
noncomputable def relativeProjectiveLinearSystemMatrixSubstitution
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) R) :
    MvPolynomial (Monomials σ d) R →ₐ[R] MvPolynomial (Fin n) R :=
  (rectangularSubstitution M).comp (MvPolynomial.rename e.symm)

theorem relativeProjectiveLinearSystemMatrixSubstitution_homogeneous
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) R)
    (r : ℕ) (p : MvPolynomial (Monomials σ d) R)
    (hp : p.IsHomogeneous r) :
    (relativeProjectiveLinearSystemMatrixSubstitution d e M p).IsHomogeneous r :=
  rectangularSubstitution_homogeneous M hp.rename_isHomogeneous

theorem relativeProjectiveLinearSystemMatrixSubstitution_surjective
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) R) (N : Matrix (Fin n) (Fin m) R)
    (hNM : N * M = 1) :
    Function.Surjective (relativeProjectiveLinearSystemMatrixSubstitution d e M) :=
  (rectangularSubstitution_surjective M N hNM).comp
    (MvPolynomial.rename_surjective e.symm e.symm.surjective)

/-- The relative closed projective subsystem determined by a split coefficient
matrix. -/
noncomputable def relativeProjectiveLinearSystemMatrixToParameters
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) R) (N : Matrix (Fin n) (Fin m) R)
    (hNM : N * M = 1) :
    relativeProjectiveLinearSystemParameters (R := R) (τ := Fin n) ⟶
      projectiveParameters R σ d :=
  relativeProjectiveLinearSystemToParameters d
    (relativeProjectiveLinearSystemMatrixSubstitution d e M)
    (fun r p hp => relativeProjectiveLinearSystemMatrixSubstitution_homogeneous d e M r p hp)
    (relativeProjectiveLinearSystemMatrixSubstitution_surjective d e M N hNM)

instance relativeProjectiveLinearSystemMatrixToParameters_isClosedImmersion
    {m n : ℕ} (e : Fin m ≃ Monomials σ d)
    (M : Matrix (Fin m) (Fin n) R) (N : Matrix (Fin n) (Fin m) R)
    (hNM : N * M = 1) :
    IsClosedImmersion (relativeProjectiveLinearSystemMatrixToParameters d e M N hNM) := by
  unfold relativeProjectiveLinearSystemMatrixToParameters
  exact relativeProjectiveLinearSystemToParameters_isClosedImmersion d
    (relativeProjectiveLinearSystemMatrixSubstitution d e M)
    (fun r p hp => relativeProjectiveLinearSystemMatrixSubstitution_homogeneous d e M r p hp)
    (relativeProjectiveLinearSystemMatrixSubstitution_surjective d e M N hNM)

/-- The relative projective system of homogeneous forms represented by a
Grassmannian chart. -/
noncomputable def grassmannianChartHomogeneousFrameToParameters
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials σ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    relativeProjectiveLinearSystemParameters (R := R) (τ := Fin m) ⟶
      projectiveParameters R σ d :=
  relativeProjectiveLinearSystemMatrixToParameters d e
    (grassmannianChartHomogeneousFrameCoefficientMatrix (R := R) d e ρ T)
    (grassmannianChartHomogeneousFrameCoefficientRetractionMatrix (R := R) d e ρ)
    (grassmannianChartHomogeneousFrameCoefficientMatrix_has_retraction (R := R) d e ρ T)

/-- A chart's relative projective system lies over its chart coefficient
scheme. -/
theorem grassmannianChartHomogeneousFrameToParameters_toBase
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials σ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    grassmannianChartHomogeneousFrameToParameters (R := R) d e ρ T ≫
      projectiveParametersToBase R σ d =
        toBase (⊥ : HomogeneousIdeal
          (MvPolynomial.homogeneousSubmodule (Fin m) R)) := by
  exact relativeProjectiveLinearSystemToParameters_toBase d
    (relativeProjectiveLinearSystemMatrixSubstitution d e
      (grassmannianChartHomogeneousFrameCoefficientMatrix (R := R) d e ρ T))
    (fun r p hp => relativeProjectiveLinearSystemMatrixSubstitution_homogeneous d e
      (grassmannianChartHomogeneousFrameCoefficientMatrix (R := R) d e ρ T) r p hp)
    (relativeProjectiveLinearSystemMatrixSubstitution_surjective d e
      (grassmannianChartHomogeneousFrameCoefficientMatrix (R := R) d e ρ T)
      (grassmannianChartHomogeneousFrameCoefficientRetractionMatrix (R := R) d e ρ)
      (grassmannianChartHomogeneousFrameCoefficientMatrix_has_retraction
        (R := R) d e ρ T))

/-- The local projective family attached to a Grassmannian chart is proper
over that chart. -/
instance grassmannianChartHomogeneousFrameToParameters_toBase_isProper
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials σ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    IsProper (grassmannianChartHomogeneousFrameToParameters (R := R) d e ρ T ≫
      projectiveParametersToBase R σ d) := by
  rw [grassmannianChartHomogeneousFrameToParameters_toBase]
  exact isProper_toBase _

instance grassmannianChartHomogeneousFrameToParameters_isClosedImmersion
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials σ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    IsClosedImmersion (grassmannianChartHomogeneousFrameToParameters (R := R) d e ρ T) := by
  unfold grassmannianChartHomogeneousFrameToParameters
  exact relativeProjectiveLinearSystemMatrixToParameters_isClosedImmersion d e
    (grassmannianChartHomogeneousFrameCoefficientMatrix (R := R) d e ρ T)
    (grassmannianChartHomogeneousFrameCoefficientRetractionMatrix (R := R) d e ρ)
    (grassmannianChartHomogeneousFrameCoefficientMatrix_has_retraction (R := R) d e ρ T)

end PfaffianDescent
