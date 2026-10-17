import PfaffianDescent.ProjectiveFrameCoordinateMap

/-!
# Projective coordinate transitions on Grassmannian charts

On a Grassmannian-chart overlap the two chart frames span the same homogeneous
system.  Their explicit frame retractions therefore give inverse matrices of
projective coordinates.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable {R : Type u} [CommRing R] {τ : Type} [Finite τ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Change from the coordinates of one Grassmannian-chart frame to those of
another frame for the same homogeneous system. -/
noncomputable def grassmannianChartHomogeneousFrameTransition
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ ρ' : Equiv.Perm (Fin m ⊕ Fin n))
    (T T' : Matrix (Fin n) (Fin m) R) :
    (Fin m → R) →ₗ[R] (Fin m → R) :=
  projectiveFrameTransition
    (V := ↥(homogeneousSubmodule τ R d))
      (grassmannianChartHomogeneousFrame (R := R) d e ρ T)
      (grassmannianChartHomogeneousFrame (R := R) d e ρ' T')
      (grassmannianChartHomogeneousFrameRetraction (R := R) d e ρ')

/-- Equality of the represented chart submodules gives equality of the
spans of their homogeneous frames. -/
lemma grassmannianChartHomogeneousFrame_span_eq_of_submodule_eq
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ ρ' : Equiv.Perm (Fin m ⊕ Fin n))
    (T T' : Matrix (Fin n) (Fin m) R)
    (h : grassmannianChartSubmodule R ρ T = grassmannianChartSubmodule R ρ' T') :
    Submodule.span R (Set.range
      (grassmannianChartHomogeneousFrame (R := R) d e ρ T)) =
      Submodule.span R (Set.range
        (grassmannianChartHomogeneousFrame (R := R) d e ρ' T')) := by
  rw [← grassmannianChartHomogeneousSystem_span,
    ← grassmannianChartHomogeneousSystem_span]
  exact grassmannianChartHomogeneousSystem_eq_of_submodule_eq d e ρ ρ' T T' h

/-- The two coordinate-transition matrices on a chart overlap are inverse. -/
lemma grassmannianChartHomogeneousFrameTransition_toMatrix_mul
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ ρ' : Equiv.Perm (Fin m ⊕ Fin n))
    (T T' : Matrix (Fin n) (Fin m) R)
    (h : grassmannianChartSubmodule R ρ T = grassmannianChartSubmodule R ρ' T') :
    LinearMap.toMatrix'
        (grassmannianChartHomogeneousFrameTransition (R := R) d e ρ' ρ T' T) *
      LinearMap.toMatrix'
        (grassmannianChartHomogeneousFrameTransition (R := R) d e ρ ρ' T T') = 1 := by
  have hspan := grassmannianChartHomogeneousFrame_span_eq_of_submodule_eq (R := R)
    d e ρ ρ' T T' h
  exact projectiveFrameTransition_toMatrix_mul
    (grassmannianChartHomogeneousFrame (R := R) d e ρ T)
    (grassmannianChartHomogeneousFrame (R := R) d e ρ' T')
    (grassmannianChartHomogeneousFrameRetraction (R := R) d e ρ)
    (grassmannianChartHomogeneousFrameRetraction (R := R) d e ρ')
    (grassmannianChartHomogeneousFrameRetraction_comp_map (R := R) d e ρ T)
    (grassmannianChartHomogeneousFrameRetraction_comp_map (R := R) d e ρ' T')
    hspan

/-- Expressing a form in the second frame and then changing coordinates from
the first frame recovers its coefficient vector in the first frame. -/
lemma grassmannianChartHomogeneousFrameCoefficientMatrix_mul_transition
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ ρ' : Equiv.Perm (Fin m ⊕ Fin n))
    (T T' : Matrix (Fin n) (Fin m) R)
    (h : grassmannianChartSubmodule R ρ T = grassmannianChartSubmodule R ρ' T') :
    grassmannianChartHomogeneousFrameCoefficientMatrix (R := R) d e ρ' T' *
      LinearMap.toMatrix'
        (grassmannianChartHomogeneousFrameTransition (R := R) d e ρ ρ' T T') =
    grassmannianChartHomogeneousFrameCoefficientMatrix (R := R) d e ρ T := by
  unfold grassmannianChartHomogeneousFrameCoefficientMatrix
  rw [← LinearMap.toMatrix'_comp]
  apply congrArg LinearMap.toMatrix'
  rw [LinearMap.comp_assoc]
  exact congrArg
    (fun q => (homogeneousCoefficientMapOverRing (R := R) d e).comp q)
    (projectiveFrameMap_comp_transition
      (grassmannianChartHomogeneousFrame (R := R) d e ρ T)
      (grassmannianChartHomogeneousFrame (R := R) d e ρ' T')
      (grassmannianChartHomogeneousFrameRetraction (R := R) d e ρ')
      (grassmannianChartHomogeneousFrameRetraction_comp_map
        (R := R) d e ρ' T')
      (grassmannianChartHomogeneousFrame_span_eq_of_submodule_eq
        (R := R) d e ρ ρ' T T' h).le)

/-- The projective coordinate transition attached to an overlap of two
Grassmannian chart frames. -/
noncomputable def grassmannianChartHomogeneousFrameProjectiveTransition
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ ρ' : Equiv.Perm (Fin m ⊕ Fin n))
    (T T' : Matrix (Fin n) (Fin m) R)
    (h : grassmannianChartSubmodule R ρ T = grassmannianChartSubmodule R ρ' T') :
    projectiveFrameCoordinateSpace (R := R) m ⟶
      projectiveFrameCoordinateSpace (R := R) m :=
  projectiveFrameCoordinateMap
    (LinearMap.toMatrix'
      (grassmannianChartHomogeneousFrameTransition (R := R) d e ρ ρ' T T'))
    (LinearMap.toMatrix'
      (grassmannianChartHomogeneousFrameTransition (R := R) d e ρ' ρ T' T))
    (grassmannianChartHomogeneousFrameTransition_toMatrix_mul (R := R)
      d e ρ ρ' T T' h)

instance grassmannianChartHomogeneousFrameProjectiveTransition_isClosedImmersion
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ ρ' : Equiv.Perm (Fin m ⊕ Fin n))
    (T T' : Matrix (Fin n) (Fin m) R)
    (h : grassmannianChartSubmodule R ρ T = grassmannianChartSubmodule R ρ' T') :
    IsClosedImmersion
      (grassmannianChartHomogeneousFrameProjectiveTransition (R := R)
        d e ρ ρ' T T' h) := by
  unfold grassmannianChartHomogeneousFrameProjectiveTransition
  exact projectiveFrameCoordinateMap_isClosedImmersion _ _ _

theorem grassmannianChartHomogeneousFrameProjectiveTransition_toBase
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ ρ' : Equiv.Perm (Fin m ⊕ Fin n))
    (T T' : Matrix (Fin n) (Fin m) R)
    (h : grassmannianChartSubmodule R ρ T = grassmannianChartSubmodule R ρ' T') :
    grassmannianChartHomogeneousFrameProjectiveTransition (R := R)
      d e ρ ρ' T T' h ≫
        toBase (⊥ : HomogeneousIdeal
          (MvPolynomial.homogeneousSubmodule (Fin m) R)) =
      toBase (⊥ : HomogeneousIdeal
        (MvPolynomial.homogeneousSubmodule (Fin m) R)) := by
  unfold grassmannianChartHomogeneousFrameProjectiveTransition
  exact projectiveFrameCoordinateMap_toBase _ _ _

/-- The overlap projective transitions are mutually inverse scheme maps. -/
theorem grassmannianChartHomogeneousFrameProjectiveTransition_comp
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ ρ' : Equiv.Perm (Fin m ⊕ Fin n))
    (T T' : Matrix (Fin n) (Fin m) R)
    (h : grassmannianChartSubmodule R ρ T = grassmannianChartSubmodule R ρ' T') :
    grassmannianChartHomogeneousFrameProjectiveTransition (R := R)
      d e ρ' ρ T' T h.symm ≫
      grassmannianChartHomogeneousFrameProjectiveTransition (R := R)
        d e ρ ρ' T T' h = 𝟙 _ := by
  let M := LinearMap.toMatrix'
    (grassmannianChartHomogeneousFrameTransition (R := R) d e ρ ρ' T T')
  let N := LinearMap.toMatrix'
    (grassmannianChartHomogeneousFrameTransition (R := R) d e ρ' ρ T' T)
  have hNM : N * M = 1 :=
    grassmannianChartHomogeneousFrameTransition_toMatrix_mul (R := R)
      d e ρ ρ' T T' h
  have hMN : M * N = 1 :=
    grassmannianChartHomogeneousFrameTransition_toMatrix_mul (R := R)
      d e ρ' ρ T' T h.symm
  exact projectiveFrameCoordinateMap_comp M N hNM hMN

/-- The projective coordinate spaces of two chart frames for the same
Grassmannian submodule are canonically isomorphic. -/
noncomputable def grassmannianChartHomogeneousFrameProjectiveTransitionIso
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ ρ' : Equiv.Perm (Fin m ⊕ Fin n))
    (T T' : Matrix (Fin n) (Fin m) R)
    (h : grassmannianChartSubmodule R ρ T = grassmannianChartSubmodule R ρ' T') :
    projectiveFrameCoordinateSpace (R := R) m ≅
      projectiveFrameCoordinateSpace (R := R) m where
  hom := grassmannianChartHomogeneousFrameProjectiveTransition (R := R)
    d e ρ ρ' T T' h
  inv := grassmannianChartHomogeneousFrameProjectiveTransition (R := R)
    d e ρ' ρ T' T h.symm
  hom_inv_id := grassmannianChartHomogeneousFrameProjectiveTransition_comp (R := R)
    d e ρ' ρ T' T h.symm
  inv_hom_id := grassmannianChartHomogeneousFrameProjectiveTransition_comp (R := R)
    d e ρ ρ' T T' h

end PfaffianDescent
