import PfaffianDescent.GrassmannianProjectiveFrameTransition
import PfaffianDescent.ProjectiveFrameNaturality
import PfaffianDescent.GrassmannianOverlapIsomorphism

namespace PfaffianDescent
open MvPolynomial
open AllCharacteristics.UniversalHomogeneous
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
variable {τ : Type} [Finite τ] (d : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Recovering frame coordinates commutes with changing coefficients. -/
theorem grassmannianChartHomogeneousFrameRetraction_baseChange
    (f : R →+* S) {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (p : homogeneousSubmodule τ R d) :
    grassmannianChartHomogeneousFrameRetraction (R := S) d e ρ
      (homogeneousSubmoduleBaseChange d f p) =
        fun i => f (grassmannianChartHomogeneousFrameRetraction (R := R) d e ρ p i) := by
  obtain ⟨x, rfl⟩ := (grassmannianChartHomogeneousCoordinateEquiv (R := R) d e).surjective p
  rw [grassmannianChartHomogeneousCoordinateEquiv_baseChange]
  change (graphCoordinatePermutation S ρ
    ((grassmannianChartHomogeneousCoordinateEquiv (R := S) d e).symm
      (grassmannianChartHomogeneousCoordinateEquiv (R := S) d e (graphCoefficientMap f x)))).1 =
    fun i => f ((graphCoordinatePermutation R ρ
      ((grassmannianChartHomogeneousCoordinateEquiv (R := R) d e).symm
        (grassmannianChartHomogeneousCoordinateEquiv (R := R) d e x))).1 i)
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact congrArg Prod.fst (graphCoordinatePermutation_map f ρ x)

/-- The matrix changing coordinates between two Grassmannian homogeneous
frames commutes with every coefficient-ring homomorphism. -/
theorem grassmannianChartHomogeneousFrameTransition_toMatrix_baseChange
    (f : R →+* S) {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ ρ' : Equiv.Perm (Fin m ⊕ Fin n))
    (T T' : Matrix (Fin n) (Fin m) R) :
    (LinearMap.toMatrix'
      (grassmannianChartHomogeneousFrameTransition (R := R) d e ρ ρ' T T')).map f =
      LinearMap.toMatrix'
        (grassmannianChartHomogeneousFrameTransition (R := S) d e ρ ρ'
          (T.map f) (T'.map f)) := by
  ext i j
  simp only [Matrix.map_apply, LinearMap.toMatrix'_apply]
  unfold grassmannianChartHomogeneousFrameTransition projectiveFrameTransition
  simp only [LinearMap.comp_apply, projectiveFrameMap,
    Fintype.linearCombination_apply_single, one_smul]
  change f (grassmannianChartHomogeneousFrameRetraction (R := R) d e ρ'
      (grassmannianChartHomogeneousFrame (R := R) d e ρ T j) i) =
    grassmannianChartHomogeneousFrameRetraction (R := S) d e ρ'
      (grassmannianChartHomogeneousFrame (R := S) d e ρ (T.map f) j) i
  rw [← grassmannianChartHomogeneousFrame_baseChange (R := R) d f e ρ T j,
    grassmannianChartHomogeneousFrameRetraction_baseChange (R := R) d f e ρ']

/-- The ambient coefficient matrix of a Grassmannian homogeneous frame
commutes with coefficient extension. -/
theorem grassmannianChartHomogeneousFrameCoefficientMatrix_baseChange
    (f : R →+* S) {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    (grassmannianChartHomogeneousFrameCoefficientMatrix
      (R := R) d e ρ T).map f =
      grassmannianChartHomogeneousFrameCoefficientMatrix
        (R := S) d e ρ (T.map f) := by
  ext i j
  simp only [Matrix.map_apply]
  unfold grassmannianChartHomogeneousFrameCoefficientMatrix
  simp only [LinearMap.toMatrix'_apply, LinearMap.comp_apply,
    grassmannianChartHomogeneousFrameMap,
    Fintype.linearCombination_apply_single, one_smul]
  rw [← grassmannianChartHomogeneousFrame_baseChange (R := R) d f e ρ T j,
    homogeneousCoefficientMapOverRing_baseChange (R := R) d f e]

/-- After transport to the forward overlap ring, the reverse overlap's frame
transition is the reverse frame transition over the forward ring. -/
theorem grassmannianOverlap_reverseFrameTransition_toMatrix_map
    (K : Type u) [CommRing K] {m n : ℕ}
    (e : Fin (m + n) ≃ Monomials τ d)
    (ρ ρ' : Equiv.Perm (Fin m ⊕ Fin n))
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (LinearMap.toMatrix'
      (grassmannianChartHomogeneousFrameTransition
        (R := GrassmannianOverlapRing K σ.symm) d e ρ' ρ
        (grassmannianOverlapUniversalMatrix K σ.symm)
        (grassmannianOverlapTransitionMatrix K σ.symm))).map
          (grassmannianOverlapTransitionAlgHom K σ).toRingHom =
      LinearMap.toMatrix'
        (grassmannianChartHomogeneousFrameTransition
          (R := GrassmannianOverlapRing K σ) d e ρ' ρ
          (grassmannianOverlapTransitionMatrix K σ)
          (grassmannianOverlapUniversalMatrix K σ)) := by
  rw [grassmannianChartHomogeneousFrameTransition_toMatrix_baseChange]
  have hU : (grassmannianOverlapUniversalMatrix K σ.symm).map
      (grassmannianOverlapTransitionAlgHom K σ).toRingHom =
        grassmannianOverlapTransitionMatrix K σ := by
    simpa using grassmannianOverlapTransitionAlgHom_map_universal K σ
  have hT : (grassmannianOverlapTransitionMatrix K σ.symm).map
      (grassmannianOverlapTransitionAlgHom K σ).toRingHom =
        grassmannianOverlapUniversalMatrix K σ := by
    simpa using grassmannianOverlapTransitionAlgHom_map_transition K σ
  rw [hU, hT]

/-- The inverse matrix occurring in the reverse projective transition also
transports to the corresponding forward-overlap frame transition. -/
theorem grassmannianOverlap_reverseInverseFrameTransition_toMatrix_map
    (K : Type u) [CommRing K] {m n : ℕ}
    (e : Fin (m + n) ≃ Monomials τ d)
    (ρ ρ' : Equiv.Perm (Fin m ⊕ Fin n))
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (LinearMap.toMatrix'
      (grassmannianChartHomogeneousFrameTransition
        (R := GrassmannianOverlapRing K σ.symm) d e ρ ρ'
        (grassmannianOverlapTransitionMatrix K σ.symm)
        (grassmannianOverlapUniversalMatrix K σ.symm))).map
          (grassmannianOverlapTransitionAlgHom K σ).toRingHom =
      LinearMap.toMatrix'
        (grassmannianChartHomogeneousFrameTransition
          (R := GrassmannianOverlapRing K σ) d e ρ ρ'
          (grassmannianOverlapUniversalMatrix K σ)
          (grassmannianOverlapTransitionMatrix K σ)) := by
  rw [grassmannianChartHomogeneousFrameTransition_toMatrix_baseChange]
  have hU : (grassmannianOverlapUniversalMatrix K σ.symm).map
      (grassmannianOverlapTransitionAlgHom K σ).toRingHom =
        grassmannianOverlapTransitionMatrix K σ := by
    simpa using grassmannianOverlapTransitionAlgHom_map_universal K σ
  have hT : (grassmannianOverlapTransitionMatrix K σ.symm).map
      (grassmannianOverlapTransitionAlgHom K σ).toRingHom =
        grassmannianOverlapUniversalMatrix K σ := by
    simpa using grassmannianOverlapTransitionAlgHom_map_transition K σ
  rw [hT, hU]

end PfaffianDescent
