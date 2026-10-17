import PfaffianDescent.GrassmannianSubmoduleBaseChange
import PfaffianDescent.HomogeneousCoordinatesOverRing
import PfaffianDescent.HomogeneousCoordinatesBaseChange

/-!
# Homogeneous frames on Grassmannian charts

A Grassmannian chart represents a free submodule by the columns of a matrix.
After choosing monomial coordinates for a homogeneous polynomial piece, those
columns are an actual free frame of homogeneous forms over the chart ring.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable {R : Type u} [CommRing R] {τ : Type} [Finite τ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Identify a pair of finite coordinate vectors with one vector indexed by
the concatenated finite type. -/
noncomputable def finiteProductCoordinateEquiv (m n : ℕ) :
    ((Fin m → R) × (Fin n → R)) ≃ₗ[R] (Fin (m + n) → R) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin n) R R).symm.trans
    (LinearEquiv.piCongrLeft R (fun _ : Fin (m + n) => R) finSumFinEquiv)

/-- Concatenated finite coordinates commute with a coefficient-ring map. -/
theorem finiteProductCoordinateEquiv_baseChange
    {S : Type u} [CommRing S] (f : R →+* S) (m n : ℕ)
    (x : (Fin m → R) × (Fin n → R)) :
    (fun i => f (finiteProductCoordinateEquiv (R := R) m n x i)) =
      finiteProductCoordinateEquiv (R := S) m n
        (graphCoefficientMap f x) := by
  rcases x with ⟨x₁, x₂⟩
  funext i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j <;>
    simp [finiteProductCoordinateEquiv, LinearEquiv.piCongrLeft,
      LinearEquiv.piCongrLeft', LinearEquiv.sumArrowLequivProdArrow,
      graphCoefficientMap, Function.comp_def,
      Equiv.sumArrowEquivProdArrow_symm_apply_inl,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr]

/-- Recover the source coordinates of a graph-chart column from ambient
coordinates. -/
noncomputable def grassmannianChartColumnRetraction (m n : ℕ)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) :
    ((Fin m → R) × (Fin n → R)) →ₗ[R] (Fin m → R) :=
  (LinearMap.fst R (Fin m → R) (Fin n → R)).comp
    (graphCoordinatePermutation R ρ).toLinearMap

/-- The chart-column retraction sends each graph column to its standard
coordinate vector. -/
theorem grassmannianChartColumnRetraction_apply_column
    {m n : ℕ} (ρ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R) (j : Fin m) :
    grassmannianChartColumnRetraction (R := R) m n ρ
      (grassmannianChartColumn R ρ T j) = Pi.basisFun R (Fin m) j := by
  let E := graphCoordinatePermutation R ρ
  change (E (graphCoordinatePermutation R ρ.symm
    (Pi.single j 1, fun i => T i j))).1 = Pi.basisFun R (Fin m) j
  rw [← graphCoordinatePermutation_symm]
  rw [E.apply_symm_apply]
  simp [Pi.basisFun_apply]

/-- Interpret a Grassmannian chart's ambient coordinates as homogeneous
polynomials in a fixed monomial coordinate system. -/
noncomputable def grassmannianChartHomogeneousCoordinateEquiv
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d) :
    ((Fin m → R) × (Fin n → R)) ≃ₗ[R]
      homogeneousSubmodule τ R d :=
  (finiteProductCoordinateEquiv (R := R) m n).trans
    (homogeneousCoefficientLinearEquivOverRing (R := R) d e).symm

/-- Interpreting chart coordinates as homogeneous forms commutes with every
coefficient-ring map. -/
theorem grassmannianChartHomogeneousCoordinateEquiv_baseChange
    {S : Type u} [CommRing S] (f : R →+* S) {m n : ℕ}
    (e : Fin (m + n) ≃ Monomials τ d)
    (x : (Fin m → R) × (Fin n → R)) :
    homogeneousSubmoduleBaseChange d f
      (grassmannianChartHomogeneousCoordinateEquiv (R := R) d e x) =
        grassmannianChartHomogeneousCoordinateEquiv (R := S) d e
          (graphCoefficientMap f x) := by
  change homogeneousSubmoduleBaseChange d f
    (homogeneousCoefficientSynthesisOverRing (R := R) d e
      (finiteProductCoordinateEquiv (R := R) m n x)) =
    homogeneousCoefficientSynthesisOverRing (R := S) d e
      (finiteProductCoordinateEquiv (R := S) m n (graphCoefficientMap f x))
  rw [homogeneousCoefficientSynthesisOverRing_baseChange]
  exact congrArg (homogeneousCoefficientSynthesisOverRing (R := S) d e)
    (finiteProductCoordinateEquiv_baseChange (R := R) f m n x)

/-- The homogeneous polynomial represented by a column of a Grassmannian
chart. -/
noncomputable def grassmannianChartHomogeneousFrame
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    Fin m → homogeneousSubmodule τ R d :=
  (grassmannianChartHomogeneousCoordinateEquiv (R := R) d e).toLinearMap ∘
    grassmannianChartColumn R ρ T

/-- The homogeneous forms of a Grassmannian chart commute with coefficient
extension and, in particular, with restriction to a smaller scheme open. -/
theorem grassmannianChartHomogeneousFrame_baseChange
    {S : Type u} [CommRing S] (f : R →+* S) {m n : ℕ}
    (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R)
    (j : Fin m) :
    homogeneousSubmoduleBaseChange d f
      (grassmannianChartHomogeneousFrame (R := R) d e ρ T j) =
        grassmannianChartHomogeneousFrame (R := S) d e ρ (T.map f) j := by
  change homogeneousSubmoduleBaseChange d f
    (grassmannianChartHomogeneousCoordinateEquiv (R := R) d e
      (grassmannianChartColumn R ρ T j)) =
    grassmannianChartHomogeneousCoordinateEquiv (R := S) d e
      (grassmannianChartColumn S ρ (T.map f) j)
  rw [grassmannianChartHomogeneousCoordinateEquiv_baseChange]
  exact congrArg (grassmannianChartHomogeneousCoordinateEquiv (R := S) d e)
    (grassmannianChartColumn_map f ρ T j)

/-- Recover the coordinates in a homogeneous chart frame. -/
noncomputable def grassmannianChartHomogeneousFrameRetraction
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) :
    homogeneousSubmodule τ R d →ₗ[R] (Fin m → R) :=
  (grassmannianChartColumnRetraction (R := R) m n ρ).comp
    (grassmannianChartHomogeneousCoordinateEquiv (R := R) d e).symm.toLinearMap

/-- The homogeneous-frame retraction sends a local frame vector to its
standard coordinate vector. -/
theorem grassmannianChartHomogeneousFrameRetraction_apply
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R)
    (j : Fin m) :
    grassmannianChartHomogeneousFrameRetraction (R := R) d e ρ
      (grassmannianChartHomogeneousFrame (R := R) d e ρ T j) =
        Pi.basisFun R (Fin m) j := by
  change grassmannianChartColumnRetraction (R := R) m n ρ
    ((grassmannianChartHomogeneousCoordinateEquiv (R := R) d e).symm
      ((grassmannianChartHomogeneousCoordinateEquiv (R := R) d e)
        (grassmannianChartColumn R ρ T j))) = _
  rw [(grassmannianChartHomogeneousCoordinateEquiv (R := R) d e).symm_apply_apply]
  exact grassmannianChartColumnRetraction_apply_column (R := R) ρ T j

/-- The linear combination map of a homogeneous Grassmannian chart frame. -/
noncomputable def grassmannianChartHomogeneousFrameMap
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    (Fin m → R) →ₗ[R] homogeneousSubmodule τ R d :=
  Fintype.linearCombination R (grassmannianChartHomogeneousFrame (R := R) d e ρ T)

/-- The explicit retraction is a left inverse to the homogeneous chart-frame
linear-combination map. -/
theorem grassmannianChartHomogeneousFrameRetraction_comp_map
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    (grassmannianChartHomogeneousFrameRetraction (R := R) d e ρ).comp
      (grassmannianChartHomogeneousFrameMap (R := R) d e ρ T) = LinearMap.id := by
  apply LinearMap.ext
  intro c
  ext i
  change grassmannianChartHomogeneousFrameRetraction (R := R) d e ρ
    (Fintype.linearCombination R
      (grassmannianChartHomogeneousFrame (R := R) d e ρ T) c) i = c i
  rw [Fintype.linearCombination_apply, map_sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp [grassmannianChartHomogeneousFrameRetraction_apply]
  · intro j _ hji
    rw [map_smul, grassmannianChartHomogeneousFrameRetraction_apply]
    simp [Pi.basisFun_apply, hji]
  · simp

/-- Coefficient matrix of the homogeneous frame on a Grassmannian chart. -/
noncomputable def grassmannianChartHomogeneousFrameCoefficientMatrix
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    Matrix (Fin (m + n)) (Fin m) R :=
  LinearMap.toMatrix' ((homogeneousCoefficientMapOverRing (R := R) d e).comp
    (grassmannianChartHomogeneousFrameMap (R := R) d e ρ T))

/-- Matrix of the explicit coefficient retraction for a Grassmannian chart
frame. -/
noncomputable def grassmannianChartHomogeneousFrameCoefficientRetractionMatrix
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Matrix (Fin m) (Fin (m + n)) R :=
  LinearMap.toMatrix'
    ((grassmannianChartHomogeneousFrameRetraction (R := R) d e ρ).comp
      (homogeneousCoefficientSynthesisOverRing (R := R) d e))

/-- The chart homogeneous-frame coefficient matrix is split over every
commutative coordinate ring. -/
theorem grassmannianChartHomogeneousFrameCoefficientMatrix_has_retraction
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    grassmannianChartHomogeneousFrameCoefficientRetractionMatrix (R := R) d e ρ *
      grassmannianChartHomogeneousFrameCoefficientMatrix (R := R) d e ρ T = 1 := by
  change LinearMap.toMatrix'
      ((grassmannianChartHomogeneousFrameRetraction (R := R) d e ρ).comp
        (homogeneousCoefficientSynthesisOverRing (R := R) d e)) *
      LinearMap.toMatrix' ((homogeneousCoefficientMapOverRing (R := R) d e).comp
        (grassmannianChartHomogeneousFrameMap (R := R) d e ρ T)) = 1
  rw [← LinearMap.toMatrix'_comp]
  have hcomp :
      ((grassmannianChartHomogeneousFrameRetraction (R := R) d e ρ).comp
        (homogeneousCoefficientSynthesisOverRing (R := R) d e)).comp
        ((homogeneousCoefficientMapOverRing (R := R) d e).comp
          (grassmannianChartHomogeneousFrameMap (R := R) d e ρ T)) =
        (grassmannianChartHomogeneousFrameRetraction (R := R) d e ρ).comp
          (grassmannianChartHomogeneousFrameMap (R := R) d e ρ T) := by
    apply LinearMap.ext
    intro x
    change grassmannianChartHomogeneousFrameRetraction (R := R) d e ρ
      (homogeneousCoefficientSynthesisOverRing (R := R) d e
        (homogeneousCoefficientMapOverRing (R := R) d e
          (grassmannianChartHomogeneousFrameMap (R := R) d e ρ T x))) =
      grassmannianChartHomogeneousFrameRetraction (R := R) d e ρ
        (grassmannianChartHomogeneousFrameMap (R := R) d e ρ T x)
    rw [homogeneousCoefficientSynthesisOverRing_map]
  rw [hcomp, grassmannianChartHomogeneousFrameRetraction_comp_map,
    LinearMap.toMatrix'_id]

/-- The homogeneous system represented by a Grassmannian chart.  This is
defined from the underlying chart submodule, so it is independent of the
chosen local frame. -/
noncomputable def grassmannianChartHomogeneousSystem
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    Submodule R (homogeneousSubmodule τ R d) :=
  (grassmannianChartSubmodule R ρ T).map
    (grassmannianChartHomogeneousCoordinateEquiv (R := R) d e).toLinearMap

/-- The homogeneous system is spanned by the local chart frame. -/
theorem grassmannianChartHomogeneousSystem_span
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    grassmannianChartHomogeneousSystem (R := R) d e ρ T =
      Submodule.span R (Set.range
        (grassmannianChartHomogeneousFrame (R := R) d e ρ T)) := by
  rw [grassmannianChartHomogeneousSystem, grassmannianChartSubmodule_span,
    Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨grassmannianChartColumn R ρ T j, ⟨j, rfl⟩, rfl⟩

/-- The homogeneous system represented by a chart commutes with arbitrary
coefficient extension. -/
theorem grassmannianChartHomogeneousSystem_baseChange
    {S : Type u} [CommRing S] (f : R →+* S) {m n : ℕ}
    (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    homogeneousSystemBaseChange d f
      (grassmannianChartHomogeneousSystem (R := R) d e ρ T) =
        grassmannianChartHomogeneousSystem (R := S) d e ρ (T.map f) := by
  rw [homogeneousSystemBaseChange, grassmannianChartHomogeneousSystem_span,
    span_image_span_semilinear, ← Set.range_comp,
    grassmannianChartHomogeneousSystem_span]
  congr 2
  funext j
  exact grassmannianChartHomogeneousFrame_baseChange (R := R) d f e ρ T j

/-- Agreement of Grassmannian chart submodules gives agreement of the
corresponding homogeneous systems.  This is the chart-overlap compatibility
needed to glue local systems of equations. -/
theorem grassmannianChartHomogeneousSystem_eq_of_submodule_eq
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ ρ' : Equiv.Perm (Fin m ⊕ Fin n))
    (T T' : Matrix (Fin n) (Fin m) R)
    (h : grassmannianChartSubmodule R ρ T = grassmannianChartSubmodule R ρ' T') :
    grassmannianChartHomogeneousSystem (R := R) d e ρ T =
      grassmannianChartHomogeneousSystem (R := R) d e ρ' T' := by
  exact congrArg (fun W : Submodule R ((Fin m → R) × (Fin n → R)) =>
    W.map (grassmannianChartHomogeneousCoordinateEquiv (R := R) d e).toLinearMap) h

/-- The local homogeneous forms supplied by a Grassmannian chart are a free
frame over every commutative coordinate ring. -/
theorem grassmannianChartHomogeneousFrame_linearIndependent
    {m n : ℕ} (e : Fin (m + n) ≃ Monomials τ d)
    (ρ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    LinearIndependent R (grassmannianChartHomogeneousFrame (R := R) d e ρ T) := by
  have hker :
      (grassmannianChartHomogeneousCoordinateEquiv (R := R) d e).toLinearMap.ker =
        ⊥ :=
    LinearMap.ker_eq_bot_of_injective
      (grassmannianChartHomogeneousCoordinateEquiv (R := R) d e).injective
  simpa [grassmannianChartHomogeneousFrame] using
    (grassmannianChartColumn_linearIndependent R ρ T).map'
      (grassmannianChartHomogeneousCoordinateEquiv (R := R) d e).toLinearMap hker

end PfaffianDescent
