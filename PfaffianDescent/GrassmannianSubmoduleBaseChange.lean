import PfaffianDescent.GrassmannianChartSubmodules
import Mathlib.LinearAlgebra.Basis.Basic

namespace PfaffianDescent
section
variable {R S M N : Type*} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] {φ : R →+* S}

lemma span_image_span_semilinear (f : M →ₛₗ[φ] N) (s : Set M) :
    Submodule.span S (f '' (Submodule.span R s : Set M)) = Submodule.span S (f '' s) := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (Submodule.image_span_subset_span f s)
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

end
section
variable (R : Type*) [CommRing R] {m n : ℕ}

/-- The ambient generators of the submodule represented by a graph chart. -/
def grassmannianChartColumn (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R)
    (j : Fin m) : (Fin m → R) × (Fin n → R) :=
  graphCoordinatePermutation R σ.symm (Pi.single j 1, fun i => T i j)

lemma grassmannianChartSubmodule_span (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R) :
    grassmannianChartSubmodule R σ T = Submodule.span R (Set.range (grassmannianChartColumn R σ T)) := by
  let f : (Fin m → R) →ₗ[R] ((Fin m → R) × (Fin n → R)) :=
    (graphCoordinatePermutation R σ.symm).toLinearMap.comp (LinearMap.id.prod (Matrix.toLin' T))
  have he : grassmannianChartSubmodule R σ T = f.range := by
    rw [grassmannianChartSubmodule, LinearMap.graph_eq_range_prod, LinearMap.range_comp]
  rw [he, ← Submodule.map_top f, ← (Pi.basisFun R (Fin m)).span_eq, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext j
  simp [f, grassmannianChartColumn, Pi.basisFun_apply, Matrix.col]
  rfl

/-- The columns of a Grassmannian chart are a free frame for its represented
submodule.  Together with `grassmannianChartSubmodule_span`, this gives the
local universal subspace in a form suitable for constructing families of
homogeneous equations. -/
theorem grassmannianChartColumn_linearIndependent
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    LinearIndependent R (grassmannianChartColumn R σ T) := by
  let f : (Fin m → R) →ₗ[R] ((Fin m → R) × (Fin n → R)) :=
    (graphCoordinatePermutation R σ.symm).toLinearMap.comp
      (LinearMap.id.prod (Matrix.toLin' T))
  have hf : f.ker = ⊥ := by
    apply LinearMap.ker_eq_bot_of_injective
    intro x y hxy
    have hxy' := congrArg Prod.fst
      ((graphCoordinatePermutation R σ.symm).injective hxy)
    simpa [f] using hxy'
  have hcols : f ∘ (Pi.basisFun R (Fin m)) =
      grassmannianChartColumn R σ T := by
    funext j
    simp [f, grassmannianChartColumn, Pi.basisFun_apply, Matrix.col]
    rfl
  rw [← hcols]
  exact (Pi.basisFun R (Fin m)).linearIndependent.map' f hf

/-- The explicit matrix columns form a basis of the Grassmannian chart
submodule.  This packages the universal local subspace as a finite free
module without choosing any additional coordinates. -/
noncomputable def grassmannianChartColumnBasis
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R) :
    Module.Basis (Fin m) R (grassmannianChartSubmodule R σ T) :=
  (Module.Basis.span (grassmannianChartColumn_linearIndependent R σ T)).map
    (LinearEquiv.ofEq _ _ (grassmannianChartSubmodule_span R σ T).symm)

/-- The basis vector of the local universal subspace is the corresponding
explicit Grassmannian chart column in ambient coordinates. -/
theorem grassmannianChartColumnBasis_apply
    (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R)
    (j : Fin m) :
    ((grassmannianChartColumnBasis R σ T j :
      grassmannianChartSubmodule R σ T) : (Fin m → R) × (Fin n → R)) =
      grassmannianChartColumn R σ T j := by
  simp [grassmannianChartColumnBasis]

end
section
variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m n : ℕ}

/-- Coefficient extension in the ambient coordinate module. -/
def graphCoefficientMap : ((Fin m → R) × (Fin n → R)) →ₛₗ[φ] ((Fin m → S) × (Fin n → S)) where
  toFun x := (φ ∘ x.1, φ ∘ x.2)
  map_add' x y := by ext <;> simp [Function.comp_def]
  map_smul' r x := by ext <;> simp [Function.comp_def]

/-- Scalar extension of a submodule, viewed inside the extended ambient coordinate module. -/
def grassmannianSubmoduleBaseChange (W : Submodule R ((Fin m → R) × (Fin n → R))) :
    Submodule S ((Fin m → S) × (Fin n → S)) :=
  Submodule.span S (graphCoefficientMap φ '' (W : Set ((Fin m → R) × (Fin n → R))))

lemma grassmannianChartColumn_map (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R) (j : Fin m) :
    graphCoefficientMap φ (grassmannianChartColumn R σ T j) = grassmannianChartColumn S σ (T.map φ) j := by
  change (φ ∘ (graphCoordinatePermutation R σ.symm (Pi.single j 1, fun i => T i j)).1,
    φ ∘ (graphCoordinatePermutation R σ.symm (Pi.single j 1, fun i => T i j)).2) = _
  rw [← graphCoordinatePermutation_map]
  congr 1
  apply Prod.ext
  · funext i
    simp [Function.comp_def, Pi.single_apply]
  · rfl

/-- Coordinate charts commute with every coefficient-ring homomorphism, including nonflat ones. -/
lemma grassmannianChartSubmodule_baseChange (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) R) :
    grassmannianSubmoduleBaseChange φ (grassmannianChartSubmodule R σ T) =
      grassmannianChartSubmodule S σ (T.map φ) := by
  rw [grassmannianSubmoduleBaseChange, grassmannianChartSubmodule_span,
    span_image_span_semilinear, ← Set.range_comp, grassmannianChartSubmodule_span]
  congr 2
  funext j
  exact grassmannianChartColumn_map φ σ T j

end
end PfaffianDescent
