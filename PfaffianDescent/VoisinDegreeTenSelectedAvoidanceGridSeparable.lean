import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceConcreteGrid
import AllCharacteristics.TangentHyperplaneGeneric
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! # The nine native cubic line restrictions are separable

An affine root of any grid line restriction would be an actual rational point
of the original surface. Consequently each degree-three restriction is
irreducible and, in characteristic zero, separable. These certificates come
from the actual cubic; no separability condition is supplied by the caller.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Evaluation of the chosen tensor at the excluded infinity point is
nonzero. -/
theorem voisinDegreeTenSelectedAvoidance_grid_tensor_infinity_ne_zero
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (c : Cubic K 4) (hc : c.toMvPolynomial = p) :
    c.eval (voisinDegreeTenSelectedAvoidance_gridInfinity K) ≠ 0 := by
  have hne := voisinDegreeTenSelectedAvoidance_eval_ne_zero_of_no_section p hp hno
    (voisinDegreeTenSelectedAvoidance_gridInfinity K) (by
      intro h
      have h3 := congrFun h 3
      simpa [voisinDegreeTenSelectedAvoidance_gridInfinity] using h3)
  have hec : c.toMvPolynomial.eval (voisinDegreeTenSelectedAvoidance_gridInfinity K) =
      c.eval (voisinDegreeTenSelectedAvoidance_gridInfinity K) := by
    change MvPolynomial.eval₂ (RingHom.id K)
      (voisinDegreeTenSelectedAvoidance_gridInfinity K) c.toMvPolynomial = _
    rw [Cubic.eval_toMvPolynomial]
    rfl
  rw [← hec, hc]
  exact hne

/-- Every native grid line polynomial is irreducible over the ground field
because a root would supply a rational point of the surface. -/
theorem voisinDegreeTenSelectedAvoidance_grid_linePolynomial_irreducible
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (c : Cubic K 4) (hc : c.toMvPolynomial = p) (a b : Fin 3) :
    Irreducible (cubicLinePolynomial c
      (voisinDegreeTenSelectedAvoidance_gridInfinity K)
      (voisinDegreeTenSelectedAvoidance_gridBase K a b)) := by
  have hdeg := cubicLinePolynomial_natDegree c
    (voisinDegreeTenSelectedAvoidance_gridInfinity K)
    (voisinDegreeTenSelectedAvoidance_gridBase K a b)
    (voisinDegreeTenSelectedAvoidance_grid_tensor_infinity_ne_zero p hp hno c hc)
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by rw [hdeg]; decide)
  intro t ht
  let v := t • voisinDegreeTenSelectedAvoidance_gridInfinity K +
    voisinDegreeTenSelectedAvoidance_gridBase K a b
  have hv : v ≠ 0 := by
    intro hv0
    have h0 := congrFun hv0 0
    simpa [v, voisinDegreeTenSelectedAvoidance_gridInfinity,
      voisinDegreeTenSelectedAvoidance_gridBase] using h0
  apply voisinDegreeTenSelectedAvoidance_eval_ne_zero_of_no_section p hp hno v hv
  have ht' : (cubicLinePolynomial c
      (voisinDegreeTenSelectedAvoidance_gridInfinity K)
      (voisinDegreeTenSelectedAvoidance_gridBase K a b)).eval₂ (RingHom.id K) t = 0 := ht
  rw [cubicLinePolynomial_eval₂ (RingHom.id K)] at ht'
  change c.eval v = 0 at ht'
  rw [← hc]
  change MvPolynomial.eval₂ (RingHom.id K) v c.toMvPolynomial = 0
  rw [Cubic.eval_toMvPolynomial]
  exact ht'

/-- The nine ground-field line restrictions are separable in characteristic
zero. -/
theorem voisinDegreeTenSelectedAvoidance_grid_linePolynomial_separable
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (c : Cubic K 4) (hc : c.toMvPolynomial = p) (a b : Fin 3) :
    (cubicLinePolynomial c (voisinDegreeTenSelectedAvoidance_gridInfinity K)
      (voisinDegreeTenSelectedAvoidance_gridBase K a b)).Separable :=
  (voisinDegreeTenSelectedAvoidance_grid_linePolynomial_irreducible p hp hno c hc a b).separable

/-- Mapping the original native line polynomial is exactly the line
polynomial of the mapped tensor and the literal mapped grid vectors. -/
theorem voisinDegreeTenSelectedAvoidance_grid_linePolynomial_map
    {K L : Type u} [Field K] [Field L] (φ : K →+* L)
    (c : Cubic K 4) (a b : Fin 3) :
    (cubicLinePolynomial c (voisinDegreeTenSelectedAvoidance_gridInfinity K)
      (voisinDegreeTenSelectedAvoidance_gridBase K a b)).map φ =
    cubicLinePolynomial (c.map φ) (voisinDegreeTenSelectedAvoidance_gridInfinity L)
      (voisinDegreeTenSelectedAvoidance_gridBase L a b) := by
  have hu : (fun i => φ (voisinDegreeTenSelectedAvoidance_gridInfinity K i)) =
      voisinDegreeTenSelectedAvoidance_gridInfinity L := by
    ext i
    fin_cases i <;> simp [voisinDegreeTenSelectedAvoidance_gridInfinity]
  have hv : (fun i => φ (voisinDegreeTenSelectedAvoidance_gridBase K a b i)) =
      voisinDegreeTenSelectedAvoidance_gridBase L a b := by
    ext i
    fin_cases i <;> simp [voisinDegreeTenSelectedAvoidance_gridBase,
      voisinDegreeTenSelectedAvoidance_gridSlope]
  rw [← hu, ← hv]
  simp only [cubicLinePolynomial, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, Cubic.eval_map, Cubic.mixed_map]

end PfaffianDescent
