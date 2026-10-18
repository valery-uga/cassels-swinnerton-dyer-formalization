import AllCharacteristics.UniversalSecantPolynomial
import Mathlib.RingTheory.Localization.FractionRing

namespace PfaffianDescent

open MvPolynomial
open scoped BigOperators

universe u

/-- A matrix with tangent columns parametrizes only tangent directions. -/
theorem mixed_matrix_mulVec_eq_zero_of_columns
    {L : Type u} [Field L] (c : Cubic L 4) (x : Fin 4 → L)
    (M : Matrix (Fin 4) (Fin 3) L)
    (hM : ∀ j, c.mixed x (fun i => M i j) = 0) (w : Fin 3 → L) :
    c.mixed x (M.mulVec w) = 0 := by
  have hvec : M.mulVec w = ∑ j, w j • (fun i => M i j) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [hvec]
  change Cubic.tangentLinear c x (∑ j, w j • (fun i => M i j)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_smul]
  change w j • c.mixed x (fun i => M i j) = 0
  rw [hM j, smul_zero]

/-- Evaluating at the formal generic variables is exactly the canonical
inclusion of the polynomial ring in its fraction field. -/
theorem eval₂Hom_fractionRing_variables
    {L : Type u} [Field L] :
    MvPolynomial.eval₂Hom
      (algebraMap L (FractionRing (MvPolynomial ConjugateTangentParameterIndex L)))
      (fun j => algebraMap (MvPolynomial ConjugateTangentParameterIndex L)
        (FractionRing (MvPolynomial ConjugateTangentParameterIndex L)) (MvPolynomial.X j)) =
      algebraMap (MvPolynomial ConjugateTangentParameterIndex L)
        (FractionRing (MvPolynomial ConjugateTangentParameterIndex L)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [MvPolynomial.eval₂Hom_C]
    exact (IsScalarTower.algebraMap_apply L
      (MvPolynomial ConjugateTangentParameterIndex L) _ r).symm
  · intro j
    exact MvPolynomial.eval₂Hom_X' _ _ j

/-- The raw six-variable secant polynomial satisfies the cubic identically.
All that is required is that the two matrices have tangent columns.  The
proof works over finite fields as well, by evaluating at formal generic
variables in the polynomial fraction field and using injectivity. -/
theorem eval_universalTwoTangentSecantPolynomial_eq_zero
    {L : Type u} [Field L] (c : Cubic L 4) (x y : Fin 4 → L)
    (hx : c.eval x = 0) (hy : c.eval y = 0)
    (M N : Matrix (Fin 4) (Fin 3) L)
    (hM : ∀ j, c.mixed x (fun i => M i j) = 0)
    (hN : ∀ j, c.mixed y (fun i => N i j) = 0) (a b : L) :
    (c.map MvPolynomial.C).eval
      (universalTwoTangentSecantPolynomial c x y M N a b) = 0 := by
  let P := MvPolynomial ConjugateTangentParameterIndex L
  let E := FractionRing P
  let f : L →+* E := algebraMap L E
  let iP : P →+* E := algebraMap P E
  let z : ConjugateTangentParameterIndex → E := fun j => iP (MvPolynomial.X j)
  let cP := c.map (MvPolynomial.C : L →+* P)
  let rP := universalTwoTangentSecantPolynomial c x y M N a b
  have hinc : MvPolynomial.eval₂Hom f z = iP := eval₂Hom_fractionRing_variables
  have hc : cP.map iP = c.map f := by
    funext i
    exact IsScalarTower.algebraMap_apply L P E (c i)
  have hr : (fun i => iP (rP i)) =
      Cubic.secantResidualPoint (c.map f)
        (Cubic.tangentResidualPoint (c.map f) (fun i => f (x i))
          ((M.map f).mulVec (fun j => z (0, j) + f a * z (1, j))))
        (Cubic.tangentResidualPoint (c.map f) (fun i => f (y i))
          ((N.map f).mulVec (fun j => z (0, j) + f b * z (1, j)))) := by
    rw [← hinc]
    exact eval₂_universalTwoTangentSecantPolynomial f c x y M N a b z
  have hxE : (c.map f).eval (fun i => f (x i)) = 0 := by
    rw [Cubic.eval_map, hx, map_zero]
  have hyE : (c.map f).eval (fun i => f (y i)) = 0 := by
    rw [Cubic.eval_map, hy, map_zero]
  have hME : ∀ j, (c.map f).mixed (fun i => f (x i))
      (fun i => (M.map f) i j) = 0 := by
    intro j
    change (c.map f).mixed (fun i => f (x i)) (fun i => f (M i j)) = 0
    rw [Cubic.mixed_map, hM j, map_zero]
  have hNE : ∀ j, (c.map f).mixed (fun i => f (y i))
      (fun i => (N.map f) i j) = 0 := by
    intro j
    change (c.map f).mixed (fun i => f (y i)) (fun i => f (N i j)) = 0
    rw [Cubic.mixed_map, hN j, map_zero]
  have hzero : (c.map f).eval (fun i => iP (rP i)) = 0 := by
    rw [hr]
    apply Cubic.eval_secantResidualPoint
    · exact Cubic.eval_tangentResidualPoint _ _ _ hxE
        (mixed_matrix_mulVec_eq_zero_of_columns _ _ _ hME _)
    · exact Cubic.eval_tangentResidualPoint _ _ _ hyE
        (mixed_matrix_mulVec_eq_zero_of_columns _ _ _ hNE _)
  apply IsFractionRing.injective P E
  rw [map_zero]
  have hmap := Cubic.eval_map iP cP rP
  rw [hc, hzero] at hmap
  exact hmap.symm

end PfaffianDescent
