import PfaffianDescent.CubicSecant
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.MvPolynomial.CommRing

namespace PfaffianDescent

open MvPolynomial
open scoped BigOperators

universe u

abbrev ConjugateTangentParameterIndex := Fin 2 × Fin 3

/-- A polynomial tangent direction with three constant and three root
coefficients.  Its six variables are retained for exact specialization. -/
noncomputable def universalTangentDirectionPolynomial
    {L : Type u} [Field L] (M : Matrix (Fin 4) (Fin 3) L) (a : L) :
    Fin 4 → MvPolynomial ConjugateTangentParameterIndex L :=
  (M.map MvPolynomial.C).mulVec
    (fun j => MvPolynomial.X (0, j) + MvPolynomial.C a * MvPolynomial.X (1, j))

/-- The raw third-intersection vector, polynomial in all six tangent
parameters over the residual splitting field. -/
noncomputable def universalTwoTangentSecantPolynomial
    {L : Type u} [Field L] (c : Cubic L 4) (x y : Fin 4 → L)
    (M N : Matrix (Fin 4) (Fin 3) L) (a b : L) :
    Fin 4 → MvPolynomial ConjugateTangentParameterIndex L :=
  Cubic.secantResidualPoint (c.map MvPolynomial.C)
    (Cubic.tangentResidualPoint (c.map MvPolynomial.C)
      (fun i => MvPolynomial.C (x i)) (universalTangentDirectionPolynomial M a))
    (Cubic.tangentResidualPoint (c.map MvPolynomial.C)
      (fun i => MvPolynomial.C (y i)) (universalTangentDirectionPolynomial N b))

/-- Specializing all six variables gives the literal matrix tangent
directions at the two roots. -/
theorem eval_universalTangentDirectionPolynomial
    {L : Type u} [Field L] (M : Matrix (Fin 4) (Fin 3) L) (a : L)
    (z : ConjugateTangentParameterIndex → L) :
    (fun i => MvPolynomial.eval z (universalTangentDirectionPolynomial M a i)) =
      M.mulVec (fun j => z (0, j) + a * z (1, j)) := by
  funext i
  simp [universalTangentDirectionPolynomial, Matrix.mulVec, dotProduct]

/-- The same identity after any coefficient field extension, allowing
specialization at geometric preimages over a larger field. -/
theorem eval₂_universalTangentDirectionPolynomial
    {L E : Type u} [Field L] [Field E] (f : L →+* E)
    (M : Matrix (Fin 4) (Fin 3) L) (a : L)
    (z : ConjugateTangentParameterIndex → E) :
    (fun i => MvPolynomial.eval₂ f z (universalTangentDirectionPolynomial M a i)) =
      (M.map f).mulVec (fun j => z (0, j) + f a * z (1, j)) := by
  funext i
  simp [universalTangentDirectionPolynomial, Matrix.mulVec, dotProduct]

/-- The raw universal polynomial retains its exact coordinates after any
field extension and all six parameter specializations. -/
theorem eval₂_universalTwoTangentSecantPolynomial
    {L E : Type u} [Field L] [Field E] (f : L →+* E)
    (c : Cubic L 4) (x y : Fin 4 → L)
    (M N : Matrix (Fin 4) (Fin 3) L) (a b : L)
    (z : ConjugateTangentParameterIndex → E) :
    (fun i => MvPolynomial.eval₂ f z
      (universalTwoTangentSecantPolynomial c x y M N a b i)) =
      Cubic.secantResidualPoint (c.map f)
        (Cubic.tangentResidualPoint (c.map f) (fun i => f (x i))
          ((M.map f).mulVec (fun j => z (0, j) + f a * z (1, j))))
        (Cubic.tangentResidualPoint (c.map f) (fun i => f (y i))
          ((N.map f).mulVec (fun j => z (0, j) + f b * z (1, j)))) := by
  let e : MvPolynomial ConjugateTangentParameterIndex L →+* E := MvPolynomial.eval₂Hom f z
  let cP := c.map (MvPolynomial.C : L →+* MvPolynomial ConjugateTangentParameterIndex L)
  have hc : cP.map e = c.map f := by
    funext i
    simp [cP, Cubic.map, e]
  have hx : (fun i => e (MvPolynomial.C (x i))) = fun i => f (x i) := by
    funext i
    simp [e]
  have hy : (fun i => e (MvPolynomial.C (y i))) = fun i => f (y i) := by
    funext i
    simp [e]
  change (fun i => e (Cubic.secantResidualPoint cP
    (Cubic.tangentResidualPoint cP (fun i => MvPolynomial.C (x i))
      (universalTangentDirectionPolynomial M a))
    (Cubic.tangentResidualPoint cP (fun i => MvPolynomial.C (y i))
      (universalTangentDirectionPolynomial N b)) i)) = _
  rw [← Cubic.map_secantResidualPoint,
    ← Cubic.map_tangentResidualPoint e cP (fun i => MvPolynomial.C (x i)),
    ← Cubic.map_tangentResidualPoint e cP (fun i => MvPolynomial.C (y i)), hc, hx, hy]
  change (Cubic.secantResidualPoint (c.map f)
    (Cubic.tangentResidualPoint (c.map f) (fun i => f (x i))
      (fun i => MvPolynomial.eval₂ f z (universalTangentDirectionPolynomial M a i)))
    (Cubic.tangentResidualPoint (c.map f) (fun i => f (y i))
      (fun i => MvPolynomial.eval₂ f z (universalTangentDirectionPolynomial N b i)))) = _
  rw [eval₂_universalTangentDirectionPolynomial f M a z,
    eval₂_universalTangentDirectionPolynomial f N b z]

/-- The entire raw secant vector specializes exactly, retaining its
homogeneous coordinates rather than merely its projective image. -/
theorem eval_universalTwoTangentSecantPolynomial
    {L : Type u} [Field L] (c : Cubic L 4) (x y : Fin 4 → L)
    (M N : Matrix (Fin 4) (Fin 3) L) (a b : L)
    (z : ConjugateTangentParameterIndex → L) :
    (fun i => MvPolynomial.eval z
      (universalTwoTangentSecantPolynomial c x y M N a b i)) =
      Cubic.secantResidualPoint c
        (Cubic.tangentResidualPoint c x
          (M.mulVec (fun j => z (0, j) + a * z (1, j))))
        (Cubic.tangentResidualPoint c y
          (N.mulVec (fun j => z (0, j) + b * z (1, j)))) := by
  let e : MvPolynomial ConjugateTangentParameterIndex L →+* L := MvPolynomial.eval z
  let cP := c.map (MvPolynomial.C : L →+* MvPolynomial ConjugateTangentParameterIndex L)
  have hc : cP.map e = c := by
    funext i
    simp [cP, Cubic.map, e]
  have hx : (fun i => e (MvPolynomial.C (x i))) = x := by
    funext i
    simp [e]
  have hy : (fun i => e (MvPolynomial.C (y i))) = y := by
    funext i
    simp [e]
  change (fun i => e (Cubic.secantResidualPoint cP
    (Cubic.tangentResidualPoint cP (fun i => MvPolynomial.C (x i))
      (universalTangentDirectionPolynomial M a))
    (Cubic.tangentResidualPoint cP (fun i => MvPolynomial.C (y i))
      (universalTangentDirectionPolynomial N b)) i)) = _
  rw [← Cubic.map_secantResidualPoint,
    ← Cubic.map_tangentResidualPoint e cP (fun i => MvPolynomial.C (x i)),
    ← Cubic.map_tangentResidualPoint e cP (fun i => MvPolynomial.C (y i)), hc, hx, hy]
  rw [eval_universalTangentDirectionPolynomial M a z,
    eval_universalTangentDirectionPolynomial N b z]

/-- A nonzero specialization certifies that the generic raw vector is
nonzero as a vector of polynomials. -/
theorem universalTwoTangentSecantPolynomial_ne_zero_of_specialization
    {L : Type u} [Field L] (c : Cubic L 4) (x y : Fin 4 → L)
    (M N : Matrix (Fin 4) (Fin 3) L) (a b : L)
    (z : ConjugateTangentParameterIndex → L)
    (hz : Cubic.secantResidualPoint c
      (Cubic.tangentResidualPoint c x
        (M.mulVec (fun j => z (0, j) + a * z (1, j))))
      (Cubic.tangentResidualPoint c y
        (N.mulVec (fun j => z (0, j) + b * z (1, j)))) ≠ 0) :
    universalTwoTangentSecantPolynomial c x y M N a b ≠ 0 := by
  intro hzero
  apply hz
  rw [← eval_universalTwoTangentSecantPolynomial c x y M N a b z, hzero]
  funext i
  exact map_zero (MvPolynomial.eval z)

end PfaffianDescent
