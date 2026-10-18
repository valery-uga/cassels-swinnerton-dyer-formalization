import AllCharacteristics.TangentHyperplaneGeneric
import PfaffianDescent.QuadraticConjugateDescent

/-!
# The six affine Weil coordinates of a conjugate tangent direction

For a quadratic extension, three extension-valued tangent-plane coordinates
are exactly six ground-field coordinates.  The formulas below construct the
tangent direction and prove its coefficient conjugacy; the geometric
nonvanishing and dominance assertions are deliberately not premises of these
coordinate statements.
-/

namespace PfaffianDescent

open scoped BigOperators

universe u

/-- Solving a hyperplane equation commutes with every field homomorphism. -/
theorem map_hyperplaneInclusion
    {K L : Type u} [Field K] [Field L] (f : K →+* L)
    (g : Fin 4 → K) (k : Fin 4) :
    (hyperplaneInclusion g k).map f =
      hyperplaneInclusion (fun i => f (g i)) k := by
  classical
  ext i j
  simp only [Matrix.map_apply, hyperplaneInclusion]
  split_ifs <;> simp [map_inv₀]

/-- Two coefficients in the ground field encode one coordinate in a
quadratic extension.  Applying this to three coordinates gives affine six
space, without requiring any nonzero parameter.
-/
noncomputable def quadraticWeilCoordinates
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (b : Module.Basis (Fin 2) K L) (u : Fin 2 → Fin 3 → K) : Fin 3 → L :=
  fun j => ∑ i, u i j • b i

/-- The six coordinates parametrize all triples in the quadratic extension. -/
theorem quadraticWeilCoordinates_surjective
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (b : Module.Basis (Fin 2) K L) :
    Function.Surjective (quadraticWeilCoordinates b) := by
  intro x
  refine ⟨fun i j => b.repr (x j) i, ?_⟩
  funext j
  exact b.sum_repr (x j)

/-- Coefficient conjugation acts on the extension basis and fixes all six
ground-field parameters. -/
theorem quadraticWeilCoordinates_conjugate
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (b : Module.Basis (Fin 2) K L) (σ : L ≃ₐ[K] L)
    (u : Fin 2 → Fin 3 → K) :
    (fun j => σ (quadraticWeilCoordinates b u j)) =
      quadraticWeilCoordinates (b.map σ.toLinearEquiv) u := by
  funext j
  simp only [quadraticWeilCoordinates, map_sum, map_smul,
    Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply]

/-- The explicit tangent direction over the quadratic extension in terms of
six affine parameters over the ground field. -/
noncomputable def quadraticWeilTangentDirection
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (b : Module.Basis (Fin 2) K L)
    (g : Fin 4 → L) (k : Fin 4) (u : Fin 2 → Fin 3 → K) : Fin 4 → L :=
  (hyperplaneInclusion g k).mulVec (quadraticWeilCoordinates b u)

/-- Every affine parameter choice satisfies the tangent hyperplane equation. -/
theorem quadraticWeilTangentDirection_mem_hyperplane
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (b : Module.Basis (Fin 2) K L)
    (g : Fin 4 → L) (k : Fin 4) (hk : g k ≠ 0)
    (u : Fin 2 → Fin 3 → K) :
    ∑ i, g i * quadraticWeilTangentDirection b g k u i = 0 := by
  simpa only [quadraticWeilTangentDirection, RingHom.coe_id, Matrix.map_id,
    RingHom.id_apply] using
    hyperplaneInclusion_dot_mulVec_zero (RingHom.id L) g k hk
      (quadraticWeilCoordinates b u)

/-- The explicit six-parameter direction conjugates to the direction obtained
by conjugating the gradient and extension basis. -/
theorem quadraticWeilTangentDirection_conjugate
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (b : Module.Basis (Fin 2) K L) (σ : L ≃ₐ[K] L)
    (g : Fin 4 → L) (k : Fin 4) (u : Fin 2 → Fin 3 → K) :
    (fun i => σ (quadraticWeilTangentDirection b g k u i)) =
      quadraticWeilTangentDirection (b.map σ.toLinearEquiv)
        (fun i => σ (g i)) k u := by
  have hu := quadraticWeilCoordinates_conjugate b σ u
  have hg := map_hyperplaneInclusion σ.toRingHom g k
  funext i
  change σ (∑ j, hyperplaneInclusion g k i j * quadraticWeilCoordinates b u j) =
    ∑ j, hyperplaneInclusion (fun l => σ (g l)) k i j *
      quadraticWeilCoordinates (b.map σ.toLinearEquiv) u j
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul]
  have hmatrix := congrArg (fun M => M i j) hg
  have hcoord := congrFun hu j
  exact congrArg₂ (· * ·) hmatrix hcoord

end PfaffianDescent

namespace AllCharacteristics

open PfaffianDescent MvPolynomial

universe u

/-- Using the actual cubic gradient in the preceding coordinates gives a
genuine tangent direction at the specified point, over any ground field. -/
theorem mixed_quadraticWeilTangentDirection_eq_zero
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (b : Module.Basis (Fin 2) K L) (c : Cubic L 4) (p : Fin 4 → L)
    (k : Fin 4) (hk : (MvPolynomial.pderiv k c.toMvPolynomial).eval p ≠ 0)
    (u : Fin 2 → Fin 3 → K) :
    c.mixed p
      (quadraticWeilTangentDirection b
        (fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval p) k u) = 0 := by
  rw [Cubic.mixed_eq_sum_pderiv_eval]
  simpa only [mul_comm] using quadraticWeilTangentDirection_mem_hyperplane b
    (fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval p) k hk u

/-- The residual tangent operation applied to these six explicit affine
parameters lies on the original cubic. -/
theorem eval_quadraticWeilTangentResidual_eq_zero
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (b : Module.Basis (Fin 2) K L) (c : Cubic L 4) (p : Fin 4 → L)
    (hp : c.eval p = 0)
    (k : Fin 4) (hk : (MvPolynomial.pderiv k c.toMvPolynomial).eval p ≠ 0)
    (u : Fin 2 → Fin 3 → K) :
    c.eval (Cubic.tangentResidualPoint c p
      (quadraticWeilTangentDirection b
        (fun i => (MvPolynomial.pderiv i c.toMvPolynomial).eval p) k u)) = 0 := by
  exact Cubic.eval_tangentResidualPoint c p _ hp
    (mixed_quadraticWeilTangentDirection_eq_zero b c p k hk u)

end AllCharacteristics
