import AllCharacteristics.ArbitraryFieldCubicPointDescent
import PfaffianDescent.PerfectFieldClosedPointGeometricPosition

/-! Literal statement wrappers for the two parts of `lem:position` and the
closed-point alternative in `prop:four-five` of `2-proofs.tex`.
The stronger degree-four/five point theorem supplies the rational-point
alternative; no particular residual-intersection construction is asserted. -/

noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory
open HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Both parts of the position lemma over the manuscript's perfect field,
for the actual original closed point and its residue-field immersion. -/
theorem twoProofs_position_perfect
    {k : Type u} [Field k] [PerfectField k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 4 ∨
      (hypersurfaceToBase p hp).residueDegree x.1 = 5) :
    let coplanar := ∃ c : Fin 4 → k, c ≠ 0 ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal (PfaffianDescent.homogeneousLinearForm c) ∈
        x.1.asHomogeneousIdeal.toIdeal
    (coplanar → ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ∧
    (¬ coplanar → PfaffianDescent.ProjectiveGeometricGeneralPosition (equationIdeal p hp)
      ((hypersurface p hp).fromSpecResidueField x.1)) := by
  dsimp only
  constructor
  · intro _
    exact cubic_section_of_closedPoint_degree_four_or_five p hp hne x hx
  · intro hplane
    exact PfaffianDescent.perfectField_cubic_closedPoint_degree_four_or_five_general_position
      p hp x hx hplane

/-- Cassels's finer closed-point alternative. The checked stronger descent
always supplies its first branch, over any field. For degrees four and five,
`9 - residueDegree x` is precisely the other degree. -/
theorem twoProofs_cassels_four_five_closed_point_alternative
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 4 ∨
      (hypersurfaceToBase p hp).residueDegree x.1 = 5) :
    (∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
    (∃ y : closedPoints (hypersurface p hp),
      (hypersurfaceToBase p hp).residueDegree y.1 =
        9 - (hypersurfaceToBase p hp).residueDegree x.1) :=
  Or.inl (cubic_section_of_closedPoint_degree_four_or_five p hp hne x hx)

end AllCharacteristics
