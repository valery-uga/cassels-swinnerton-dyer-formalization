import AllCharacteristics.FinitePointFieldDescent
import AllCharacteristics.CoprimeEffectiveCycle
import AllCharacteristics.HomogeneousClosedPoints

/-!
# Descending the degree-one zero-cycle condition to finitely generated fields

Extract a closed point of degree prime to three from the source signed cycle.
Descend its finite residue extension and coordinates along with the smooth
cubic equation. The full extension degree is preserved, so a degree-three
cycle and Bézout construct a degree-one cycle on the descended cubic. This
proves the finite-data reduction for the existence assertion over every field.
-/

open AlgebraicGeometry
namespace AllCharacteristics
open HomogeneousProjective
universe u

/-- A nonzero smooth cubic with a signed degree-one cycle over any field
has an exact smooth equation model over a finitely generated subfield, and
that model itself has a signed degree-one cycle. -/
theorem exists_fg_subfield_smooth_cubic_degree_one_model
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp)) (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ F : Subfield k, Field.FG F ∧
      ∃ q : MvPolynomial (Fin 4) F, ∃ hq : q.IsHomogeneous 3,
        q.map F.subtype = p ∧ q ≠ 0 ∧ Smooth (hypersurfaceToBase q hq) ∧
        ∃ w : ZeroCycle (hypersurface q hq), ZeroCycle.degree (hypersurfaceToBase q hq) w = 1 := by
  let f := hypersurfaceToBase p hp
  obtain ⟨x, _, hx⟩ := ZeroCycle.exists_coprime_degree f z hz
  let := pointAlgebra f x.1
  have := closedPoint_moduleFinite f x
  obtain ⟨v, hv, he⟩ := hypersurface_residueField_coordinates p hp x.1
  obtain ⟨F, hF, q, hq, hmap, hqne, hs, E, _, _, _, c, hdegree, _, y, hy, hey, _⟩ :=
    exists_fg_subfield_smooth_point_model p hp hne v hv he
  obtain ⟨a, ha⟩ := hypersurface_point_of_coordinates (algebraMap F E) q hq y hy hey
  obtain ⟨w, hw⟩ := exists_effectiveZeroCycle_of_finite_algebra_point (hypersurfaceToBase q hq) a ha
  have hc : Nat.Coprime (EffectiveZeroCycle.degree (hypersurfaceToBase q hq) w) 3 := by
    rw [hw, hdegree, closedPoint_finrank_eq_residueDegree f x]
    exact hx
  exact ⟨F, hF, q, hq, hmap, hqne, hs,
    cubicSurface_zeroCycle_degree_one_of_effective_coprime q hq w hc⟩

end AllCharacteristics
