import AllCharacteristics.HomogeneousClosedPoints
import AllCharacteristics.CubicPolynomialCoordinates

/-!
# Quadratic secants for actual projective cubic schemes

The coordinate secant proof applies to actual closed points, retaining their
full residue degree. In particular an effective degree-four cycle on a cubic
hypersurface gives either a rational point or a degree-four closed point over
every field.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
namespace HomogeneousProjective
universe u

/-- A closed point of degree at most two on an actual cubic hypersurface gives
a rational point in every characteristic. Inseparable quadratic points are
included. -/
theorem hypersurface_section_of_closedPoint_degree_le_two
    {k : Type u} [Field k] {n : ℕ}
    (p : MvPolynomial (Fin n) k) (hp : p.IsHomogeneous 3)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 ≤ 2) :
    ∃ q : Spec (.of k) ⟶ hypersurface p hp, q ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  let X := hypersurface p hp
  let f := hypersurfaceToBase p hp
  let := pointAlgebra f x.1
  have := closedPoint_moduleFinite f x
  obtain ⟨v, hv, he⟩ := hypersurface_residueField_coordinates p hp x.1
  have hd : Module.finrank k (X.residueField x.1) ≤ 2 :=
    (closedPoint_finrank_eq_residueDegree f x).trans_le hx
  obtain ⟨y, hy, hey⟩ := homogeneous_cubic_degree_le_two_descent p hp hd v hv he
  obtain ⟨q, hq⟩ := hypersurface_point_of_coordinates (RingHom.id k) p hp y hy hey
  exact ⟨q, by simpa using hq⟩

/-- The effective-cycle form of the secant lemma: an effective zero-cycle of
degree one or two on a cubic hypersurface gives a rational section. -/
theorem hypersurface_section_of_effective_cycle_degree_one_or_two
    {k : Type u} [Field k] {n : ℕ}
    (p : MvPolynomial (Fin n) k) (hp : p.IsHomogeneous 3)
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 1 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 2) :
    ∃ q : Spec (.of k) ⟶ hypersurface p hp,
      q ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  classical
  have small (d : ℕ)
      (hd : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = d)
      (hdpos : 0 < d) (hdle : d ≤ 2) :
      ∃ q : Spec (.of k) ⟶ hypersurface p hp,
        q ≫ hypersurfaceToBase p hp = 𝟙 _ := by
    have hsum : (∑ x ∈ z.support,
        z x * (hypersurfaceToBase p hp).residueDegree x.val) = d := hd
    obtain ⟨x, hx, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (hsum.trans_ne (Nat.ne_of_gt hdpos))
    have hweight : 0 < z x := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)
    have hterm : z x * (hypersurfaceToBase p hp).residueDegree x.val ≤ 2 := by
      calc
        z x * (hypersurfaceToBase p hp).residueDegree x.val ≤
            ∑ y ∈ z.support, z y * (hypersurfaceToBase p hp).residueDegree y.val := by
              exact Finset.single_le_sum (s := z.support)
                (f := fun y : closedPoints (hypersurface p hp) =>
                  z y * (hypersurfaceToBase p hp).residueDegree y.val)
                (fun _ _ => Nat.zero_le _) hx
        _ = d := hsum
        _ ≤ 2 := hdle
    have hdegree : (hypersurfaceToBase p hp).residueDegree x.val ≤ 2 :=
      (Nat.le_mul_of_pos_left _ hweight).trans hterm
    exact hypersurface_section_of_closedPoint_degree_le_two p hp x hdegree
  rcases hz with hz | hz
  · exact small 1 hz (by omega) (by omega)
  · exact small 2 hz (by omega) (by omega)

/-- An effective degree-four cycle on an actual cubic hypersurface gives a
rational point or a degree-four closed point in its support, over every field. -/
theorem hypersurface_section_or_quartic_of_effective_degree_four
    {k : Type u} [Field k] {n : ℕ}
    (p : MvPolynomial (Fin n) k) (hp : p.IsHomogeneous 3)
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4) :
    (∃ q : Spec (.of k) ⟶ hypersurface p hp, q ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
      ∃ x ∈ z.support, (hypersurfaceToBase p hp).residueDegree x.1 = 4 := by
  obtain ⟨x, hx, hd⟩ := EffectiveZeroCycle.exists_degree_one_two_four
    (hypersurfaceToBase p hp) z hz
  rcases hd with h₁ | h₂ | h₄
  · exact Or.inl (hypersurface_section_of_closedPoint_degree_le_two p hp x (by omega))
  · exact Or.inl (hypersurface_section_of_closedPoint_degree_le_two p hp x (by omega))
  · exact Or.inr ⟨x, hx, h₄⟩

/-- A rank-four finite closed subscheme of an actual cubic hypersurface gives
a rational point or a degree-four closed point, without any characteristic,
reducedness, or separability assumption. -/
theorem hypersurface_section_or_quartic_of_finite_closed_subscheme_rank_four
    {k : Type u} [Field k] {n : ℕ}
    (p : MvPolynomial (Fin n) k) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hi : finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 4) :
    (∃ q : Spec (.of k) ⟶ hypersurface p hp, q ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
      ∃ x : closedPoints (hypersurface p hp),
        (hypersurfaceToBase p hp).residueDegree x.1 = 4 := by
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_of_finite_closed_subscheme i
    (hypersurfaceToBase p hp)
  rcases hypersurface_section_or_quartic_of_effective_degree_four p hp z (hz.trans hi) with
    h | ⟨x, _, hx⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, hx⟩

end HomogeneousProjective
end AllCharacteristics
