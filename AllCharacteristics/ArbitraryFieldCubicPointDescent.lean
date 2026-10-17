import AllCharacteristics.FinitePointFieldDescent
import AllCharacteristics.FinitelyGeneratedCubicDescent
import AllCharacteristics.ProperCyclePushforward

/-!
# Cubic degree-four/five descent over arbitrary fields

A finite-extension point and its smooth cubic equation descend to a finitely
generated subfield without changing the extension degree. The constructed
mixed-characteristic DVR proof applies there. Its rational coordinates map
back to the original field. Combining this with the proved characteristic-zero
inputs gives degree-four/five descent with no restriction on the field.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
open HomogeneousProjective
universe u
variable {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]

/-- Degree-four/five finite-extension points on smooth cubics descend to
rational points over every field of positive characteristic. -/
theorem cubic_coordinates_of_finite_point_degree_four_or_five_positive
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hd : Module.finrank k L = 4 ∨ Module.finrank k L = 5)
    (x : Fin 4 → L) (hx : x ≠ 0) (heval : p.eval₂ (algebraMap k L) x = 0) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain ⟨F, hF, q, hq, he, hqne, hs, E, _, _, _, c, hdegree, _, y, hy, hey, _⟩ :=
    exists_fg_subfield_smooth_point_model p hp hne x hx heval
  have : Field.FG F := hF
  have : Smooth (hypersurfaceToBase q hq) := hs
  obtain ⟨a, ha⟩ := hypersurface_point_of_coordinates (algebraMap F E) q hq y hy hey
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_of_finite_algebra_point (hypersurfaceToBase q hq) a ha
  have hdeg : EffectiveZeroCycle.degree (hypersurfaceToBase q hq) z = 4 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase q hq) z = 5 := by
    rw [hz, hdegree]
    exact hd
  obtain ⟨v, hv, hve⟩ := cubic_coordinates_of_effective_degree_four_or_five_fg_positive
    ℓ q hq hqne z hdeg
  refine ⟨F.subtype ∘ v, ?_, ?_⟩
  · intro hzero
    apply hv
    funext i
    apply F.subtype.injective
    exact (congrFun hzero i).trans (map_zero F.subtype).symm
  · rw [← he, MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp, hve, map_zero]

/-- A smooth cubic with a point over an extension of degree four or five
has rational coordinates over an arbitrary field, in every characteristic. -/
theorem cubic_coordinates_of_finite_point_degree_four_or_five
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hd : Module.finrank k L = 4 ∨ Module.finrank k L = 5)
    (x : Fin 4 → L) (hx : x ≠ 0) (heval : p.eval₂ (algebraMap k L) x = 0) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  rcases CharP.exists' k with hzero | ⟨ℓ, hprime, hchar⟩
  · rcases hd with hd | hd
    · exact PfaffianDescent.homogeneous_cubic_degree_four_descent p hp hd x hx heval
    · exact PfaffianDescent.homogeneous_cubic_degree_five_descent p hp hd x hx heval
  · exact cubic_coordinates_of_finite_point_degree_four_or_five_positive ℓ p hp hne hd x hx heval

/-- A closed point of degree four or five on a nonzero smooth cubic surface
gives an actual rational section over every field. -/
theorem cubic_section_of_closedPoint_degree_four_or_five
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 4 ∨
      (hypersurfaceToBase p hp).residueDegree x.1 = 5) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp, a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  let f := hypersurfaceToBase p hp
  let := pointAlgebra f x.1
  have := closedPoint_moduleFinite f x
  obtain ⟨v, hv, he⟩ := hypersurface_residueField_coordinates p hp x.1
  have hd : Module.finrank k ((hypersurface p hp).residueField x.1) = 4 ∨
      Module.finrank k ((hypersurface p hp).residueField x.1) = 5 := by
    rw [closedPoint_finrank_eq_residueDegree f x]
    exact hx
  obtain ⟨y, hy, hey⟩ := cubic_coordinates_of_finite_point_degree_four_or_five p hp hne hd v hv he
  obtain ⟨a, ha⟩ := hypersurface_point_of_coordinates (RingHom.id k) p hp y hy hey
  exact ⟨a, by simpa using ha⟩

end AllCharacteristics
