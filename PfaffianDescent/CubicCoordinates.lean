import PfaffianDescent.CanonicalQuinticPoint
import PfaffianDescent.CubicLinear

namespace PfaffianDescent
open scoped BigOperators
namespace Cubic
section
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Collect the ordered tensor coefficients into the twenty ordinary cubic coefficients. -/
def coordinates (c : Cubic R 4) : Vec R 20 :=
  ![c (0, 0, 0),
    c (0, 0, 1) + c (0, 1, 0) + c (1, 0, 0),
    c (0, 0, 2) + c (0, 2, 0) + c (2, 0, 0),
    c (0, 0, 3) + c (0, 3, 0) + c (3, 0, 0),
    c (0, 1, 1) + c (1, 0, 1) + c (1, 1, 0),
    c (0, 1, 2) + c (0, 2, 1) + c (1, 0, 2) + c (1, 2, 0) + c (2, 0, 1) + c (2, 1, 0),
    c (0, 1, 3) + c (0, 3, 1) + c (1, 0, 3) + c (1, 3, 0) + c (3, 0, 1) + c (3, 1, 0),
    c (0, 2, 2) + c (2, 0, 2) + c (2, 2, 0),
    c (0, 2, 3) + c (0, 3, 2) + c (2, 0, 3) + c (2, 3, 0) + c (3, 0, 2) + c (3, 2, 0),
    c (0, 3, 3) + c (3, 0, 3) + c (3, 3, 0),
    c (1, 1, 1),
    c (1, 1, 2) + c (1, 2, 1) + c (2, 1, 1),
    c (1, 1, 3) + c (1, 3, 1) + c (3, 1, 1),
    c (1, 2, 2) + c (2, 1, 2) + c (2, 2, 1),
    c (1, 2, 3) + c (1, 3, 2) + c (2, 1, 3) + c (2, 3, 1) + c (3, 1, 2) + c (3, 2, 1),
    c (1, 3, 3) + c (3, 1, 3) + c (3, 3, 1),
    c (2, 2, 2),
    c (2, 2, 3) + c (2, 3, 2) + c (3, 2, 2),
    c (2, 3, 3) + c (3, 2, 3) + c (3, 3, 2),
    c (3, 3, 3)]

theorem eval_coordinates (c : Cubic R 4) (x : Vec R 4) :
    coordinateCubic c.coordinates x = c.eval x := by
  simp only [coordinateCubic, dotProduct, eval, Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (c (0, 0, 0)) * (x 0 * x 0 * x 0) + ((c (0, 0, 1) + c (0, 1, 0) + c (1, 0, 0)) * (x 0 * x 0 * x 1) + ((c (0, 0, 2) + c (0, 2, 0) + c (2, 0, 0)) * (x 0 * x 0 * x 2) + ((c (0, 0, 3) + c (0, 3, 0) + c (3, 0, 0)) * (x 0 * x 0 * x 3) + ((c (0, 1, 1) + c (1, 0, 1) + c (1, 1, 0)) * (x 0 * x 1 * x 1) + ((c (0, 1, 2) + c (0, 2, 1) + c (1, 0, 2) + c (1, 2, 0) + c (2, 0, 1) + c (2, 1, 0)) * (x 0 * x 1 * x 2) + ((c (0, 1, 3) + c (0, 3, 1) + c (1, 0, 3) + c (1, 3, 0) + c (3, 0, 1) + c (3, 1, 0)) * (x 0 * x 1 * x 3) + ((c (0, 2, 2) + c (2, 0, 2) + c (2, 2, 0)) * (x 0 * x 2 * x 2) + ((c (0, 2, 3) + c (0, 3, 2) + c (2, 0, 3) + c (2, 3, 0) + c (3, 0, 2) + c (3, 2, 0)) * (x 0 * x 2 * x 3) + ((c (0, 3, 3) + c (3, 0, 3) + c (3, 3, 0)) * (x 0 * x 3 * x 3) + ((c (1, 1, 1)) * (x 1 * x 1 * x 1) + ((c (1, 1, 2) + c (1, 2, 1) + c (2, 1, 1)) * (x 1 * x 1 * x 2) + ((c (1, 1, 3) + c (1, 3, 1) + c (3, 1, 1)) * (x 1 * x 1 * x 3) + ((c (1, 2, 2) + c (2, 1, 2) + c (2, 2, 1)) * (x 1 * x 2 * x 2) + ((c (1, 2, 3) + c (1, 3, 2) + c (2, 1, 3) + c (2, 3, 1) + c (3, 1, 2) + c (3, 2, 1)) * (x 1 * x 2 * x 3) + ((c (1, 3, 3) + c (3, 1, 3) + c (3, 3, 1)) * (x 1 * x 3 * x 3) + ((c (2, 2, 2)) * (x 2 * x 2 * x 2) + ((c (2, 2, 3) + c (2, 3, 2) + c (3, 2, 2)) * (x 2 * x 2 * x 3) + ((c (2, 3, 3) + c (3, 2, 3) + c (3, 3, 2)) * (x 2 * x 3 * x 3) + ((c (3, 3, 3)) * (x 3 * x 3 * x 3)))))))))))))))))))) = c (0, 0, 0) * x 0 * x 0 * x 0 + (c (0, 0, 1) * x 0 * x 0 * x 1 + (c (0, 0, 2) * x 0 * x 0 * x 2 + (c (0, 0, 3) * x 0 * x 0 * x 3))) + (c (0, 1, 0) * x 0 * x 1 * x 0 + (c (0, 1, 1) * x 0 * x 1 * x 1 + (c (0, 1, 2) * x 0 * x 1 * x 2 + (c (0, 1, 3) * x 0 * x 1 * x 3))) + (c (0, 2, 0) * x 0 * x 2 * x 0 + (c (0, 2, 1) * x 0 * x 2 * x 1 + (c (0, 2, 2) * x 0 * x 2 * x 2 + (c (0, 2, 3) * x 0 * x 2 * x 3))) + (c (0, 3, 0) * x 0 * x 3 * x 0 + (c (0, 3, 1) * x 0 * x 3 * x 1 + (c (0, 3, 2) * x 0 * x 3 * x 2 + (c (0, 3, 3) * x 0 * x 3 * x 3)))))) + (c (1, 0, 0) * x 1 * x 0 * x 0 + (c (1, 0, 1) * x 1 * x 0 * x 1 + (c (1, 0, 2) * x 1 * x 0 * x 2 + (c (1, 0, 3) * x 1 * x 0 * x 3))) + (c (1, 1, 0) * x 1 * x 1 * x 0 + (c (1, 1, 1) * x 1 * x 1 * x 1 + (c (1, 1, 2) * x 1 * x 1 * x 2 + (c (1, 1, 3) * x 1 * x 1 * x 3))) + (c (1, 2, 0) * x 1 * x 2 * x 0 + (c (1, 2, 1) * x 1 * x 2 * x 1 + (c (1, 2, 2) * x 1 * x 2 * x 2 + (c (1, 2, 3) * x 1 * x 2 * x 3))) + (c (1, 3, 0) * x 1 * x 3 * x 0 + (c (1, 3, 1) * x 1 * x 3 * x 1 + (c (1, 3, 2) * x 1 * x 3 * x 2 + (c (1, 3, 3) * x 1 * x 3 * x 3)))))) + (c (2, 0, 0) * x 2 * x 0 * x 0 + (c (2, 0, 1) * x 2 * x 0 * x 1 + (c (2, 0, 2) * x 2 * x 0 * x 2 + (c (2, 0, 3) * x 2 * x 0 * x 3))) + (c (2, 1, 0) * x 2 * x 1 * x 0 + (c (2, 1, 1) * x 2 * x 1 * x 1 + (c (2, 1, 2) * x 2 * x 1 * x 2 + (c (2, 1, 3) * x 2 * x 1 * x 3))) + (c (2, 2, 0) * x 2 * x 2 * x 0 + (c (2, 2, 1) * x 2 * x 2 * x 1 + (c (2, 2, 2) * x 2 * x 2 * x 2 + (c (2, 2, 3) * x 2 * x 2 * x 3))) + (c (2, 3, 0) * x 2 * x 3 * x 0 + (c (2, 3, 1) * x 2 * x 3 * x 1 + (c (2, 3, 2) * x 2 * x 3 * x 2 + (c (2, 3, 3) * x 2 * x 3 * x 3)))))) + (c (3, 0, 0) * x 3 * x 0 * x 0 + (c (3, 0, 1) * x 3 * x 0 * x 1 + (c (3, 0, 2) * x 3 * x 0 * x 2 + (c (3, 0, 3) * x 3 * x 0 * x 3))) + (c (3, 1, 0) * x 3 * x 1 * x 0 + (c (3, 1, 1) * x 3 * x 1 * x 1 + (c (3, 1, 2) * x 3 * x 1 * x 2 + (c (3, 1, 3) * x 3 * x 1 * x 3))) + (c (3, 2, 0) * x 3 * x 2 * x 0 + (c (3, 2, 1) * x 3 * x 2 * x 1 + (c (3, 2, 2) * x 3 * x 2 * x 2 + (c (3, 2, 3) * x 3 * x 2 * x 3))) + (c (3, 3, 0) * x 3 * x 3 * x 0 + (c (3, 3, 1) * x 3 * x 3 * x 1 + (c (3, 3, 2) * x 3 * x 3 * x 2 + (c (3, 3, 3) * x 3 * x 3 * x 3)))))))))
  ring

theorem coordinates_map (f : R →+* S) (c : Cubic R 4) :
    (c.map f).coordinates = fun i => f (c.coordinates i) := by
  funext i
  fin_cases i
  · change f (c (0, 0, 0)) = f (c (0, 0, 0))
    simp only [map_add]
  · change f (c (0, 0, 1)) + f (c (0, 1, 0)) + f (c (1, 0, 0)) = f (c (0, 0, 1) + c (0, 1, 0) + c (1, 0, 0))
    simp only [map_add]
  · change f (c (0, 0, 2)) + f (c (0, 2, 0)) + f (c (2, 0, 0)) = f (c (0, 0, 2) + c (0, 2, 0) + c (2, 0, 0))
    simp only [map_add]
  · change f (c (0, 0, 3)) + f (c (0, 3, 0)) + f (c (3, 0, 0)) = f (c (0, 0, 3) + c (0, 3, 0) + c (3, 0, 0))
    simp only [map_add]
  · change f (c (0, 1, 1)) + f (c (1, 0, 1)) + f (c (1, 1, 0)) = f (c (0, 1, 1) + c (1, 0, 1) + c (1, 1, 0))
    simp only [map_add]
  · change f (c (0, 1, 2)) + f (c (0, 2, 1)) + f (c (1, 0, 2)) + f (c (1, 2, 0)) + f (c (2, 0, 1)) + f (c (2, 1, 0)) = f (c (0, 1, 2) + c (0, 2, 1) + c (1, 0, 2) + c (1, 2, 0) + c (2, 0, 1) + c (2, 1, 0))
    simp only [map_add]
  · change f (c (0, 1, 3)) + f (c (0, 3, 1)) + f (c (1, 0, 3)) + f (c (1, 3, 0)) + f (c (3, 0, 1)) + f (c (3, 1, 0)) = f (c (0, 1, 3) + c (0, 3, 1) + c (1, 0, 3) + c (1, 3, 0) + c (3, 0, 1) + c (3, 1, 0))
    simp only [map_add]
  · change f (c (0, 2, 2)) + f (c (2, 0, 2)) + f (c (2, 2, 0)) = f (c (0, 2, 2) + c (2, 0, 2) + c (2, 2, 0))
    simp only [map_add]
  · change f (c (0, 2, 3)) + f (c (0, 3, 2)) + f (c (2, 0, 3)) + f (c (2, 3, 0)) + f (c (3, 0, 2)) + f (c (3, 2, 0)) = f (c (0, 2, 3) + c (0, 3, 2) + c (2, 0, 3) + c (2, 3, 0) + c (3, 0, 2) + c (3, 2, 0))
    simp only [map_add]
  · change f (c (0, 3, 3)) + f (c (3, 0, 3)) + f (c (3, 3, 0)) = f (c (0, 3, 3) + c (3, 0, 3) + c (3, 3, 0))
    simp only [map_add]
  · change f (c (1, 1, 1)) = f (c (1, 1, 1))
    simp only [map_add]
  · change f (c (1, 1, 2)) + f (c (1, 2, 1)) + f (c (2, 1, 1)) = f (c (1, 1, 2) + c (1, 2, 1) + c (2, 1, 1))
    simp only [map_add]
  · change f (c (1, 1, 3)) + f (c (1, 3, 1)) + f (c (3, 1, 1)) = f (c (1, 1, 3) + c (1, 3, 1) + c (3, 1, 1))
    simp only [map_add]
  · change f (c (1, 2, 2)) + f (c (2, 1, 2)) + f (c (2, 2, 1)) = f (c (1, 2, 2) + c (2, 1, 2) + c (2, 2, 1))
    simp only [map_add]
  · change f (c (1, 2, 3)) + f (c (1, 3, 2)) + f (c (2, 1, 3)) + f (c (2, 3, 1)) + f (c (3, 1, 2)) + f (c (3, 2, 1)) = f (c (1, 2, 3) + c (1, 3, 2) + c (2, 1, 3) + c (2, 3, 1) + c (3, 1, 2) + c (3, 2, 1))
    simp only [map_add]
  · change f (c (1, 3, 3)) + f (c (3, 1, 3)) + f (c (3, 3, 1)) = f (c (1, 3, 3) + c (3, 1, 3) + c (3, 3, 1))
    simp only [map_add]
  · change f (c (2, 2, 2)) = f (c (2, 2, 2))
    simp only [map_add]
  · change f (c (2, 2, 3)) + f (c (2, 3, 2)) + f (c (3, 2, 2)) = f (c (2, 2, 3) + c (2, 3, 2) + c (3, 2, 2))
    simp only [map_add]
  · change f (c (2, 3, 3)) + f (c (3, 2, 3)) + f (c (3, 3, 2)) = f (c (2, 3, 3) + c (3, 2, 3) + c (3, 3, 2))
    simp only [map_add]
  · change f (c (3, 3, 3)) = f (c (3, 3, 3))
    simp only [map_add]

end
end Cubic

section
variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem canonical_quintic_tensor_descent (α : L) (b : Module.Basis (Fin 5) K L)
    (hb : ∀ i, b i = α^(i : ℕ)) (c : Cubic K 4)
    (hF : (c.map (algebraMap K L)).eval (rationalCubicCoordinates α) = 0) :
    ∃ x : Vec K 4, x ≠ 0 ∧ c.eval x = 0 := by
  have h := (Cubic.eval_coordinates (c.map (algebraMap K L)) (rationalCubicCoordinates α)).trans hF
  rw [Cubic.coordinates_map] at h
  obtain ⟨x, hx, he⟩ := canonical_quintic_point_descent α b hb c.coordinates h
  exact ⟨x, hx, (Cubic.eval_coordinates c x).symm.trans he⟩

end
end PfaffianDescent
