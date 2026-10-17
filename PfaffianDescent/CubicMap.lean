import PfaffianDescent.CubicLinear

namespace PfaffianDescent.Cubic
open scoped BigOperators
section
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {n : ℕ}

theorem map_map (f : R →+* S) (g : S →+* T) (c : Cubic R n) :
    (c.map f).map g = c.map (g.comp f) := rfl

theorem map_sub (f : R →+* S) (c d : Cubic R n) :
    (c - d).map f = c.map f - d.map f := by
  funext i
  exact _root_.map_sub f _ _

theorem map_coefficient_smul (f : R →+* S) (s : R) (c : Cubic R n) :
    (s • c).map f = f s • c.map f := by
  funext i
  exact _root_.map_mul f _ _

theorem map_sum {ι : Type*} (f : R →+* S) (s : Finset ι) (c : ι → Cubic R n) :
    (∑ i ∈ s, c i).map f = ∑ i ∈ s, (c i).map f := by
  funext j
  simp only [map, Finset.sum_apply, _root_.map_sum]

end
end PfaffianDescent.Cubic
