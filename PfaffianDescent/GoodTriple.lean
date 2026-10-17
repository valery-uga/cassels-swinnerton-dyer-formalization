import PfaffianDescent.Constraints

namespace PfaffianDescent
section
variable {R : Type*} [CommRing R]

private theorem goodTriple_alternating_0 : IsAlternating (goodTriple 0 : Mat R 6) := by
  constructor
  · intro i
    fin_cases i <;> rfl
  · intro i j
    fin_cases i <;> fin_cases j
    · change (0 : R) = -(0 : R)
      ring
    · change (-1 : R) = -(1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (1 : R) = -(-1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (-1 : R) = -(1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (1 : R) = -(-1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (-1 : R) = -(1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (1 : R) = -(-1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring

private theorem goodTriple_alternating_1 : IsAlternating (goodTriple 1 : Mat R 6) := by
  constructor
  · intro i
    fin_cases i <;> rfl
  · intro i j
    fin_cases i <;> fin_cases j
    · change (0 : R) = -(0 : R)
      ring
    · change (-1 : R) = -(1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (1 : R) = -(-1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (-2 : R) = -(2 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (2 : R) = -(-2 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (-3 : R) = -(3 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (3 : R) = -(-3 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring

private theorem goodTriple_alternating_2 : IsAlternating (goodTriple 2 : Mat R 6) := by
  constructor
  · intro i
    fin_cases i <;> rfl
  · intro i j
    fin_cases i <;> fin_cases j
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (-1 : R) = -(1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (-1 : R) = -(1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (-1 : R) = -(1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (-1 : R) = -(1 : R)
      ring
    · change (1 : R) = -(-1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (-1 : R) = -(1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (1 : R) = -(-1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (-2 : R) = -(2 : R)
      ring
    · change (1 : R) = -(-1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (1 : R) = -(-1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (1 : R) = -(-1 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (2 : R) = -(-2 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring
    · change (0 : R) = -(0 : R)
      ring

theorem goodTriple_alternating : ∀ i : Fin 3, IsAlternating (goodTriple i : Mat R 6) := by
  intro i
  fin_cases i
  · exact goodTriple_alternating_0
  · exact goodTriple_alternating_1
  · exact goodTriple_alternating_2

variable {S : Type*} [CommRing S]

private theorem goodTriple_map_0 (φ : R →+* S) :
    (goodTriple 0 : Mat R 6).map φ = goodTriple 0 := by
  funext i j
  fin_cases i <;> fin_cases j
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (1 : R) = (1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (-1 : R) = (-1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (1 : R) = (1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (-1 : R) = (-1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (1 : R) = (1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (-1 : R) = (-1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]

private theorem goodTriple_map_1 (φ : R →+* S) :
    (goodTriple 1 : Mat R 6).map φ = goodTriple 1 := by
  funext i j
  fin_cases i <;> fin_cases j
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (1 : R) = (1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (-1 : R) = (-1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (2 : R) = (2 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (-2 : R) = (-2 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (3 : R) = (3 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (-3 : R) = (-3 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]

private theorem goodTriple_map_2 (φ : R →+* S) :
    (goodTriple 2 : Mat R 6).map φ = goodTriple 2 := by
  funext i j
  fin_cases i <;> fin_cases j
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (1 : R) = (1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (1 : R) = (1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (1 : R) = (1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (1 : R) = (1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (-1 : R) = (-1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (1 : R) = (1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (-1 : R) = (-1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (2 : R) = (2 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (-1 : R) = (-1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (-1 : R) = (-1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (-1 : R) = (-1 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (-2 : R) = (-2 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]
  · change φ (0 : R) = (0 : S)
    simp only [map_neg, map_ofNat, map_one, map_zero]

theorem goodTriple_map (φ : R →+* S) :
    (fun i => (goodTriple i : Mat R 6).map φ) = goodTriple := by
  funext i
  fin_cases i
  · exact goodTriple_map_0 φ
  · exact goodTriple_map_1 φ
  · exact goodTriple_map_2 φ

end
end PfaffianDescent
