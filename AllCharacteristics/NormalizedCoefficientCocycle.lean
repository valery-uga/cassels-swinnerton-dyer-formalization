import AllCharacteristics.NormalizedCoefficientTransitions

/-!
# Composition of normalized coefficient transitions

Normalization at the same coefficient is the identity. Normalizing successively
at two coefficients agrees with normalizing directly, with the composite unit
constructed from the two coefficient ratios. These are ring-map identities
over every commutative target ring, including triple-overlap rings.
-/

open MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable {R A : Type u} [CommRing R] [CommRing A] {σ : Type} {d : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Normalizing a chart at its already distinguished coefficient changes nothing. -/
theorem normalizedChartTransition_self (j : Monomials σ d)
    (g : ParameterChartRing R σ d j →+* A) :
    normalizedChartTransition j j g 1 (by rw [chartCoordinate_self, map_one]; rfl) = g := by
  apply projectiveChartMap_ext j
  · apply RingHom.ext
    intro r
    exact normalizedChartTransition_baseMap j j g 1
      (by rw [chartCoordinate_self, map_one]; rfl) r
  · intro m
    simpa only [inv_one, Units.val_one, one_mul] using
      normalizedChartTransition_coordinate j j g 1
        (by rw [chartCoordinate_self, map_one]; rfl) m

variable (i j l : Monomials σ d) (g : ParameterChartRing R σ d l →+* A)
variable (u : Aˣ) (hu : (u : A) = g (chartCoordinate (ParameterIdeal R σ d) l j))
variable (v : Aˣ)
variable (hv : (v : A) =
  normalizedChartTransition j l g u hu (chartCoordinate (ParameterIdeal R σ d) j i))

include hu hv in
/-- The product of the two successive coefficient ratios is the direct ratio. -/
theorem normalizedChartTransition_compositeUnit :
    ((v * u : Aˣ) : A) = g (chartCoordinate (ParameterIdeal R σ d) l i) := by
  have h := hv.trans (normalizedChartTransition_coordinate j l g u hu i)
  rw [Units.val_mul, h]
  calc
    (↑(u⁻¹) * g (chartCoordinate (ParameterIdeal R σ d) l i)) * ↑u =
        (↑(u⁻¹) * ↑u) * g (chartCoordinate (ParameterIdeal R σ d) l i) := by ring
    _ = g (chartCoordinate (ParameterIdeal R σ d) l i) := by simp

/-- The normalized coefficient transition maps satisfy composition on triple overlaps. -/
theorem normalizedChartTransition_comp :
    normalizedChartTransition i j (normalizedChartTransition j l g u hu) v hv =
      normalizedChartTransition i l g (v * u)
        (normalizedChartTransition_compositeUnit i j l g u hu v hv) := by
  apply projectiveChartMap_ext i
  · apply RingHom.ext
    intro r
    change normalizedChartTransition i j (normalizedChartTransition j l g u hu) v hv
      (chartBaseMap (ParameterIdeal R σ d) i r) =
      normalizedChartTransition i l g (v * u)
        (normalizedChartTransition_compositeUnit i j l g u hu v hv)
        (chartBaseMap (ParameterIdeal R σ d) i r)
    simp only [normalizedChartTransition_baseMap]
  · intro m
    rw [normalizedChartTransition_coordinate, normalizedChartTransition_coordinate,
      normalizedChartTransition_coordinate]
    change (↑(v⁻¹) : A) * ((↑(u⁻¹) : A) * g (chartCoordinate (ParameterIdeal R σ d) l m)) =
      ((↑(u⁻¹) : A) * (↑(v⁻¹) : A)) * g (chartCoordinate (ParameterIdeal R σ d) l m)
    ring

end UniversalHomogeneous
end AllCharacteristics
