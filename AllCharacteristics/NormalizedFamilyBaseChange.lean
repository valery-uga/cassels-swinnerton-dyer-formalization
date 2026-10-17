import AllCharacteristics.HypersurfaceFiberNaturality
import AllCharacteristics.NormalizedFamilyCocycle

/-!
# Normalized universal families under further coefficient change

Normalized coefficient transitions commute with coefficient change, including
their distinguished units. The actual normalized family isomorphisms commute
with the canonical Cartesian restriction maps, with source transport explicit.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] {σ : Type} {d : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (j l : Monomials σ d) (g : ParameterChartRing R σ d l →+* A)
variable (u : Aˣ) (hu : (u : A) = g (chartCoordinate (ParameterIdeal R σ d) l j))
variable (b : A →+* B)

include hu in
/-- The transported distinguished unit is the new value of the same coefficient. -/
theorem normalizedChartTransition_mapUnit :
    (Units.map b.toMonoidHom u : B) =
      (b.comp g) (chartCoordinate (ParameterIdeal R σ d) l j) := by
  change b (u : A) = b (g (chartCoordinate (ParameterIdeal R σ d) l j))
  rw [hu]

/-- Normalizing coefficients commutes with arbitrary further coefficient change. -/
theorem normalizedChartTransition_baseChange :
    b.comp (normalizedChartTransition j l g u hu) =
      normalizedChartTransition j l (b.comp g) (Units.map b.toMonoidHom u)
        (normalizedChartTransition_mapUnit j l g u hu b) := by
  apply projectiveChartMap_ext j
  · apply RingHom.ext
    intro r
    change b (normalizedChartTransition j l g u hu (chartBaseMap (ParameterIdeal R σ d) j r)) =
      normalizedChartTransition j l (b.comp g) (Units.map b.toMonoidHom u)
        (normalizedChartTransition_mapUnit j l g u hu b) (chartBaseMap (ParameterIdeal R σ d) j r)
    rw [normalizedChartTransition_baseMap, normalizedChartTransition_baseMap]
    rfl
  · intro m
    rw [RingHom.comp_apply, normalizedChartTransition_coordinate,
      normalizedChartTransition_coordinate, map_mul]
    rfl

variable [Finite σ]

/-- The actual normalized-family isomorphism is natural for further coefficient
change, through the canonical restriction maps and the exact source transport. -/
theorem normalizedChartFamilyIso_baseChange :
    (eqToIso (congrArg (fun f : ParameterChartRing R σ d j →+* B ↦
      pullback (normalizedFamilyToBase R σ d j) (Spec.map (CommRingCat.ofHom f)))
        (normalizedChartTransition_baseChange j l g u hu b))).hom ≫
      (normalizedChartFamilyIso j l (b.comp g) (Units.map b.toMonoidHom u)
        (normalizedChartTransition_mapUnit j l g u hu b)).hom ≫
      projectiveFiberRestriction g b
        (equationIdeal (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)) =
    projectiveFiberRestriction (normalizedChartTransition j l g u hu) b
      (equationIdeal (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)) ≫
      (normalizedChartFamilyIso j l g u hu).hom := by
  simp only [normalizedChartFamilyIso_eq_fiberComparison]
  let f := normalizedChartTransition j l g u hu
  let f' := normalizedChartTransition j l (b.comp g) (Units.map b.toMonoidHom u)
    (normalizedChartTransition_mapUnit j l g u hu b)
  let h := equationIdeal_eq_of_unit_multiple _ _
    ((normalizedForm_isHomogeneous R σ d j).map f)
    ((normalizedForm_isHomogeneous R σ d l).map g) (↑(u⁻¹) : A) (u⁻¹).isUnit
    (map_normalizedForm_transition j l g u hu)
  let h' := equationIdeal_eq_of_unit_multiple _ _
    ((normalizedForm_isHomogeneous R σ d j).map f')
    ((normalizedForm_isHomogeneous R σ d l).map (b.comp g))
    (↑((Units.map b.toMonoidHom u)⁻¹) : B) ((Units.map b.toMonoidHom u)⁻¹).isUnit
    (map_normalizedForm_transition j l (b.comp g) (Units.map b.toMonoidHom u)
      (normalizedChartTransition_mapUnit j l g u hu b))
  have he := hypersurfaceFiberComparison_congr_left (b.comp f) f'
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    (b.comp g) (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)
    (equationIdeal_specialization_eq_map f (normalizedForm R σ d j)
      (normalizedForm_isHomogeneous R σ d j) g (normalizedForm R σ d l)
      (normalizedForm_isHomogeneous R σ d l) h b) h'
    (normalizedChartTransition_baseChange j l g u hu b)
  have hn := hypersurfaceFiberComparison_naturality f
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    g (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l) h b
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a ↦ a ≫ projectiveFiberRestriction g b
      (equationIdeal (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)))
        (congrArg Iso.hom he.symm)).trans hn)

end UniversalHomogeneous
end AllCharacteristics
