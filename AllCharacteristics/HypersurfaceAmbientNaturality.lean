import AllCharacteristics.HomogeneousProjectiveAmbient
import AllCharacteristics.ScaledHypersurfaceMaps

/-!
# Ambient naturality for projective hypersurfaces

The canonical map of a projective hypersurface to its ambient projective
space commutes with coefficient change, including the unit rescalings used
on projective coefficient-chart overlaps.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R S : Type u} [CommRing R] [CommRing S] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The canonical hypersurface map for ordinary coefficient change is
compatible with the ambient projective-space map. -/
theorem hypersurfaceBaseChangeMap_comp_hypersurfaceToAmbient
    (b : R →+* S) (q : MvPolynomial σ R) {d : ℕ} (hq : q.IsHomogeneous d) :
    projectiveCoefficientMap b (equationIdeal q hq)
      (equationIdeal (q.map b) (hq.map b)) (equationIdeal_map b q hq) ≫
        hypersurfaceToAmbient q hq =
      hypersurfaceToAmbient (q.map b) (hq.map b) ≫ ambientCoefficientMap b :=
  projectiveCoefficientMap_comp_quotientProjMap b (equationIdeal q hq)
    (equationIdeal (q.map b) (hq.map b)) (equationIdeal_map b q hq)

/-- Coefficient change to a unit multiple preserves the ambient projective
map of the resulting hypersurface. -/
theorem scaledHypersurfaceMap_comp_hypersurfaceToAmbient
    (b : R →+* S) (q : MvPolynomial σ R) {d : ℕ} (hq : q.IsHomogeneous d)
    (p : MvPolynomial σ S) (hp : p.IsHomogeneous d) (a : S) (ha : IsUnit a)
    (he : q.map b = C a * p) :
    scaledHypersurfaceMap b q hq p hp a ha he ≫ hypersurfaceToAmbient q hq =
      hypersurfaceToAmbient p hp ≫ ambientCoefficientMap b :=
  projectiveCoefficientMap_comp_quotientProjMap b (equationIdeal q hq)
    (equationIdeal p hp) (equationIdeal_map_of_unit_multiple b q hq p hp a ha he)

end HomogeneousProjective
end AllCharacteristics
