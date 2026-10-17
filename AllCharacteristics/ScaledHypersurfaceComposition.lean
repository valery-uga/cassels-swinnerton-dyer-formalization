import AllCharacteristics.ScaledHypersurfaceMaps

/-!
# Composition of coefficient changes up to units

Successive coefficient changes multiply the transported equation units. The
canonical actual hypersurface maps obey identity and composition, so their
compatibility does not depend on a choice of rescaling formula.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Under successive coefficient changes, the equation multipliers combine
by transporting the first multiplier and multiplying by the second. -/
theorem mapped_unit_multiple_comp (f : R →+* S) (g : S →+* T)
    (q : MvPolynomial σ R) (p : MvPolynomial σ S) (r : MvPolynomial σ T) (a : S) (b : T)
    (he : q.map f = C a * p) (he' : p.map g = C b * r) :
    q.map (g.comp f) = C (g a * b) * r := by
  rw [← MvPolynomial.map_map, he, map_mul, MvPolynomial.map_C, he', map_mul, mul_assoc]

/-- Identity coefficient change with multiplier one gives the identity hypersurface map. -/
theorem scaledHypersurfaceMap_id (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) :
    scaledHypersurfaceMap (RingHom.id R) p hp p hp 1 isUnit_one
      (by rw [MvPolynomial.map_id, map_one, one_mul]) = 𝟙 (hypersurface p hp) :=
  projectiveCoefficientMap_id (equationIdeal p hp)

/-- Canonical scaled hypersurface maps compose with the transported product multiplier. -/
theorem scaledHypersurfaceMap_comp (f : R →+* S) (g : S →+* T)
    (q : MvPolynomial σ R) {d : ℕ} (hq : q.IsHomogeneous d)
    (p : MvPolynomial σ S) (hp : p.IsHomogeneous d)
    (r : MvPolynomial σ T) (hr : r.IsHomogeneous d)
    (a : S) (ha : IsUnit a) (b : T) (hb : IsUnit b)
    (he : q.map f = C a * p) (he' : p.map g = C b * r) :
    scaledHypersurfaceMap g p hp r hr b hb he' ≫
      scaledHypersurfaceMap f q hq p hp a ha he =
    scaledHypersurfaceMap (g.comp f) q hq r hr (g a * b) ((ha.map g).mul hb)
      (mapped_unit_multiple_comp f g q p r a b he he') :=
  projectiveCoefficientMap_comp f g (equationIdeal q hq) (equationIdeal p hp)
    (equationIdeal r hr) (equationIdeal_map_of_unit_multiple f q hq p hp a ha he)
    (equationIdeal_map_of_unit_multiple g p hp r hr b hb he')

end HomogeneousProjective
end AllCharacteristics
