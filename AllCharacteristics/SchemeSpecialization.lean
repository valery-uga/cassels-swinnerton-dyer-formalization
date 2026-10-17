import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Specialization of points of proper schemes

This proves the valuation-ring case of the regular-local specialization lemma
in `all_characteristics_specialization.tex` for actual Mathlib schemes and
Mathlib's properness predicate. It assumes neither an extension of the point
nor an abstract specialization rule.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AllCharacteristics

universe u

/-- A point of an `R`-scheme with values in an `R`-algebra. The commutativity
condition retains the given base structure. -/
def HasPointOver {R k : Type u} [CommRing R] [CommRing k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (g : R →+* k) : Prop :=
  ∃ x : Spec (.of k) ⟶ X, x ≫ f = Spec.map (CommRingCat.ofHom g)

section Valuation
variable {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]

/-- Properness extends a generic-fiber point over a valuation ring. -/
theorem extend_point_over_valuation
    (x : Spec (.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ s : Spec (.of R) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = x ∧ s ≫ f = 𝟙 _ := by
  have hp : IsProper f := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hp
  have hv : ValuativeCriterion.Existence f := hp.1.1.1.existence
  let sq : ValuativeCommSq f :=
    { R := R
      K := K
      i₁ := x
      i₂ := 𝟙 _
      commSq := ⟨by simpa only [Category.comp_id] using hx⟩ }
  obtain ⟨l⟩ := (hv sq).exists_lift
  exact ⟨l.l, l.fac_left, l.fac_right⟩

/-- A point of the generic fiber of a proper scheme specializes along every
map from the valuation ring. In particular it specializes to the residue field. -/
theorem specialize_proper_point {k : Type u} [CommRing k]
    (red : R →+* k) (h : HasPointOver f (algebraMap R K)) : HasPointOver f red := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨s, _, hs⟩ := extend_point_over_valuation f x hx
  refine ⟨Spec.map (CommRingCat.ofHom red) ≫ s, ?_⟩
  rw [Category.assoc, hs, Category.comp_id]

/-- The residue-field form of the proper specialization theorem. -/
theorem specialize_proper_point_to_residue
    (h : HasPointOver f (algebraMap R K)) :
    HasPointOver f (IsLocalRing.residue R) :=
  specialize_proper_point f (IsLocalRing.residue R) h

/-- The specialized point is an actual section of the special fiber, described
as a scheme-theoretic pullback. -/
theorem special_fiber_has_section {k : Type u} [CommRing k]
    (red : R →+* k) (h : HasPointOver f (algebraMap R K)) :
    ∃ q : Spec (.of k) ⟶ pullback f (Spec.map (CommRingCat.ofHom red)),
      q ≫ pullback.snd f (Spec.map (CommRingCat.ofHom red)) = 𝟙 _ := by
  obtain ⟨x, hx⟩ := specialize_proper_point f red h
  refine ⟨pullback.lift x (𝟙 _) ?_, ?_⟩
  · simpa only [Category.id_comp] using hx
  · exact pullback.lift_snd _ _ _

end Valuation
end AllCharacteristics
