import AllCharacteristics.SchemeSpecialization
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Specialization with a fixed ambient base

Keeping the proper morphism over its original base lets the regular-local
induction pass through parameter quotients while retaining all base maps.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u

/-- Extend the field or coefficient ring of a scheme-valued point. -/
theorem HasPointOver.map {A k l : Type u} [CommRing A] [CommRing k] [CommRing l]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} {g : A →+* k}
    (h : HasPointOver f g) (j : k →+* l) : HasPointOver f (j.comp g) := by
  obtain ⟨x, hx⟩ := h
  refine ⟨Spec.map (CommRingCat.ofHom j) ≫ x, ?_⟩
  rw [Category.assoc, hx, ← Spec.map_comp]
  rfl

/-- Replace an arbitrary fraction field by the canonical fraction ring, retaining
the prescribed map from the ambient base. -/
theorem HasPointOver.canonicalFractionRing
    {A R K : Type u} [CommRing A] [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} (a : A →+* R)
    (h : HasPointOver f ((algebraMap R K).comp a)) :
    HasPointOver f ((algebraMap R (FractionRing R)).comp a) := by
  let e := FractionRing.algEquiv R K
  have hh := h.map e.symm.toRingHom
  have he : e.symm.toRingHom.comp ((algebraMap R K).comp a) =
      (algebraMap R (FractionRing R)).comp a := by
    ext r
    exact e.symm.commutes (a r)
  rwa [he] at hh

/-- The existence part of the valuative criterion specializes a point even
when the valuation ring maps to a different ambient base ring.  Separatedness
is not needed for this existence statement: universal closedness is enough. -/
theorem specialize_proper_point_along_valuation
    {A V K k : Type u} [CommRing A] [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] [CommRing k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [UniversallyClosed f]
    (a : A →+* V) (red : V →+* k)
    (h : HasPointOver f ((algebraMap V K).comp a)) :
    HasPointOver f (red.comp a) := by
  obtain ⟨x, hx⟩ := h
  have hp : UniversallyClosed f := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at hp
  have hv : ValuativeCriterion.Existence f := hp.1
  let sq : ValuativeCommSq f :=
    { R := V
      K := K
      i₁ := x
      i₂ := Spec.map (CommRingCat.ofHom a)
      commSq := ⟨by rw [← Spec.map_comp]; exact hx⟩ }
  obtain ⟨l⟩ := (hv sq).exists_lift
  refine ⟨Spec.map (CommRingCat.ofHom red) ≫ l.l, ?_⟩
  rw [Category.assoc, l.fac_right, ← Spec.map_comp]
  rfl

end AllCharacteristics
