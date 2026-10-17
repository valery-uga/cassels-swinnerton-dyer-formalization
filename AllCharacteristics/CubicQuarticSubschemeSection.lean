import AllCharacteristics.CubicFiberDescent
import AllCharacteristics.FiniteSubschemeFunctor
import AllCharacteristics.FiniteFlatCycle
import AllCharacteristics.BaseChangedFamilyMap
import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-! # Rational sections supplied by an actual quartic subscheme

An actual rank-four finite subscheme of a cubic family supplies field-valued lifts in characteristic zero by the proved Pfaffian descent. Over an integral base with characteristic-zero function field it supplies an actual Mathlib rational section. Integrality is an explicit hypothesis of this general lemma, not an assertion about a particular universal base.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
open HomogeneousProjective
universe u

/- A rank-four finite-flat subscheme of a cubic fiber gives the effective
degree-four cycle used by the descent theorem. -/
theorem exists_effective_cycle_of_quarticSubscheme
    {R k : Type u} [CommRing R] [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3) (b : R →+* k)
    (D : FiniteSubschemeDatum
      (pullback.snd (hypersurfaceToBase p hp)
        (Spec.map (CommRingCat.ofHom b))) 4) :
    ∃ z : EffectiveZeroCycle
        (pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))),
      EffectiveZeroCycle.degree
        (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) z = 4 := by
  let f := pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))
  have hfinite : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_of_finite_closed_subscheme
    D.val.subschemeι f
  have hrank : finiteSchemeRank (D.val.subschemeι ≫ f) = 4 := by
    rw [finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint k)
  exact ⟨z, hz.trans hrank⟩

theorem hypersurface_fiber_section_of_quarticSubscheme
    {R k : Type u} [CommRing R] [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3) (b : R →+* k)
    (D : FiniteSubschemeDatum (pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))) 4) :
    ∃ s : Spec (.of k) ⟶ pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)),
      s ≫ pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)) = 𝟙 _ := by
  let f := pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b))
  obtain ⟨z, hz⟩ := exists_effective_cycle_of_quarticSubscheme p hp b D
  apply hypersurface_fiber_section_of_effective_degree_four_or_five p hp b z
  exact Or.inl hz

theorem cubicFamily_fieldLift_of_quarticSubscheme
    {R k : Type u} [CommRing R] [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    {B : Scheme.{u}} (b : B ⟶ Spec (.of R))
    (D : FiniteSubschemeDatum (pullback.snd (hypersurfaceToBase p hp) b) 4)
    (a : Spec (.of k) ⟶ B) :
    ∃ s : Spec (.of k) ⟶ pullback (hypersurfaceToBase p hp) b,
      s ≫ pullback.snd (hypersurfaceToBase p hp) b = a := by
  let c := Spec.preimage (a ≫ b)
  have hc : a ≫ b = Spec.map c := (Spec.map_preimage _).symm
  let m := baseChangedFamilyMap (hypersurfaceToBase p hp) (Spec.map c) b a hc
  have hM := isPullback_baseChangedFamilyMap (hypersurfaceToBase p hp) (Spec.map c) b a hc
  let D' := FiniteSubschemeDatum.baseChange m a hM D
  obtain ⟨s, hs⟩ := hypersurface_fiber_section_of_quarticSubscheme (R := R) (k := k) p hp c.hom D'
  let t : Spec (.of k) ⟶ pullback (hypersurfaceToBase p hp) (Spec.map c) := s
  have ht : t ≫ pullback.snd (hypersurfaceToBase p hp) (Spec.map c) = 𝟙 _ := hs
  refine ⟨t ≫ m, ?_⟩
  rw [Category.assoc, baseChangedFamilyMap_snd, ← Category.assoc, ht, Category.id_comp]

theorem exists_rational_section_cubicFamily_of_quarticSubscheme
    {R : Type u} [CommRing R] (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    {B : Scheme.{u}} [IsIntegral B] [CharZero B.functionField]
    (b : B ⟶ Spec (.of R))
    (D : FiniteSubschemeDatum (pullback.snd (hypersurfaceToBase p hp) b) 4) :
    ∃ s : B.RationalMap (pullback (hypersurfaceToBase p hp) b),
      s.compHom (pullback.snd (hypersurfaceToBase p hp) b) = Scheme.Hom.toRationalMap (𝟙 B) := by
  obtain ⟨q, hq⟩ := cubicFamily_fieldLift_of_quarticSubscheme p hp b D
    (B.fromSpecStalk (genericPoint B))
  let s := (Scheme.RationalMap.equivFunctionField (𝟙 B)
    (pullback.snd (hypersurfaceToBase p hp) b)) ⟨q, by simpa only [Category.comp_id] using hq⟩
  exact ⟨s.val, s.property⟩

end AllCharacteristics
