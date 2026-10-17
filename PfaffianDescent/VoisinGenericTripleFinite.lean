import PfaffianDescent.VoisinFractionGenericBasePoint

/-! Finiteness of the generic fiber of the relative triple intersection. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem finite_pullback_of_factor_through_finite_open
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    [IsFinite (f ∣_ V)] (g : Z ⟶ V.toScheme) :
    IsFinite (pullback.snd f (g ≫ V.ι)) := by
  have hp := (IsPullback.of_hasPullback (f ∣_ V) g).paste_horiz
    (isPullback_morphismRestrict f V).flip
  rw [← hp.isoPullback_inv_snd]
  infer_instance

/-- A finite neighborhood of the generic point remains finite after any
injective specialization to a field. -/
theorem relativeTripleIntersection_isFinite_at_injectiveFieldPoint_of_finiteNeighborhood
    {R F : Type u} [CommRing R] [IsDomain R] [Field F]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (V : (Spec (.of R)).Opens)
    (hη : genericPoint (Spec (.of R)) ∈ V)
    [IsFinite ((relativeTripleIntersectionToBase p q r hp hq hr) ∣_ V)]
    (g : R →+* F) (hg : Function.Injective g) :
    IsFinite (toBase (relativeTripleIntersectionHomogeneousIdeal
      (p.map g) (q.map g) (r.map g)
      (hp.map g) (hq.map g) (hr.map g))) := by
  let f := relativeTripleIntersectionToBase p q r hp hq hr
  let b := Spec.map (CommRingCat.ofHom g)
  have hrange : Set.range b ⊆ Set.range V.ι := by
    rintro y ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint F := Subsingleton.elim x _
    rw [hx, specFieldMap_closedPoint_eq_genericPoint_of_injective g hg]
    rw [V.range_ι]
    exact hη
  let bV := IsOpenImmersion.lift V.ι b hrange
  have hfac : bV ≫ V.ι = b := IsOpenImmersion.lift_fac _ _ _
  haveI : IsFinite (pullback.snd f b) := by
    rw [← hfac]
    exact finite_pullback_of_factor_through_finite_open f V bV
  let J := relativeTripleIntersectionHomogeneousIdeal
    (p.map g) (q.map g) (r.map g)
    (hp.map g) (hq.map g) (hr.map g)
  let e := relativeTripleIntersectionBaseChangeIso g p q r hp hq hr
  have he : e.hom ≫ pullback.snd f b = toBase J := by
    exact projectiveBaseChangeIso_hom_snd _ _ _
      (relativeTripleIntersectionHomogeneousIdeal_map g p q r hp hq hr)
  change IsFinite (toBase J)
  rw [← he]
  infer_instance

theorem relativeTripleIntersection_generic_isFinite_of_finiteNeighborhood
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (V : (Spec (.of R)).Opens)
    (hη : genericPoint (Spec (.of R)) ∈ V)
    [IsFinite ((relativeTripleIntersectionToBase p q r hp hq hr) ∣_ V)] :
    IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap R (FractionRing R)))
      (q.map (algebraMap R (FractionRing R)))
      (r.map (algebraMap R (FractionRing R)))
      (hp.map (algebraMap R (FractionRing R)))
      (hq.map (algebraMap R (FractionRing R)))
      (hr.map (algebraMap R (FractionRing R))))) := by
  let f := relativeTripleIntersectionToBase p q r hp hq hr
  let g := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have hrange : Set.range g ⊆ Set.range V.ι := by
    rintro y ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint (FractionRing R) := Subsingleton.elim x _
    rw [hx, specFractionMap_closedPoint_eq_genericPoint]
    rw [V.range_ι]
    exact hη
  let gV := IsOpenImmersion.lift V.ι g hrange
  have hfac : gV ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  haveI : IsFinite (pullback.snd f g) := by
    rw [← hfac]
    exact finite_pullback_of_factor_through_finite_open f V gV
  let J := relativeTripleIntersectionHomogeneousIdeal
    (p.map (algebraMap R (FractionRing R)))
    (q.map (algebraMap R (FractionRing R)))
    (r.map (algebraMap R (FractionRing R)))
    (hp.map (algebraMap R (FractionRing R)))
    (hq.map (algebraMap R (FractionRing R)))
    (hr.map (algebraMap R (FractionRing R)))
  let e := relativeTripleIntersectionBaseChangeIso
    (algebraMap R (FractionRing R)) p q r hp hq hr
  have he : e.hom ≫ pullback.snd f g = toBase J := by
    exact projectiveBaseChangeIso_hom_snd _ _ _
      (relativeTripleIntersectionHomogeneousIdeal_map
        (algebraMap R (FractionRing R)) p q r hp hq hr)
  haveI : IsFinite (toBase J) := by
    rw [← he]
    infer_instance
  rw [← relativeTripleIntersectionHomogeneousIdeal_eq_triple]
  infer_instance

end PfaffianDescent
