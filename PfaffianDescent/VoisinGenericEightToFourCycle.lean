import PfaffianDescent.VoisinGenericTripleEightSubscheme
import PfaffianDescent.VoisinGenericTripleLength
import PfaffianDescent.FiniteClosedSubschemeCycleComplement

/-! The selected eight rational points leave an effective degree-four cycle. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem genericTripleIntersection_exists_degreeFourComplementCycle
    {R : Type u} [CommRing R] [IsDomain R]
    [Infinite (FractionRing R)]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hEight : HasEightDistinctGenericTriplePoints
      p q r hp hq hr ell hell x)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap R (FractionRing R)))
      (q.map (algebraMap R (FractionRing R)))
      (r.map (algebraMap R (FractionRing R)))
      (hp.map (algebraMap R (FractionRing R)))
      (hq.map (algebraMap R (FractionRing R)))
      (hr.map (algebraMap R (FractionRing R)))))] :
    let f := algebraMap R (FractionRing R)
    let I := tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f)
    ∃ z : EffectiveZeroCycle (scheme I),
      EffectiveZeroCycle.degree (toBase I) z = 4 := by
  dsimp only
  obtain ⟨hzero, hnorm, hinj⟩ := hEight
  let f := algebraMap R (FractionRing R)
  let I := tripleCompleteIntersectionHomogeneousIdeal
    (p.map f) (q.map f) (r.map f)
    (hp.map f) (hq.map f) (hr.map f)
  let b := toBase I
  let i := genericTripleIntersectionEightEmbedding
    p q r hp hq hr ell hell x hzero hnorm
  letI : IsClosedImmersion i :=
    genericTripleIntersectionEightEmbedding_isClosedImmersion
      p q r hp hq hr ell hell x hzero hnorm hinj
  letI : IsFinite (i ≫ b) := by
    rw [genericTripleIntersectionEightEmbedding_toBase]
    exact isFinite_constantCoverToBase_spec
      (ULift.{u} (Fin 8)) (FractionRing R)
  refine ⟨finiteClosedSubschemeComplementCycle i b, ?_⟩
  rw [finiteClosedSubschemeComplementCycle_degree]
  have h12 := relativeTripleIntersection_generic_rank_twelve
    p q r hp hq hr ell hell x ⟨hzero, hnorm, hinj⟩
  have h8 := genericTripleIntersectionEightEmbedding_rank_eight
    p q r hp hq hr ell hell x hzero hnorm
  rw [h12, h8]

/-- For fixed cubic and quadratic equations, the residual cycle is unchanged
when the eight selected points are relabeled. -/
theorem genericTripleIntersection_complementCycle_relabel
    {R : Type u} [CommRing R] [IsDomain R]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hzero : ∀ k, p.eval (x k) = 0 ∧
      q.eval (x k) = 0 ∧ r.eval (x k) = 0)
    (hnorm : ∀ k, ell.eval (x k) = 1)
    (hinj : Function.Injective (genericTripleIntersectionSelectedPoints
      p q r hp hq hr ell hell x hzero hnorm))
    (σ : Equiv.Perm (Fin 8))
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap R (FractionRing R)))
      (q.map (algebraMap R (FractionRing R)))
      (r.map (algebraMap R (FractionRing R)))
      (hp.map (algebraMap R (FractionRing R)))
      (hq.map (algebraMap R (FractionRing R)))
      (hr.map (algebraMap R (FractionRing R)))))] :
    let xr := fun k => x (σ k)
    let hzr := fun k => hzero (σ k)
    let hnr := fun k => hnorm (σ k)
    let b := toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (algebraMap R (FractionRing R)))
      (q.map (algebraMap R (FractionRing R)))
      (r.map (algebraMap R (FractionRing R)))
      (hp.map (algebraMap R (FractionRing R)))
      (hq.map (algebraMap R (FractionRing R)))
      (hr.map (algebraMap R (FractionRing R))))
    let ir := genericTripleIntersectionEightEmbedding
      p q r hp hq hr ell hell xr hzr hnr
    let i := genericTripleIntersectionEightEmbedding
      p q r hp hq hr ell hell x hzero hnorm
    ∃ (hir : IsClosedImmersion ir) (hi : IsClosedImmersion i),
    letI : IsClosedImmersion ir := hir
    letI : IsClosedImmersion i := hi
    finiteClosedSubschemeComplementCycle
      ir b =
      finiteClosedSubschemeComplementCycle
        i b := by
  dsimp only
  let xr := fun k => x (σ k)
  let hzr := fun k => hzero (σ k)
  let hnr := fun k => hnorm (σ k)
  let b := toBase (tripleCompleteIntersectionHomogeneousIdeal
    (p.map (algebraMap R (FractionRing R)))
    (q.map (algebraMap R (FractionRing R)))
    (r.map (algebraMap R (FractionRing R)))
    (hp.map (algebraMap R (FractionRing R)))
    (hq.map (algebraMap R (FractionRing R)))
    (hr.map (algebraMap R (FractionRing R))))
  let i := genericTripleIntersectionEightEmbedding
    p q r hp hq hr ell hell x hzero hnorm
  let ir := genericTripleIntersectionEightEmbedding
    p q r hp hq hr ell hell xr hzr hnr
  have hinjr : Function.Injective (genericTripleIntersectionSelectedPoints
      p q r hp hq hr ell hell xr hzr hnr) := by
    obtain ⟨_, _, h⟩ := hasEightDistinctGenericTriplePoints_relabel
      p q r hp hq hr ell hell x σ ⟨hzero, hnorm, hinj⟩
    exact h
  letI : IsClosedImmersion i :=
    genericTripleIntersectionEightEmbedding_isClosedImmersion
      p q r hp hq hr ell hell x hzero hnorm hinj
  letI : IsClosedImmersion ir :=
    genericTripleIntersectionEightEmbedding_isClosedImmersion
      p q r hp hq hr ell hell xr hzr hnr hinjr
  obtain ⟨e, he⟩ := genericTripleIntersectionEightEmbedding_relabel
    p q r hp hq hr ell hell x hzero hnorm σ
  exact ⟨inferInstance, inferInstance,
    finiteClosedSubschemeComplementCycle_eq_of_iso ir i b e he⟩

theorem genericTripleIntersection_exists_degreeFourComplementCycle_of_finiteNeighborhood
    {R : Type u} [CommRing R] [IsDomain R]
    [Infinite (FractionRing R)]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hEight : HasEightDistinctGenericTriplePoints
      p q r hp hq hr ell hell x)
    (V : (Spec (.of R)).Opens)
    (hη : genericPoint (Spec (.of R)) ∈ V)
    [IsFinite ((relativeTripleIntersectionToBase p q r hp hq hr) ∣_ V)] :
    let f := algebraMap R (FractionRing R)
    let I := tripleCompleteIntersectionHomogeneousIdeal
      (p.map f) (q.map f) (r.map f)
      (hp.map f) (hq.map f) (hr.map f)
    ∃ z : EffectiveZeroCycle (scheme I),
      EffectiveZeroCycle.degree (toBase I) z = 4 := by
  dsimp only
  letI := relativeTripleIntersection_generic_isFinite_of_finiteNeighborhood
    p q r hp hq hr V hη
  exact genericTripleIntersection_exists_degreeFourComplementCycle
    p q r hp hq hr ell hell x hEight

/-- The complement cycle lies on the generic cubic surface, with degree four
over its coefficient field. -/
theorem genericCubic_exists_degreeFourCycle_of_selected_finiteNeighborhood
    {R : Type u} [CommRing R] [IsDomain R]
    [Infinite (FractionRing R)]
    (p q r : MvPolynomial (Fin 4) R)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (ell : MvPolynomial (Fin 4) R)
    (hell : ell.IsHomogeneous 1)
    (x : Fin 8 → Fin 4 → R)
    (hEight : HasEightDistinctGenericTriplePoints
      p q r hp hq hr ell hell x)
    (V : (Spec (.of R)).Opens)
    (hη : genericPoint (Spec (.of R)) ∈ V)
    [IsFinite ((relativeTripleIntersectionToBase p q r hp hq hr) ∣_ V)] :
    let f := algebraMap R (FractionRing R)
    ∃ z : EffectiveZeroCycle (hypersurface (p.map f) (hp.map f)),
      EffectiveZeroCycle.degree
        (hypersurfaceToBase (p.map f) (hp.map f)) z = 4 := by
  dsimp only
  obtain ⟨z, hz⟩ :=
    genericTripleIntersection_exists_degreeFourComplementCycle_of_finiteNeighborhood
      p q r hp hq hr ell hell x hEight V hη
  exact exists_effectiveZeroCycle_on_hypersurface_of_triple
    (p.map (algebraMap R (FractionRing R)))
    (q.map (algebraMap R (FractionRing R)))
    (r.map (algebraMap R (FractionRing R)))
    (hp.map (algebraMap R (FractionRing R)))
    (hq.map (algebraMap R (FractionRing R)))
    (hr.map (algebraMap R (FractionRing R))) 4 z hz

end PfaffianDescent
