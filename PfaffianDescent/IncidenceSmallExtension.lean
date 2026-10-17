import PfaffianDescent.IncidenceDegreeTwoOpen
import PfaffianDescent.FiniteSchemeSmallFieldPoint
import PfaffianDescent.TripleIncidenceFieldPoint

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u
section
variable (K : Type u) [Field K] [CharZero K]

/-- A rational triple in the finite étale open lifts to the actual incidence
over a field extension of degree at most two. -/
theorem incidence_open_small_field_point (t : Spec (.of K) ⟶ alternatingTripleScheme K)
    (ht : Set.range t ⊆ (goodFiniteEtaleOpen K : Set (alternatingTripleScheme K))) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (p : Spec (.of L) ⟶ incidenceScheme K),
      finrank K L ≤ 2 ∧ p ≫ incidenceToTriples K =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ t := by
  let V := goodFiniteEtaleOpen K
  let g : Spec (.of K) ⟶ V.toScheme :=
    IsOpenImmersion.lift V.ι t (by simpa only [Scheme.Opens.range_ι] using ht)
  have hg : g ≫ V.ι = t := IsOpenImmersion.lift_fac _ _ _
  let f := incidenceToTriples K ∣_ V
  let b : pullback f g ⟶ Spec (.of K) := pullback.snd f g
  have hr : b.finrank (IsLocalRing.closedPoint K) = 2 :=
    (Scheme.Hom.finrank_pullback_snd f g _).trans (goodFiniteEtaleOpen_finrank K _)
  obtain ⟨L, hL, aL, hfin, q, hdim, hq⟩ := finiteScheme_small_field_point b (by decide) hr
  letI := hL
  letI := aL
  letI := hfin
  let p : Spec (.of L) ⟶ incidenceScheme K :=
    q ≫ pullback.fst f g ≫ (incidenceToTriples K ⁻¹ᵁ V).ι
  refine ⟨L, hL, aL, hfin, p, hdim, ?_⟩
  change (q ≫ pullback.fst f g ≫ (incidenceToTriples K ⁻¹ᵁ V).ι) ≫ incidenceToTriples K = _
  rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, ← Category.assoc (pullback.fst f g),
    pullback.condition, Category.assoc, hg, ← Category.assoc]
  exact congrArg (fun z => z ≫ t) hq

/-- The actual common-isotropic three-space consequence in Lemma 2.1. -/
theorem triple_in_open_isotropic_over_degree_le_two (c : AlternatingTripleIndex → K)
    (hc : tripleCoefficientSection K c (IsLocalRing.closedPoint K) ∈ goodFiniteEtaleOpen K) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (W : Submodule L (Fin 6 → L)),
      finrank K L ≤ 2 ∧ finrank L W = 3 ∧ ∀ k : Fin 3,
        alternatingRestriction L _ W
          (tripleCoefficientFormSix L (fun j => algebraMap K L (c j)) k) = 0 := by
  have ht : Set.range (tripleCoefficientSection K c) ⊆
      (goodFiniteEtaleOpen K : Set (alternatingTripleScheme K)) := by
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    change tripleCoefficientSection K c x ∈ goodFiniteEtaleOpen K
    rw [hx]
    exact hc
  obtain ⟨L, hL, aL, hfin, p, hdim, hp⟩ := incidence_open_small_field_point K
    (tripleCoefficientSection K c) ht
  letI := hL
  letI := aL
  letI := hfin
  obtain ⟨W, hW, hi⟩ := incidence_field_point_subspace K c p hp
  exact ⟨L, hL, aL, hfin, W, hdim, hW, hi⟩

end
end PfaffianDescent
