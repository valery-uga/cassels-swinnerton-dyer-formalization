import PfaffianDescent.GoodIncidenceEtaleNeighborhood
import Mathlib.AlgebraicGeometry.Properties

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [Field K] [NeZero (2 : K)]

/-- The displayed triple as a point of the finite étale neighborhood. -/
noncomputable def goodTripleIntoFiniteEtaleOpen :
    Spec (.of K) ⟶ (goodFiniteEtaleOpen K).toScheme :=
  IsOpenImmersion.lift (goodFiniteEtaleOpen K).ι (goodTripleSection K)
    (by simpa only [Scheme.Opens.range_ι] using goodFiniteEtaleOpen_contains_good K)

lemma goodTripleIntoFiniteEtaleOpen_fac :
    goodTripleIntoFiniteEtaleOpen K ≫ (goodFiniteEtaleOpen K).ι = goodTripleSection K :=
  IsOpenImmersion.lift_fac _ _ _

/-- The full good fiber maps to the restriction of the incidence scheme. -/
noncomputable def goodFiberIntoRestrictedIncidence :
    goodIncidenceFiber K ⟶ (incidenceToTriples K ⁻¹ᵁ goodFiniteEtaleOpen K).toScheme :=
  (isPullback_morphismRestrict (incidenceToTriples K) (goodFiniteEtaleOpen K)).flip.lift
    (pullback.fst (incidenceToTriples K) (goodTripleSection K))
    (goodIncidenceFiberToBase K ≫ goodTripleIntoFiniteEtaleOpen K)
    (by rw [Category.assoc, goodTripleIntoFiniteEtaleOpen_fac]; exact pullback.condition)

lemma goodFiberIntoRestrictedIncidence_fst :
    goodFiberIntoRestrictedIncidence K ≫ (incidenceToTriples K ⁻¹ᵁ goodFiniteEtaleOpen K).ι =
      pullback.fst (incidenceToTriples K) (goodTripleSection K) :=
  (isPullback_morphismRestrict (incidenceToTriples K) (goodFiniteEtaleOpen K)).flip.lift_fst _ _ _

lemma goodFiberIntoRestrictedIncidence_snd :
    goodFiberIntoRestrictedIncidence K ≫ (incidenceToTriples K ∣_ goodFiniteEtaleOpen K) =
      goodIncidenceFiberToBase K ≫ goodTripleIntoFiniteEtaleOpen K :=
  (isPullback_morphismRestrict (incidenceToTriples K) (goodFiniteEtaleOpen K)).flip.lift_snd _ _ _

lemma goodFiber_restricted_isPullback :
    IsPullback (goodFiberIntoRestrictedIncidence K) (goodIncidenceFiberToBase K)
      (incidenceToTriples K ∣_ goodFiniteEtaleOpen K) (goodTripleIntoFiniteEtaleOpen K) := by
  apply IsPullback.of_right
    (h₁₂ := (incidenceToTriples K ⁻¹ᵁ goodFiniteEtaleOpen K).ι)
    (h₂₂ := (goodFiniteEtaleOpen K).ι)
  · rw [goodFiberIntoRestrictedIncidence_fst, goodTripleIntoFiniteEtaleOpen_fac]
    exact IsPullback.of_hasPullback _ _
  · exact goodFiberIntoRestrictedIncidence_snd K
  · exact (isPullback_morphismRestrict (incidenceToTriples K) (goodFiniteEtaleOpen K)).flip

lemma goodFiniteEtaleOpen_finrank_good (x : Spec (.of K)) :
    (incidenceToTriples K ∣_ goodFiniteEtaleOpen K).finrank (goodTripleIntoFiniteEtaleOpen K x) = 2 := by
  have he := Scheme.Hom.finrank_of_isPullback _ _ _ _ (goodFiber_restricted_isPullback K) x
  exact he.symm.trans (goodIncidenceFiberToBase_finrank K x)

/-- The affine parameter space of triples is irreducible over every field. -/
instance alternatingTripleScheme_irreducible : IrreducibleSpace (alternatingTripleScheme K) := by
  change IrreducibleSpace (Spec (.of (AlternatingTripleRing K)))
  infer_instance

instance goodFiniteEtaleOpen_preirreducible : PreirreducibleSpace (goodFiniteEtaleOpen K).toScheme :=
  (goodFiniteEtaleOpen K).ι.isOpenEmbedding.preirreducibleSpace

/-- The finite étale incidence projection has degree two throughout the constructed open. -/
theorem goodFiniteEtaleOpen_finrank (x : (goodFiniteEtaleOpen K).toScheme) :
    (incidenceToTriples K ∣_ goodFiniteEtaleOpen K).finrank x = 2 := by
  have he := (incidenceToTriples K ∣_ goodFiniteEtaleOpen K).isLocallyConstant_finrank
    |>.apply_eq_of_preconnectedSpace x
      (goodTripleIntoFiniteEtaleOpen K (IsLocalRing.closedPoint K))
  exact he.trans (goodFiniteEtaleOpen_finrank_good K (IsLocalRing.closedPoint K))

/-- The note's global incidence theorem: a nonempty open containing the displayed triple,
with actual common-isotropic incidence finite étale of degree two. -/
theorem incidence_finite_etale_degree_two_open :
    ∃ U : (alternatingTripleScheme K).Opens,
      (U : Set (alternatingTripleScheme K)).Nonempty ∧
      Set.range (goodTripleSection K) ⊆ (U : Set (alternatingTripleScheme K)) ∧
      IsFinite (incidenceToTriples K ∣_ U) ∧ Etale (incidenceToTriples K ∣_ U) ∧
      ∀ x : U.toScheme, (incidenceToTriples K ∣_ U).finrank x = 2 :=
  ⟨goodFiniteEtaleOpen K, goodFiniteEtaleOpen_nonempty K,
    goodFiniteEtaleOpen_contains_good K, inferInstance, inferInstance,
    goodFiniteEtaleOpen_finrank K⟩

end
end PfaffianDescent
