import PfaffianDescent.IncidencePointNaturality
import PfaffianDescent.IncidenceGraphProjection
import PfaffianDescent.GrassmannianAtlas

namespace PfaffianDescent
open Module
section
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The ordered ambient basis, independent of the chosen Grassmannian chart. -/
noncomputable def incidenceAmbientBasis (R : Type*) [CommRing R] :
    Basis (Fin 6) R ((Fin 3 → R) × (Fin 3 → R)) :=
  ((Pi.basisFun R (Fin 3)).prod (Pi.basisFun R (Fin 3))).reindex finSumFinEquiv

lemma incidenceAmbientBasis_map (φ : R →+* S) (i : Fin 6) :
    incidenceAmbientBasis S i =
      (φ ∘ (incidenceAmbientBasis R i).1, φ ∘ (incidenceAmbientBasis R i).2) := by
  simp only [incidenceAmbientBasis, Basis.reindex_apply]
  rcases (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm i with j | j
  · apply Prod.ext <;> simp only [Basis.prod_apply_inl_fst, Basis.prod_apply_inl_snd,
      Pi.basisFun_apply, ringHom_comp_single_one, ringHom_comp_zero]
  · apply Prod.ext <;> simp only [Basis.prod_apply_inr_fst, Basis.prod_apply_inr_snd,
      Pi.basisFun_apply, ringHom_comp_single_one, ringHom_comp_zero]

private lemma incidence_pair_eta {A : Type*} (v : Fin 2 → A) : v = ![v 0, v 1] := by
  funext i
  fin_cases i <;> rfl

lemma incidenceAmbientCoordinates_map (φ : R →+* S)
    (B : AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)))
    (C : AlternatingTwoForms S ((Fin 3 → S) × (Fin 3 → S)))
    (hBC : ∀ x y : (Fin 3 → R) × (Fin 3 → R),
      C ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] = φ (B ![x, y]))
    (s : Set.powersetCard (Fin 6) 2) :
    alternatingCoordinates (incidenceAmbientBasis S) C s =
      φ (alternatingCoordinates (incidenceAmbientBasis R) B s) := by
  rw [alternatingCoordinates_apply, alternatingCoordinates_apply]
  rw [incidence_pair_eta ((incidenceAmbientBasis S : Fin 6 → _) ∘ Set.powersetCard.ofFinEmbEquiv.symm s),
    incidence_pair_eta ((incidenceAmbientBasis R : Fin 6 → _) ∘ Set.powersetCard.ofFinEmbEquiv.symm s)]
  simp only [Function.comp_apply, incidenceAmbientBasis_map φ]
  exact hBC _ _

/-- Recover the original ambient form from a point in the chart indexed by `i`. -/
noncomputable def incidenceOriginalForm (i : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (p : IncidenceGraphPoints R) (k : Fin 3) :
    AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)) :=
  alternatingTransport (graphCoordinatePermutation R i.symm) (p.2 k).1

lemma incidenceOriginalForm_map (φ : R →+* S)
    (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints R) (k : Fin 3)
    (x y : (Fin 3 → R) × (Fin 3 → R)) :
    incidenceOriginalForm i (incidenceGraphPointMap φ p) k
      ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] =
      φ (incidenceOriginalForm i p k ![x, y]) :=
  alternatingTransport_permutation_map φ i.symm _ _ (incidenceGraphPointMap_form φ p k) x y

/-- The original form is unchanged by a Grassmannian chart transition. -/
lemma incidenceOriginalForm_transition (i j : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (p : IncidenceGraphPoints R)
    (hp : Function.Bijective (graphTransitionFirst
      (graphCoordinatePermutation R (grassmannianChartChange i j)) p.1)) (k : Fin 3) :
    incidenceOriginalForm j
      (incidencePointTransition (graphCoordinatePermutation R (grassmannianChartChange i j)) p hp) k =
      incidenceOriginalForm i p k := by
  change (alternatingTransport (graphCoordinatePermutation R (grassmannianChartChange i j))).trans
    (alternatingTransport (graphCoordinatePermutation R j.symm)) (p.2 k).1 = _
  rw [alternatingTransport_trans, graphCoordinatePermutation_trans]
  have he : j.symm.trans (grassmannianChartChange i j) = i.symm := by
    apply Equiv.ext
    intro a
    simp [grassmannianChartChange]
  rw [he]
  rfl

/-- The forty-five original ambient coefficients carried by an incidence chart point. -/
noncomputable def incidenceOriginalCoefficients (i : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (p : IncidenceGraphPoints R) (k : AlternatingTripleIndex) : R :=
  alternatingCoordinates (incidenceAmbientBasis R) (incidenceOriginalForm i p k.1) k.2

lemma incidenceOriginalCoefficients_map (φ : R →+* S)
    (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints R) (k : AlternatingTripleIndex) :
    incidenceOriginalCoefficients i (incidenceGraphPointMap φ p) k =
      φ (incidenceOriginalCoefficients i p k) :=
  incidenceAmbientCoordinates_map φ _ _ (incidenceOriginalForm_map φ i p k.1) k.2

lemma incidenceOriginalCoefficients_transition (i j : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (p : IncidenceGraphPoints R)
    (hp : Function.Bijective (graphTransitionFirst
      (graphCoordinatePermutation R (grassmannianChartChange i j)) p.1)) (k : AlternatingTripleIndex) :
    incidenceOriginalCoefficients j
      (incidencePointTransition (graphCoordinatePermutation R (grassmannianChartChange i j)) p hp) k =
      incidenceOriginalCoefficients i p k := by
  unfold incidenceOriginalCoefficients
  rw [incidenceOriginalForm_transition]

end
end PfaffianDescent
