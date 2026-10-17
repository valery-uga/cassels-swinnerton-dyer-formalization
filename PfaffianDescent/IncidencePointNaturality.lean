import PfaffianDescent.IncidencePointTransition
import PfaffianDescent.IncidenceCoordinateEvaluation
import PfaffianDescent.GraphTransitionCompatible

namespace PfaffianDescent
section
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Compatibility of actual graphs and forms implies compatibility of all forty-five coordinates. -/
lemma incidenceGraphPointCoordinates_of_compatible (φ : R →+* S)
    (p : IncidenceGraphPoints R) (q : IncidenceGraphPoints S)
    (hfg : ∀ a, q.1 (φ ∘ a) = φ ∘ p.1 a)
    (hB : ∀ (i : Fin 3) (x y : (Fin 3 → R) × (Fin 3 → R)),
      (q.2 i).1 ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] = φ ((p.2 i).1 ![x, y])) :
    incidenceGraphPointCoordinates S q = φ ∘ incidenceGraphPointCoordinates R p := by
  funext s
  rcases s with ⟨i, j⟩ | ⟨i, s⟩
  · have h := hfg (Pi.single j 1)
    rw [ringHom_comp_single_one] at h
    exact congrFun h i
  · exact congrFun (incidenceGraphKernelCoordinates_map φ p.1 q.1 hfg (p.2 i) (q.2 i) (hB i)) s

lemma alternatingTransport_pair
    (e : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    (B : AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)))
    (x y : (Fin 3 → R) × (Fin 3 → R)) :
    alternatingTransport e B ![x, y] = B ![e.symm x, e.symm y] :=
  alternating_comp_pair B e.symm.toLinearMap x y

/-- Transport of forms by coordinate permutations is compatible with arbitrary ring maps. -/
lemma alternatingTransport_permutation_map (φ : R →+* S)
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (B : AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)))
    (C : AlternatingTwoForms S ((Fin 3 → S) × (Fin 3 → S)))
    (hBC : ∀ x y : (Fin 3 → R) × (Fin 3 → R),
      C ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] = φ (B ![x, y]))
    (x y : (Fin 3 → R) × (Fin 3 → R)) :
    alternatingTransport (graphCoordinatePermutation S σ) C
      ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] =
      φ (alternatingTransport (graphCoordinatePermutation R σ) B ![x, y]) := by
  have he (z : (Fin 3 → R) × (Fin 3 → R)) :
      (graphCoordinatePermutation S σ).symm (φ ∘ z.1, φ ∘ z.2) =
        (φ ∘ ((graphCoordinatePermutation R σ).symm z).1,
         φ ∘ ((graphCoordinatePermutation R σ).symm z).2) := by
    simpa only [graphCoordinatePermutation_symm] using graphCoordinatePermutation_map φ σ.symm z
  rw [alternatingTransport_pair, alternatingTransport_pair, he x, he y]
  exact hBC _ _

/-- The complete incidence transition is compatible with every extension of coefficients. -/
theorem incidencePointTransition_map (φ : R →+* S)
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints R)
    (hR : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) p.1))
    (hS : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation S σ)
      (incidenceGraphPointMap φ p).1)) :
    incidencePointTransition (graphCoordinatePermutation S σ) (incidenceGraphPointMap φ p) hS =
      incidenceGraphPointMap φ (incidencePointTransition (graphCoordinatePermutation R σ) p hR) := by
  apply (incidenceGraphPointCoordinates S).injective
  rw [incidenceGraphPointMap_coordinates]
  apply incidenceGraphPointCoordinates_of_compatible φ
  · exact graphTransition_map_of_compatible φ σ p.1 (incidenceGraphPointMap φ p).1
      (incidenceGraphPointMap_graph φ p) hR hS
  · intro i x y
    exact alternatingTransport_permutation_map φ σ (p.2 i).1 ((incidenceGraphPointMap φ p).2 i).1
      (incidenceGraphPointMap_form φ p i) x y

lemma incidencePointTransition_map_of_eq (φ : R →+* S)
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints R) (q : IncidenceGraphPoints S)
    (hq : incidenceGraphPointMap φ p = q)
    (hR : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) p.1))
    (hS : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation S σ) q.1)) :
    incidenceGraphPointMap φ (incidencePointTransition (graphCoordinatePermutation R σ) p hR) =
      incidencePointTransition (graphCoordinatePermutation S σ) q hS := by
  subst q
  exact (incidencePointTransition_map φ σ p hR hS).symm

lemma incidencePointTransition_inverse_permutation
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints R)
    (h : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) p.1))
    (hb : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ.symm)
      (incidencePointTransition (graphCoordinatePermutation R σ) p h).1)) :
    incidencePointTransition (graphCoordinatePermutation R σ.symm)
      (incidencePointTransition (graphCoordinatePermutation R σ) p h) hb = p := by
  simpa only [graphCoordinatePermutation_symm] using
    incidencePointTransition_inverse (graphCoordinatePermutation R σ) p h

lemma incidencePointTransition_overlap_after (σ τ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (p : IncidenceGraphPoints R)
    (hp : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) p.1)) :
    Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R τ)
      (incidencePointTransition (graphCoordinatePermutation R σ) p hp).1) ↔
      Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R (τ.trans σ)) p.1) := by
  simpa only [incidencePointTransition_graph, graphCoordinatePermutation_trans] using
    graphTransition_overlap_after (graphCoordinatePermutation R σ) (graphCoordinatePermutation R τ) p.1 hp

lemma incidencePointTransition_cocycle_permutation (σ τ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (p : IncidenceGraphPoints R)
    (he : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R σ) p.1))
    (hd : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R τ)
      (incidencePointTransition (graphCoordinatePermutation R σ) p he).1))
    (hed : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation R (τ.trans σ)) p.1)) :
    incidencePointTransition (graphCoordinatePermutation R τ)
      (incidencePointTransition (graphCoordinatePermutation R σ) p he) hd =
      incidencePointTransition (graphCoordinatePermutation R (τ.trans σ)) p hed := by
  have hh := graphTransition_comp_overlap (graphCoordinatePermutation R σ) (graphCoordinatePermutation R τ) p.1 he hd
  simpa only [graphCoordinatePermutation_trans] using
    incidencePointTransition_cocycle (graphCoordinatePermutation R σ) (graphCoordinatePermutation R τ) p he hd hh

lemma incidencePointTransition_congr
    (e : ((Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ((Fin 3 → R) × (Fin 3 → R)))
    {p q : IncidenceGraphPoints R} (hpq : p = q)
    (hp : Function.Bijective (graphTransitionFirst e p.1))
    (hq : Function.Bijective (graphTransitionFirst e q.1)) :
    incidencePointTransition e p hp = incidencePointTransition e q hq := by
  subst q
  rfl

end
end PfaffianDescent
