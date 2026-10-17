import PfaffianDescent.IncidenceOverlapScheme

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K]

lemma incidenceOverlapTransition_bijective (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    Function.Bijective (graphTransitionFirst (graphCoordinatePermutation (IncidenceOverlapRing K σ) σ.symm)
      (incidenceOverlapTransitionPoint K σ).1) := by
  simpa only [incidenceOverlapTransitionPoint, incidencePointTransition_graph,
    graphCoordinatePermutation_symm] using
    graphTransition_inverse_overlap (graphCoordinatePermutation (IncidenceOverlapRing K σ) σ)
      (incidenceOverlapUniversal K σ).1 (incidenceOverlapUniversal_bijective K σ)

/-- The pullback of coordinate functions for the full incidence chart transition. -/
noncomputable def incidenceOverlapTransitionAlgHom (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IncidenceOverlapRing K σ.symm →ₐ[K] IncidenceOverlapRing K σ :=
  incidenceOverlapLift K σ.symm (incidenceOverlapTransitionPoint K σ)
    (incidenceOverlapTransition_bijective K σ)

lemma incidenceOverlapTransitionAlgHom_generator (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (j : IncidenceGraphIndex) :
    incidenceOverlapTransitionAlgHom K σ
      (algebraMap (IncidenceGraphRing K) (IncidenceOverlapRing K σ.symm) (MvPolynomial.X j)) =
      incidenceGraphPointCoordinates (IncidenceOverlapRing K σ) (incidenceOverlapTransitionPoint K σ) j := by
  change incidenceOverlapLift K σ.symm _ _ (algebraMap _ _ (MvPolynomial.X j)) = _
  rw [incidenceOverlapLift_apply, MvPolynomial.aeval_X]

lemma incidenceOverlapTransitionAlgHom_map_universal (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceGraphPointMap (incidenceOverlapTransitionAlgHom K σ).toRingHom
      (incidenceOverlapUniversal K σ.symm) = incidenceOverlapTransitionPoint K σ := by
  apply (incidenceGraphPointCoordinates (IncidenceOverlapRing K σ)).injective
  rw [incidenceGraphPointMap_coordinates, incidenceOverlapUniversal_coordinates]
  funext j
  exact incidenceOverlapTransitionAlgHom_generator K σ j

/-- Pulling back the reverse transition recovers the complete universal incidence point. -/
lemma incidenceOverlapTransitionAlgHom_map_transition (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceGraphPointMap (incidenceOverlapTransitionAlgHom K σ).toRingHom
      (incidenceOverlapTransitionPoint K σ.symm) = incidenceOverlapUniversal K σ := by
  have hm := incidencePointTransition_map_of_eq (incidenceOverlapTransitionAlgHom K σ).toRingHom
    σ.symm (incidenceOverlapUniversal K σ.symm) (incidenceOverlapTransitionPoint K σ)
    (incidenceOverlapTransitionAlgHom_map_universal K σ)
    (incidenceOverlapUniversal_bijective K σ.symm) (incidenceOverlapTransition_bijective K σ)
  exact hm.trans (incidencePointTransition_inverse_permutation σ (incidenceOverlapUniversal K σ)
    (incidenceOverlapUniversal_bijective K σ) (incidenceOverlapTransition_bijective K σ))

lemma incidenceOverlapTransitionAlgHom_transition_coordinate (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (j : IncidenceGraphIndex) :
    incidenceOverlapTransitionAlgHom K σ
      (incidenceGraphPointCoordinates (IncidenceOverlapRing K σ.symm) (incidenceOverlapTransitionPoint K σ.symm) j) =
      algebraMap (IncidenceGraphRing K) (IncidenceOverlapRing K σ) (MvPolynomial.X j) := by
  have h := congrArg (incidenceGraphPointCoordinates (IncidenceOverlapRing K σ))
    (incidenceOverlapTransitionAlgHom_map_transition K σ)
  rw [incidenceGraphPointMap_coordinates, incidenceOverlapUniversal_coordinates] at h
  exact congrFun h j

lemma incidenceOverlapTransitionAlgHom_comp (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    (incidenceOverlapTransitionAlgHom K σ).comp (incidenceOverlapTransitionAlgHom K σ.symm) =
      AlgHom.id K (IncidenceOverlapRing K σ) := by
  change (incidenceOverlapTransitionAlgHom K σ).comp
    (show IncidenceOverlapRing K σ →ₐ[K] IncidenceOverlapRing K σ.symm from
      incidenceOverlapTransitionAlgHom K σ.symm) = _
  apply IsLocalization.algHom_ext (Submonoid.powers (incidenceOverlapPolynomial K σ))
  apply MvPolynomial.algHom_ext
  intro j
  change incidenceOverlapTransitionAlgHom K σ
    (incidenceOverlapTransitionAlgHom K σ.symm (algebraMap (IncidenceGraphRing K) (IncidenceOverlapRing K σ)
      (MvPolynomial.X j))) = algebraMap _ _ (MvPolynomial.X j)
  have hh := incidenceOverlapTransitionAlgHom_generator K σ.symm j
  change incidenceOverlapTransitionAlgHom K σ.symm
    (algebraMap (IncidenceGraphRing K) (IncidenceOverlapRing K σ) (MvPolynomial.X j)) = _ at hh
  rw [hh]
  exact incidenceOverlapTransitionAlgHom_transition_coordinate K σ j

noncomputable def incidenceOverlapAlgEquiv (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IncidenceOverlapRing K σ.symm ≃ₐ[K] IncidenceOverlapRing K σ :=
  AlgEquiv.ofAlgHom (incidenceOverlapTransitionAlgHom K σ) (incidenceOverlapTransitionAlgHom K σ.symm)
    (incidenceOverlapTransitionAlgHom_comp K σ) (incidenceOverlapTransitionAlgHom_comp K σ.symm)

/-- An isomorphism of the actual principal-open incidence overlap schemes. -/
noncomputable def incidenceOverlapIso (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceOverlapScheme K σ ≅ incidenceOverlapScheme K σ.symm :=
  Scheme.Spec.mapIso (incidenceOverlapAlgEquiv K σ).toRingEquiv.toCommRingCatIso.op

lemma incidenceOverlapIso_hom (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    (incidenceOverlapIso K σ).hom =
      Spec.map (CommRingCat.ofHom (incidenceOverlapTransitionAlgHom K σ).toRingHom) := rfl

lemma incidenceOverlapIso_inv (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    (incidenceOverlapIso K σ).inv =
      Spec.map (CommRingCat.ofHom (incidenceOverlapTransitionAlgHom K σ.symm).toRingHom) := rfl

noncomputable def incidenceOverlapOtherι (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceOverlapScheme K σ ⟶ incidenceGraphScheme K :=
  (incidenceOverlapIso K σ).hom ≫ incidenceOverlapι K σ.symm

instance incidenceOverlapOtherι_isOpenImmersion (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IsOpenImmersion (incidenceOverlapOtherι K σ) := by
  unfold incidenceOverlapOtherι
  infer_instance

lemma incidenceOverlapTransitionAlgHom_comp_algebra (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    (incidenceOverlapTransitionAlgHom K σ).comp
      (Algebra.algHom K (IncidenceGraphRing K) (IncidenceOverlapRing K σ.symm)) =
      MvPolynomial.aeval
        (incidenceGraphPointCoordinates (IncidenceOverlapRing K σ) (incidenceOverlapTransitionPoint K σ)) := by
  apply MvPolynomial.algHom_ext
  intro j
  change incidenceOverlapTransitionAlgHom K σ (algebraMap _ _ (MvPolynomial.X j)) = _
  rw [incidenceOverlapTransitionAlgHom_generator, MvPolynomial.aeval_X]

lemma incidenceOverlapOtherι_eq (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceOverlapOtherι K σ = Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval
        (incidenceGraphPointCoordinates (IncidenceOverlapRing K σ) (incidenceOverlapTransitionPoint K σ))).toRingHom) := by
  unfold incidenceOverlapOtherι
  rw [incidenceOverlapIso_hom]
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f : IncidenceGraphRing K →ₐ[K] IncidenceOverlapRing K σ =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) (incidenceOverlapTransitionAlgHom_comp_algebra K σ)

end
end PfaffianDescent
