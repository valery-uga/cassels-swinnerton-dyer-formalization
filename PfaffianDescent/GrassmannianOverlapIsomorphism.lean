import PfaffianDescent.GrassmannianOverlapScheme
import PfaffianDescent.GrassmannianTransitionScalar

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {m n : ℕ}

/-- The normalized universal graph lies in the reverse principal-open overlap. -/
lemma grassmannianOverlapTransition_isUnit (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    IsUnit (graphOverlapDeterminant
      (graphCoordinatePermutation (GrassmannianOverlapRing K σ) σ.symm)
      (Matrix.toLin' (grassmannianOverlapTransitionMatrix K σ))) := by
  apply (graphOverlapDeterminant_isUnit_iff _ _).mpr
  simpa only [grassmannianOverlapTransitionMatrix, Matrix.toLin'_toMatrix',
    graphCoordinatePermutation_symm] using
    graphTransition_inverse_overlap
      (graphCoordinatePermutation (GrassmannianOverlapRing K σ) σ)
      (Matrix.toLin' (grassmannianOverlapUniversalMatrix K σ))
      (grassmannianOverlapUniversal_bijective K σ)

/-- Pullback of functions under the change to the other Grassmannian chart. -/
noncomputable def grassmannianOverlapTransitionAlgHom (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    GrassmannianOverlapRing K σ.symm →ₐ[K] GrassmannianOverlapRing K σ :=
  grassmannianOverlapLift K σ.symm (grassmannianOverlapTransitionMatrix K σ)
    (grassmannianOverlapTransition_isUnit K σ)

lemma grassmannianOverlapTransitionAlgHom_universal (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (i : Fin n) (j : Fin m) :
    grassmannianOverlapTransitionAlgHom K σ
      (grassmannianOverlapUniversalMatrix K σ.symm i j) =
      grassmannianOverlapTransitionMatrix K σ i j := by
  change grassmannianOverlapLift K σ.symm _ _ (algebraMap _ _ (MvPolynomial.X (i, j))) = _
  rw [grassmannianOverlapLift_apply, MvPolynomial.aeval_X]

lemma grassmannianOverlapTransitionAlgHom_map_universal (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (grassmannianOverlapUniversalMatrix K σ.symm).map
      (grassmannianOverlapTransitionAlgHom K σ) = grassmannianOverlapTransitionMatrix K σ := by
  ext i j
  exact grassmannianOverlapTransitionAlgHom_universal K σ i j

/-- Pulling back the reverse normalized graph recovers the universal graph. -/
lemma grassmannianOverlapTransitionAlgHom_map_transition (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (grassmannianOverlapTransitionMatrix K σ.symm).map
      (grassmannianOverlapTransitionAlgHom K σ) = grassmannianOverlapUniversalMatrix K σ := by
  have hb := (graphOverlapDeterminant_isUnit_iff _ _).mp
    (grassmannianOverlapTransition_isUnit K σ)
  have hm := graphTransition_matrix_map_of_eq
    (grassmannianOverlapTransitionAlgHom K σ).toRingHom σ.symm
    (grassmannianOverlapUniversalMatrix K σ.symm) (grassmannianOverlapTransitionMatrix K σ)
    (grassmannianOverlapTransitionAlgHom_map_universal K σ)
    (grassmannianOverlapUniversal_bijective K σ.symm) hb
  exact hm.trans (graphTransition_matrix_inverse σ (grassmannianOverlapUniversalMatrix K σ)
    (grassmannianOverlapUniversal_bijective K σ) hb)

lemma grassmannianOverlapTransitionAlgHom_comp (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (grassmannianOverlapTransitionAlgHom K σ).comp
      (grassmannianOverlapTransitionAlgHom K σ.symm) =
      AlgHom.id K (GrassmannianOverlapRing K σ) := by
  change (grassmannianOverlapTransitionAlgHom K σ).comp
    (show GrassmannianOverlapRing K σ →ₐ[K] GrassmannianOverlapRing K σ.symm from
      grassmannianOverlapTransitionAlgHom K σ.symm) = _
  apply IsLocalization.algHom_ext (Submonoid.powers (grassmannianOverlapPolynomial K σ))
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  change grassmannianOverlapTransitionAlgHom K σ
      (grassmannianOverlapTransitionAlgHom K σ.symm
        (grassmannianOverlapUniversalMatrix K σ i j)) =
      grassmannianOverlapUniversalMatrix K σ i j
  have hh := grassmannianOverlapTransitionAlgHom_universal K σ.symm i j
  change grassmannianOverlapTransitionAlgHom K σ.symm
    (grassmannianOverlapUniversalMatrix K σ i j) = _ at hh
  rw [hh]
  exact congrFun (congrFun (grassmannianOverlapTransitionAlgHom_map_transition K σ) i) j

/-- The two localized coordinate algebras are isomorphic over the base ring. -/
noncomputable def grassmannianOverlapAlgEquiv (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    GrassmannianOverlapRing K σ.symm ≃ₐ[K] GrassmannianOverlapRing K σ :=
  AlgEquiv.ofAlgHom (grassmannianOverlapTransitionAlgHom K σ)
    (grassmannianOverlapTransitionAlgHom K σ.symm)
    (grassmannianOverlapTransitionAlgHom_comp K σ)
    (grassmannianOverlapTransitionAlgHom_comp K σ.symm)

/-- The two actual principal-open overlap schemes are isomorphic. -/
noncomputable def grassmannianOverlapIso (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianOverlapScheme K σ ≅ grassmannianOverlapScheme K σ.symm :=
  Scheme.Spec.mapIso (grassmannianOverlapAlgEquiv K σ).toRingEquiv.toCommRingCatIso.op

lemma grassmannianOverlapIso_hom (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (grassmannianOverlapIso K σ).hom =
      Spec.map (CommRingCat.ofHom (grassmannianOverlapTransitionAlgHom K σ).toRingHom) := rfl

lemma grassmannianOverlapIso_inv (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (grassmannianOverlapIso K σ).inv =
      Spec.map (CommRingCat.ofHom (grassmannianOverlapTransitionAlgHom K σ.symm).toRingHom) := rfl

/-- The other chart map is also an open immersion. -/
noncomputable def grassmannianOverlapOtherι (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianOverlapScheme K σ ⟶ grassmannianChartScheme K m n :=
  (grassmannianOverlapIso K σ).hom ≫ grassmannianOverlapι K σ.symm

instance grassmannianOverlapOtherι_isOpenImmersion (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    IsOpenImmersion (grassmannianOverlapOtherι K σ) := by
  unfold grassmannianOverlapOtherι
  infer_instance

lemma grassmannianOverlapTransitionAlgHom_comp_algebra (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (grassmannianOverlapTransitionAlgHom K σ).comp
      (Algebra.algHom K (GrassmannianChartRing K m n) (GrassmannianOverlapRing K σ.symm)) =
      MvPolynomial.aeval (fun ij : Fin n × Fin m => grassmannianOverlapTransitionMatrix K σ ij.1 ij.2) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  change grassmannianOverlapTransitionAlgHom K σ
    (grassmannianOverlapUniversalMatrix K σ.symm i j) = _
  rw [grassmannianOverlapTransitionAlgHom_universal, MvPolynomial.aeval_X]

/-- On coordinate functions the second open immersion is the normalized graph matrix. -/
lemma grassmannianOverlapOtherι_eq (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianOverlapOtherι K σ = Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (fun ij : Fin n × Fin m =>
        grassmannianOverlapTransitionMatrix K σ ij.1 ij.2)).toRingHom) := by
  unfold grassmannianOverlapOtherι
  rw [grassmannianOverlapIso_hom]
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f : GrassmannianChartRing K m n →ₐ[K] GrassmannianOverlapRing K σ =>
    Spec.map (CommRingCat.ofHom f.toRingHom))
    (grassmannianOverlapTransitionAlgHom_comp_algebra K σ)

end
end PfaffianDescent
