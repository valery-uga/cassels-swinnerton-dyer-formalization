import PfaffianDescent.IncidenceSchemeCocycle
import PfaffianDescent.GrassmannianAtlas

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K]

lemma incidenceOverlapPolynomial_refl :
    incidenceOverlapPolynomial K (Equiv.refl (Fin 3 ⊕ Fin 3)) = 1 := by
  rw [incidenceOverlapPolynomial, grassmannianOverlapPolynomial_refl, map_one]

lemma incidenceOverlapTransitionPoint_refl :
    incidenceOverlapTransitionPoint K (Equiv.refl (Fin 3 ⊕ Fin 3)) =
      incidenceOverlapUniversal K (Equiv.refl (Fin 3 ⊕ Fin 3)) := by
  have hr : Function.Bijective (graphTransitionFirst
      (LinearEquiv.refl (IncidenceOverlapRing K (Equiv.refl (Fin 3 ⊕ Fin 3))) _)
      (incidenceOverlapUniversal K (Equiv.refl (Fin 3 ⊕ Fin 3))).1) := Function.bijective_id
  simpa only [incidenceOverlapTransitionPoint, graphCoordinatePermutation_refl] using
    incidencePointTransition_refl (incidenceOverlapUniversal K (Equiv.refl (Fin 3 ⊕ Fin 3))) hr

lemma incidenceOverlapOtherι_refl :
    incidenceOverlapOtherι K (Equiv.refl (Fin 3 ⊕ Fin 3)) =
      incidenceOverlapι K (Equiv.refl (Fin 3 ⊕ Fin 3)) := by
  apply incidenceChart_morphism_ext K _ _ (incidenceOverlapOtherι_toBase K _)
  have h₁ := incidenceChartPoint_other K (Equiv.refl (Fin 3 ⊕ Fin 3)) (𝟙 _)
  have h₂ := incidenceChartPoint_overlap K (Equiv.refl (Fin 3 ⊕ Fin 3)) (𝟙 _)
  simp only [Category.id_comp, incidenceOverlapTransitionPoint_refl] at h₁ h₂
  exact h₁.trans h₂.symm

instance incidenceOverlapι_refl_isIso :
    IsIso (incidenceOverlapι K (Equiv.refl (Fin 3 ⊕ Fin 3))) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [incidenceOverlapι_opensRange, incidenceOverlapPolynomial_refl, PrimeSpectrum.basicOpen_one]
  rfl

lemma incidenceOverlapι_isIso_of_eq_refl (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (hσ : σ = Equiv.refl _) : IsIso (incidenceOverlapι K σ) := by
  subst σ
  infer_instance

lemma incidenceOverlapOtherι_of_eq_refl (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (hσ : σ = Equiv.refl _) : incidenceOverlapOtherι K σ = incidenceOverlapι K σ := by
  subst σ
  exact incidenceOverlapOtherι_refl K

noncomputable abbrev incidenceAtlasOverlap (ij : Equiv.Perm (Fin 3 ⊕ Fin 3) × Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    Scheme.{u} := incidenceOverlapScheme K (grassmannianChartChange ij.1 ij.2)

noncomputable def incidenceAtlasι (i j : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAtlasOverlap K (i, j) ⟶ incidenceGraphScheme K :=
  incidenceOverlapι K (grassmannianChartChange i j)

instance incidenceAtlasι_isOpenImmersion (i j : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    IsOpenImmersion (incidenceAtlasι K i j) :=
  incidenceOverlapι_isOpenImmersion K (grassmannianChartChange i j)

instance incidenceAtlasι_self_isIso (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) : IsIso (incidenceAtlasι K i i) :=
  incidenceOverlapι_isIso_of_eq_refl K _ (grassmannianChartChange_self i)

noncomputable def incidenceAtlasTransition (i j : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAtlasOverlap K (i, j) ⟶ incidenceAtlasOverlap K (j, i) :=
  (incidenceOverlapIso K (grassmannianChartChange i j)).hom

lemma incidenceAtlasTransition_self (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAtlasTransition K i i = 𝟙 _ := by
  exact (cancel_mono (incidenceAtlasι K i i)).mp
    ((incidenceOverlapOtherι_of_eq_refl K _ (grassmannianChartChange_self i)).trans (Category.id_comp _).symm)

lemma incidenceAtlasTransition_inverse (i j : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAtlasTransition K i j ≫ incidenceAtlasTransition K j i = 𝟙 _ := by
  change (incidenceOverlapIso K (grassmannianChartChange i j)).hom ≫
    (incidenceOverlapIso K (grassmannianChartChange i j)).inv = _
  exact Iso.hom_inv_id _

lemma incidenceAtlasTransition_ι (i j : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceAtlasTransition K i j ≫ incidenceAtlasι K j i =
      incidenceOverlapOtherι K (grassmannianChartChange i j) := rfl

lemma incidenceAtlas_triple_exists (i j k : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    ∃ c : pullback (incidenceAtlasι K i j) (incidenceAtlasι K i k) ⟶ incidenceAtlasOverlap K (j, k),
      c ≫ incidenceAtlasι K j k = pullback.fst _ _ ≫ incidenceAtlasTransition K i j ≫ incidenceAtlasι K j i ∧
      c ≫ incidenceAtlasTransition K j k ≫ incidenceAtlasι K k j =
        pullback.snd _ _ ≫ incidenceAtlasTransition K i k ≫ incidenceAtlasι K k i := by
  exact incidence_scheme_transition_cocycle_of_eq K
    (grassmannianChartChange i j) (grassmannianChartChange j k) (grassmannianChartChange i k)
    (grassmannianChartChange_comp i j k) (pullback.fst _ _) (pullback.snd _ _) pullback.condition

end
end PfaffianDescent
