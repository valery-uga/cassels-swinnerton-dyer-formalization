import PfaffianDescent.GrassmannianSchemeCocycle
import Mathlib.AlgebraicGeometry.Pullbacks

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K] {m n : ℕ}

lemma grassmannianOverlapPolynomial_refl :
    grassmannianOverlapPolynomial K (Equiv.refl (Fin m ⊕ Fin n)) = 1 := by
  unfold grassmannianOverlapPolynomial
  have h : graphOverlapMatrix (Equiv.refl (Fin m ⊕ Fin n))
      (fun i j => MvPolynomial.X (i, j) : Matrix (Fin n) (Fin m) (GrassmannianChartRing K m n)) = 1 := by
    ext i j
    rfl
  rw [h, Matrix.det_one]

lemma grassmannianOverlapTransitionMatrix_refl :
    grassmannianOverlapTransitionMatrix K (Equiv.refl (Fin m ⊕ Fin n)) =
      grassmannianOverlapUniversalMatrix K (Equiv.refl (Fin m ⊕ Fin n)) :=
  graphTransitionMatrix_refl _ _

lemma grassmannianOverlapOtherι_refl :
    grassmannianOverlapOtherι K (Equiv.refl (Fin m ⊕ Fin n)) =
      grassmannianOverlapι K (Equiv.refl (Fin m ⊕ Fin n)) := by
  apply grassmannianChart_morphism_ext K _ _ (grassmannianOverlapOtherι_toBase K _)
  have h₁ := grassmannianChartMatrix_other K (Equiv.refl (Fin m ⊕ Fin n)) (𝟙 _)
  have h₂ := grassmannianChartMatrix_overlap K (Equiv.refl (Fin m ⊕ Fin n)) (𝟙 _)
  simp only [Category.id_comp, grassmannianOverlapTransitionMatrix_refl] at h₁ h₂
  exact h₁.trans h₂.symm

lemma grassmannianOverlapIso_refl_hom :
    (grassmannianOverlapIso K (Equiv.refl (Fin m ⊕ Fin n))).hom = 𝟙 _ := by
  exact (cancel_mono (grassmannianOverlapι K (Equiv.refl (Fin m ⊕ Fin n)))).mp
    ((grassmannianOverlapOtherι_refl K).trans (Category.id_comp _).symm)

instance grassmannianOverlapι_refl_isIso :
    IsIso (grassmannianOverlapι K (Equiv.refl (Fin m ⊕ Fin n))) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [grassmannianOverlapι_opensRange, grassmannianOverlapPolynomial_refl, PrimeSpectrum.basicOpen_one]
  rfl

lemma grassmannianOverlapι_isIso_of_eq_refl (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (hσ : σ = Equiv.refl _) : IsIso (grassmannianOverlapι K σ) := by
  subst σ
  infer_instance

lemma grassmannianOverlapOtherι_of_eq_refl (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (hσ : σ = Equiv.refl _) : grassmannianOverlapOtherι K σ = grassmannianOverlapι K σ := by
  subst σ
  exact grassmannianOverlapOtherι_refl K

/-- Relative coordinate permutation between two labeled standard charts. -/
def grassmannianChartChange (i j : Equiv.Perm (Fin m ⊕ Fin n)) : Equiv.Perm (Fin m ⊕ Fin n) :=
  j.trans i.symm

lemma grassmannianChartChange_self (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianChartChange i i = Equiv.refl _ := Equiv.self_trans_symm i

lemma grassmannianChartChange_symm (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    (grassmannianChartChange i j).symm = grassmannianChartChange j i := rfl

lemma grassmannianChartChange_comp (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    (grassmannianChartChange j k).trans (grassmannianChartChange i j) = grassmannianChartChange i k := by
  apply Equiv.ext
  intro a
  change i.symm (j (j.symm (k a))) = i.symm (k a)
  rw [Equiv.apply_symm_apply]

noncomputable abbrev grassmannianAtlasOverlap (ij : Equiv.Perm (Fin m ⊕ Fin n) × Equiv.Perm (Fin m ⊕ Fin n)) :
    Scheme.{u} := grassmannianOverlapScheme K (grassmannianChartChange ij.1 ij.2)

noncomputable def grassmannianAtlasι (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianAtlasOverlap K (i, j) ⟶ grassmannianChartScheme K m n :=
  grassmannianOverlapι K (grassmannianChartChange i j)

instance grassmannianAtlasι_isOpenImmersion (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    IsOpenImmersion (grassmannianAtlasι K i j) := by
  exact grassmannianOverlapι_isOpenImmersion K (grassmannianChartChange i j)

instance grassmannianAtlasι_self_isIso (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    IsIso (grassmannianAtlasι K i i) := by
  exact grassmannianOverlapι_isIso_of_eq_refl K _ (grassmannianChartChange_self i)

noncomputable def grassmannianAtlasTransition (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianAtlasOverlap K (i, j) ⟶ grassmannianAtlasOverlap K (j, i) :=
  (grassmannianOverlapIso K (grassmannianChartChange i j)).hom

lemma grassmannianAtlasTransition_self (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianAtlasTransition K i i = 𝟙 _ := by
  exact (cancel_mono (grassmannianAtlasι K i i)).mp
    ((grassmannianOverlapOtherι_of_eq_refl K _ (grassmannianChartChange_self i)).trans
      (Category.id_comp _).symm)

lemma grassmannianAtlasTransition_inverse (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianAtlasTransition K i j ≫ grassmannianAtlasTransition K j i = 𝟙 _ := by
  change (grassmannianOverlapIso K (grassmannianChartChange i j)).hom ≫
    (grassmannianOverlapIso K (grassmannianChartChange i j)).inv = _
  exact Iso.hom_inv_id _

lemma grassmannianAtlasTransition_ι (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianAtlasTransition K i j ≫ grassmannianAtlasι K j i =
      grassmannianOverlapOtherι K (grassmannianChartChange i j) := rfl

lemma grassmannianAtlas_triple_exists (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    ∃ c : pullback (grassmannianAtlasι K i j) (grassmannianAtlasι K i k) ⟶
        grassmannianAtlasOverlap K (j, k),
      c ≫ grassmannianAtlasι K j k =
        pullback.fst _ _ ≫ grassmannianAtlasTransition K i j ≫ grassmannianAtlasι K j i ∧
      c ≫ grassmannianAtlasTransition K j k ≫ grassmannianAtlasι K k j =
        pullback.snd _ _ ≫ grassmannianAtlasTransition K i k ≫ grassmannianAtlasι K k i := by
  exact grassmannian_scheme_transition_cocycle_of_eq K
    (grassmannianChartChange i j) (grassmannianChartChange j k) (grassmannianChartChange i k)
    (grassmannianChartChange_comp i j k) (pullback.fst _ _) (pullback.snd _ _) pullback.condition

end
end PfaffianDescent
