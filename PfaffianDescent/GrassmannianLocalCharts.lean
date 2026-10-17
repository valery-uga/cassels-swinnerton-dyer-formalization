import PfaffianDescent.GrassmannianLocalBasis
import PfaffianDescent.GrassmannianChartSubmodules

namespace PfaffianDescent
open Module
section
variable (R : Type*) [CommRing R] (m n : ℕ)

noncomputable def graphAmbientBasis : Basis (Fin m ⊕ Fin n) R ((Fin m → R) × (Fin n → R)) :=
  (Pi.basisFun R (Fin m)).prod (Pi.basisFun R (Fin n))

lemma graphAmbientBasis_coordinate (i j : Fin m ⊕ Fin n) :
    Sum.elim (graphAmbientBasis R m n i).1 (graphAmbientBasis R m n i).2 j = if j = i then 1 else 0 := by
  cases i <;> cases j <;> simp [graphAmbientBasis, Basis.prod_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm]

lemma graphCoordinatePermutation_basis (σ : Equiv.Perm (Fin m ⊕ Fin n)) (i : Fin m ⊕ Fin n) :
    graphCoordinatePermutation R σ (graphAmbientBasis R m n (σ i)) = graphAmbientBasis R m n i := by
  apply Prod.ext
  · funext j
    rw [graphCoordinatePermutation_fst, graphAmbientBasis_coordinate]
    change (if σ (Sum.inl j) = σ i then 1 else 0) =
      Sum.elim (graphAmbientBasis R m n i).1 (graphAmbientBasis R m n i).2 (Sum.inl j)
    rw [graphAmbientBasis_coordinate]
    simp only [σ.injective.eq_iff]
  · funext j
    rw [graphCoordinatePermutation_snd, graphAmbientBasis_coordinate]
    change (if σ (Sum.inr j) = σ i then 1 else 0) =
      Sum.elim (graphAmbientBasis R m n i).1 (graphAmbientBasis R m n i).2 (Sum.inr j)
    rw [graphAmbientBasis_coordinate]
    simp only [σ.injective.eq_iff]

end
section
variable (R : Type*) [CommRing R] [IsLocalRing R] {m n : ℕ}

/-- Every locally free quotient over a local ring lies in one of the actual standard graph charts. -/
theorem grassmannian_local_exists_graph
    (W : Module.Grassmannian R ((Fin m → R) × (Fin n → R)) n) :
    ∃ (σ : Equiv.Perm (Fin m ⊕ Fin n)) (T : Matrix (Fin n) (Fin m) R),
      W.toSubmodule = grassmannianChartSubmodule R σ T := by
  classical
  let B := graphAmbientBasis R m n
  obtain ⟨a, b, hb⟩ := grassmannian_local_quotient_basis B W
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (Sum.inr : Fin n → Fin m ⊕ Fin n) a
    Sum.inr_injective a.injective
  let e := graphCoordinatePermutation R σ
  let W' := W.toSubmodule.map e.toLinearMap
  let E : (((Fin m → R) × (Fin n → R)) ⧸ W.toSubmodule) ≃ₗ[R]
      (((Fin m → R) × (Fin n → R)) ⧸ W') := Submodule.Quotient.equiv _ _ e rfl
  let b' : Basis (Fin n) R (((Fin m → R) × (Fin n → R)) ⧸ W') := b.map E
  have hb' (i : Fin n) : b' i = graphChartQuotientMap W' (Pi.single i 1) := by
    change E (b i) = _
    rw [hb, ← hσ]
    change W'.mkQ (e (B (σ (Sum.inr i)))) = W'.mkQ (0, Pi.single i 1)
    rw [graphCoordinatePermutation_basis]
    congr 1
    simp [graphAmbientBasis, Basis.prod_apply, Pi.basisFun_apply]
  have hmap : graphChartQuotientMap W' = b'.equivFun.symm.toLinearMap := by
    apply (Pi.basisFun R (Fin n)).ext
    intro i
    rw [Pi.basisFun_apply]
    change graphChartQuotientMap W' (Pi.single i 1) = b'.equivFun.symm (Pi.single i 1)
    rw [← hb']
    simp [Basis.equivFun_symm_apply, Pi.single_apply]
  have hbij : Function.Bijective (graphChartQuotientMap W') := by
    rw [hmap]
    exact b'.equivFun.symm.bijective
  obtain ⟨f, hf, _⟩ := (graphChartQuotientMap_bijective_iff W').mp hbij
  refine ⟨σ, LinearMap.toMatrix' f, ?_⟩
  apply Submodule.map_injective_of_injective e.injective
  change W' = (grassmannianChartSubmodule R σ (LinearMap.toMatrix' f)).map e.toLinearMap
  rw [grassmannianChartSubmodule_own_chart, Matrix.toLin'_toMatrix']
  exact hf

end
end PfaffianDescent
