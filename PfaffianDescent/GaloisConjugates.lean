import PfaffianDescent.TransitiveGeneralPosition
import PfaffianDescent.GeometricEvaluation
import Mathlib.FieldTheory.Normal.Basic

namespace PfaffianDescent
open Module

section
variable {K A L : Type*} [Field K] [Field A] [Algebra K A]
    [Field L] [Algebra K L] [Normal K L]

/-- Two embeddings into a normal extension differ by a ground-field automorphism. -/
theorem embeddings_normal_transitive (φ ψ : A →ₐ[K] L) :
    ∃ σ : L ≃ₐ[K] L, ∀ a, σ (φ a) = ψ a := by
  letI : Algebra A L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A L := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let σ : L ≃ₐ[K] L := AlgEquiv.ofBijective (ψ.liftNormal L)
    (AlgHom.normal_bijective K L L _)
  refine ⟨σ, ?_⟩
  intro a
  change (ψ.liftNormal L) (algebraMap A L a) = algebraMap L L (ψ a)
  exact ψ.liftNormal_commutes L a

variable [FiniteDimensional K A]

lemma quintic_embeddings_surjective (hdim : finrank K A = 5)
    (ev : Fin 5 → A →ₐ[K] L) (hev : Function.Injective ev) : Function.Surjective ev := by
  classical
  letI := Fintype.ofFinite (A →ₐ[K] L)
  have hbound : Fintype.card (A →ₐ[K] L) ≤ 5 := by
    simpa only [Nat.card_eq_fintype_card, hdim] using card_algHom_le_finrank K A L
  have hlow : 5 ≤ Fintype.card (A →ₐ[K] L) := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective ev hev
  exact ((Fintype.bijective_iff_injective_and_card ev).mpr
    ⟨hev, by simpa only [Fintype.card_fin] using Nat.le_antisymm hlow hbound⟩).2

/-- A full set of five embeddings into a normal extension is a transitive
semilinear orbit, with the permutation and automorphism constructed internally. -/
theorem quintic_conjugates_transitive (hdim : finrank K A = 5)
    (ev : Fin 5 → A →ₐ[K] L) (hev : Function.Injective ev) (p : Vec A 4) :
    ∀ i j : Fin 5, ∃ (σ : L ≃+* L) (e : Equiv.Perm (Fin 5)),
      e i = j ∧ ∀ a b, ev (e a) (p b) = σ (ev a (p b)) := by
  classical
  let E := Equiv.ofBijective ev ⟨hev, quintic_embeddings_surjective hdim ev hev⟩
  intro i j
  obtain ⟨σ, hσ⟩ := embeddings_normal_transitive (ev i) (ev j)
  let action := AlgEquiv.arrowCongr (AlgEquiv.refl : A ≃ₐ[K] A) σ
  let e : Equiv.Perm (Fin 5) := (E.trans action).trans E.symm
  have he (a : Fin 5) : ev (e a) = σ.toAlgHom.comp (ev a) := by
    change E (E.symm (action (E a))) = _
    rw [E.apply_symm_apply]
    ext x
    rfl
  refine ⟨σ.toRingEquiv, e, ?_, ?_⟩
  · apply hev
    rw [he]
    ext x
    exact hσ x
  · intro a b
    exact congrArg (fun φ : A →ₐ[K] L => φ (p b)) (he a)

/-- Five conjugates which span projective three-space have no coplanar quartet. -/
theorem quintic_conjugates_general_position (hdim : finrank K A = 5)
    (ev : Fin 5 → A →ₐ[K] L) (hev : Function.Injective ev) (p : Vec A 4)
    (hspan : Submodule.span L (Set.range (fun i j => ev i (p j))) = ⊤) :
    FivePointGeneralPosition (fun i j => ev i (p j)) :=
  transitive_five_points_general_position _ hspan (quintic_conjugates_transitive hdim ev hev p)

end
end PfaffianDescent
