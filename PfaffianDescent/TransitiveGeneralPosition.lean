import PfaffianDescent.TransitiveFrame

namespace PfaffianDescent
open scoped BigOperators

section
variable {K : Type*} [Field K]

/-- If every nonzero relation among five vectors has all coefficients nonzero,
then every four vectors are linearly independent. -/
theorem five_point_general_position_of_relation_coeffs (p : Fin 5 → Vec K 4)
    (hp : ∀ c : Fin 5 → K, c ≠ 0 → (∑ i, c i • p i = 0) → ∀ i, c i ≠ 0) :
    FivePointGeneralPosition p := by
  classical
  intro e he
  apply Fintype.linearIndependent_iff.mpr
  intro d hd
  let c : Fin 5 → K := fun i => ∑ j : Fin 4, if e j = i then d j else 0
  have hce (j : Fin 4) : c (e j) = d j := by
    simp [c, he.eq_iff]
  have hrel : ∑ i : Fin 5, c i • p i = 0 := by
    calc
      _ = ∑ j : Fin 4, ∑ i : Fin 5, (if e j = i then d j else 0) • p i := by
        simp only [c, Finset.sum_smul]
        rw [Finset.sum_comm]
      _ = ∑ j : Fin 4, d j • p (e j) := by
        simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      _ = 0 := hd
  have hn : ¬ Function.Surjective e := by
    intro h
    have hcard := Fintype.card_le_of_surjective e h
    norm_num at hcard
  change ¬ (∀ b, ∃ a, e a = b) at hn
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  have hci : c i = 0 := by simp [c, hi]
  have hc : c = 0 := by
    by_contra h
    exact hp c h hrel i hci
  intro j
  exact (hce j).symm.trans (congrFun hc (e j))

/-- Five vectors spanning four-space and forming a transitive semilinear orbit
are in general linear position. This is the relation-space argument for the
five normalized conjugates in the note. -/
theorem transitive_five_points_general_position (p : Fin 5 → Vec K 4)
    (hp : Submodule.span K (Set.range p) = ⊤)
    (htrans : ∀ i j : Fin 5, ∃ (σ : K ≃+* K) (e : Equiv.Perm (Fin 5)),
      e i = j ∧ ∀ a b, p (e a) b = σ (p a b)) :
    FivePointGeneralPosition p :=
  five_point_general_position_of_relation_coeffs p
    (transitive_frame_relation_coeff_ne_zero p hp htrans)

end
end PfaffianDescent
