import PfaffianDescent.QuarticSemilinearNormalization

/-!
# The support graph of a skew tangent matrix

The transitive semilinear covariance of the conjugate tangent matrix makes
its support graph regular.  A nonempty noncomplete regular graph on four
vertices is either a matching or a four-cycle.
-/

namespace PfaffianDescent
namespace QuarticNet

variable {K : Type*} [Field K]

noncomputable def nonzeroEdge (x : K) : Bool :=
  @decide (x ≠ 0) (Classical.propDecidable _)

theorem nonzeroEdge_congr {x y : K} (h : x ≠ 0 ↔ y ≠ 0) :
    nonzeroEdge x = nonzeroEdge y :=
  congrArg (fun P : Prop => @decide P (Classical.propDecidable P)) (propext h)

noncomputable def supportDegree (U : Fin 4 → Fin 4 → K) (i : Fin 4) : ℕ :=
  ∑ j, (nonzeroEdge (U i j)).toNat

def matchingPattern (a b c d e f : Bool) : Prop :=
  (a = true ∧ f = true ∧ b = false ∧ c = false ∧ d = false ∧ e = false) ∨
  (b = true ∧ e = true ∧ a = false ∧ c = false ∧ d = false ∧ f = false) ∨
  (c = true ∧ d = true ∧ a = false ∧ b = false ∧ e = false ∧ f = false)

instance (a b c d e f : Bool) : Decidable (matchingPattern a b c d e f) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem regular_four_vertex_classification :
    ∀ a b c d e f : Bool,
      a.toNat + b.toNat + c.toNat = a.toNat + d.toNat + e.toNat →
      a.toNat + b.toNat + c.toNat = b.toNat + d.toNat + f.toNat →
      a.toNat + b.toNat + c.toNat = c.toNat + e.toNat + f.toNat →
      0 < a.toNat + b.toNat + c.toNat →
      (a = false ∨ b = false ∨ c = false ∨ d = false ∨ e = false ∨ f = false) →
      matchingPattern a b c d e f ∨
        matchingPattern (!a) (!b) (!c) (!d) (!e) (!f) := by decide

theorem covariance_nonzero_iff (U : Fin 4 → Fin 4 → K)
    (p : Equiv.Perm (Fin 4)) (sigma : K ≃+* K) (r s : Fin 4 → K)
    (hr : ∀ i, r i ≠ 0) (hs : ∀ i, s i ≠ 0)
    (hcov : ∀ i j, sigma (U i j) = r i * s j * U (p i) (p j)) (i j : Fin 4) :
    U i j ≠ 0 ↔ U (p i) (p j) ≠ 0 := by
  calc
    U i j ≠ 0 ↔ sigma (U i j) ≠ 0 := (map_ne_zero sigma).symm
    _ ↔ U (p i) (p j) ≠ 0 := by rw [hcov]; simp [hr, hs]

theorem covariance_preserves_degree (U : Fin 4 → Fin 4 → K)
    (p : Equiv.Perm (Fin 4)) (sigma : K ≃+* K) (r s : Fin 4 → K)
    (hr : ∀ i, r i ≠ 0) (hs : ∀ i, s i ≠ 0)
    (hcov : ∀ i j, sigma (U i j) = r i * s j * U (p i) (p j)) (i : Fin 4) :
    supportDegree U i = supportDegree U (p i) := by
  unfold supportDegree
  calc
    _ = ∑ j, (nonzeroEdge (U (p i) (p j))).toNat := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg Bool.toNat (nonzeroEdge_congr
        (covariance_nonzero_iff U p sigma r s hr hs hcov i j))
    _ = _ := Equiv.sum_comp p (fun j => (nonzeroEdge (U (p i) j)).toNat)

theorem transitive_covariance_regular (U : Fin 4 → Fin 4 → K)
    (hcov : ∀ i j : Fin 4,
      ∃ (p : Equiv.Perm (Fin 4)) (sigma : K ≃+* K) (r s : Fin 4 → K),
        p i = j ∧ (∀ m, r m ≠ 0) ∧ (∀ m, s m ≠ 0) ∧
        ∀ m n, sigma (U m n) = r m * s n * U (p m) (p n)) :
    ∀ i j, supportDegree U i = supportDegree U j := by
  intro i j
  obtain ⟨p, sigma, r, s, hp, hr, hs, hU⟩ := hcov i j
  rw [← hp]
  exact covariance_preserves_degree U p sigma r s hr hs hU i

theorem supportDegree_positive (U : Fin 4 → Fin 4 → K) (i : Fin 4)
    (hi : ∃ j, U i j ≠ 0) : 0 < supportDegree U i := by
  obtain ⟨j, hj⟩ := hi
  have hle : (nonzeroEdge (U i j)).toNat ≤ supportDegree U i := by
    unfold supportDegree
    exact Finset.single_le_sum (f := fun j => (nonzeroEdge (U i j)).toNat)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hone : (nonzeroEdge (U i j)).toNat = 1 := by simp [nonzeroEdge, hj]
  omega

theorem tangent_support_classification (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (hskew : ∀ i j, U i j = -U j i)
    (hregular : ∀ i j, supportDegree U i = supportDegree U j)
    (hrow : ∀ i, ∃ j, U i j ≠ 0) (hmissing : ∃ i j, i ≠ j ∧ U i j = 0) :
    matchingPattern (nonzeroEdge (U 0 1)) (nonzeroEdge (U 0 2))
      (nonzeroEdge (U 0 3)) (nonzeroEdge (U 1 2)) (nonzeroEdge (U 1 3))
      (nonzeroEdge (U 2 3)) ∨
    matchingPattern (!(nonzeroEdge (U 0 1))) (!(nonzeroEdge (U 0 2)))
      (!(nonzeroEdge (U 0 3))) (!(nonzeroEdge (U 1 2))) (!(nonzeroEdge (U 1 3)))
      (!(nonzeroEdge (U 2 3))) := by
  have hedge (i j : Fin 4) : nonzeroEdge (U i j) = nonzeroEdge (U j i) := by
    apply nonzeroEdge_congr
    rw [hskew i j, neg_ne_zero]
  have hz (i : Fin 4) : nonzeroEdge (U i i) = false := by simp [nonzeroEdge, hdiag]
  apply regular_four_vertex_classification
  · simpa [supportDegree, Fin.sum_univ_succ, hz, hedge 1 0, add_assoc] using hregular 0 1
  · simpa [supportDegree, Fin.sum_univ_succ, hz, hedge 2 0, hedge 2 1, add_assoc]
      using hregular 0 2
  · simpa [supportDegree, Fin.sum_univ_succ, hz, hedge 3 0, hedge 3 1, hedge 3 2, add_assoc]
      using hregular 0 3
  · simpa [supportDegree, Fin.sum_univ_succ, hz, add_assoc] using supportDegree_positive U 0 (hrow 0)
  · obtain ⟨i, j, hij, hU⟩ := hmissing
    have hE : nonzeroEdge (U i j) = false := by simp [nonzeroEdge, hU]
    have hE' : nonzeroEdge (U j i) = false := (hedge i j).symm.trans hE
    fin_cases i <;> fin_cases j
    all_goals first
    | exact (hij rfl).elim
    | tauto

end QuarticNet
end PfaffianDescent
