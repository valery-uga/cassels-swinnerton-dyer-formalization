import PfaffianDescent.QuarticSkewTangentSupport
import PfaffianDescent.QuarticTangentRelabeling
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Source-only, UNVERIFIED.  Literal graph and permutation claims in the
zero-off-diagonal proof.  Regularity and graph shape are conclusions of
transitive covariance, not supplied classification certificates. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
universe u
variable {K : Type u} [Field K]

def tangentSupportGraph (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (hskew : ∀ i j, U i j = -U j i) :
    SimpleGraph (Fin 4) where
  Adj i j := U i j ≠ 0
  symm := ⟨by
    intro i j hij
    rw [hskew j i]
    exact neg_ne_zero.mpr hij⟩
  loopless := ⟨by
    intro i hii
    exact hii (hdiag i)⟩

instance tangentSupportGraph_decidableAdj (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (hskew : ∀ i j, U i j = -U j i) :
    DecidableRel (tangentSupportGraph U hdiag hskew).Adj :=
  fun _ _ => Classical.propDecidable _

theorem tangentSupportGraph_degree (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (hskew : ∀ i j, U i j = -U j i) (i : Fin 4) :
    (tangentSupportGraph U hdiag hskew).degree i = supportDegree U i := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  unfold supportDegree
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : U i j = 0
  · simp [tangentSupportGraph, nonzeroEdge, h]
  · simp [tangentSupportGraph, nonzeroEdge, h]

/-- Every actual semilinear tangent covariance preserves the graph's
adjacency.  The graph action is thus derived from matrix covariance. -/
theorem tangentSupportGraph_covariance_adj
    (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (hskew : ∀ i j, U i j = -U j i)
    (p : Equiv.Perm (Fin 4)) (sigma : K ≃+* K) (r s : Fin 4 → K)
    (hr : ∀ i, r i ≠ 0) (hs : ∀ i, s i ≠ 0)
    (hcov : ∀ i j, sigma (U i j) = r i * s j * U (p i) (p j)) (i j : Fin 4) :
    (tangentSupportGraph U hdiag hskew).Adj i j ↔
      (tangentSupportGraph U hdiag hskew).Adj (p i) (p j) :=
  covariance_nonzero_iff U p sigma r s hr hs hcov i j

def coordinateMatchingAdj (i j : Fin 4) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)

def coordinateFourCycleAdj (i j : Fin 4) : Prop :=
  ((i = 0 ∨ i = 1) ∧ (j = 2 ∨ j = 3)) ∨
    ((i = 2 ∨ i = 3) ∧ (j = 0 ∨ j = 1))

/-- Actual common valence and complete adjacency after a vertex permutation.
These refer to the support of the supplied matrix, with no chosen graph input. -/
def ZeroEntryTangentSupportClassification (U : Fin 4 → Fin 4 → K) : Prop :=
  (∃ n : ℕ, (n = 1 ∨ n = 2) ∧ ∀ i, supportDegree U i = n) ∧
  ∃ pi : Equiv.Perm (Fin 4),
    (∀ i j, U (pi i) (pi j) ≠ 0 ↔ coordinateMatchingAdj i j) ∨
    (∀ i j, U (pi i) (pi j) ≠ 0 ↔ coordinateFourCycleAdj i j)

private theorem matching_or_complement_valence :
    ∀ a b c d e f : Bool,
      (matchingPattern a b c d e f ∨ matchingPattern (!a) (!b) (!c) (!d) (!e) (!f)) →
      a.toNat + b.toNat + c.toNat = 1 ∨ a.toNat + b.toNat + c.toNat = 2 := by
  decide

private theorem zeroEntry_support_classification_of_regular
    (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (hskew : ∀ i j, U i j = -U j i)
    (hregular : ∀ i j, supportDegree U i = supportDegree U j)
    (hrow : ∀ i, ∃ j, U i j ≠ 0)
    (hmissing : ∃ i j, i ≠ j ∧ U i j = 0) :
    ZeroEntryTangentSupportClassification U := by
  have hclass := tangent_support_classification U hdiag hskew hregular hrow hmissing
  have hn : supportDegree U 0 = 1 ∨ supportDegree U 0 = 2 := by
    have h := matching_or_complement_valence _ _ _ _ _ _ hclass
    simpa [supportDegree, Fin.sum_univ_succ, nonzeroEdge, hdiag, add_assoc] using h
  refine ⟨⟨supportDegree U 0, hn, fun i => hregular i 0⟩, ?_⟩
  rcases hclass with hmatching | hcycle
  · obtain ⟨pi, h01, h23, h02, h03, h12, h13⟩ := matching_relabel U hskew hmatching
    refine ⟨pi, Or.inl ?_⟩
    have hd (i : Fin 4) : tangentRelabel U pi i i = 0 := hdiag (pi i)
    have hs (i j : Fin 4) : tangentRelabel U pi i j = -tangentRelabel U pi j i :=
      hskew (pi i) (pi j)
    intro i j
    change tangentRelabel U pi i j ≠ 0 ↔ coordinateMatchingAdj i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinateMatchingAdj, hd, hs 1 0, hs 2 0, hs 3 0,
        hs 2 1, hs 3 1, hs 3 2, h01, h23, h02, h03, h12, h13]
  · obtain ⟨pi, h01, h23, h02, h03, h12, h13⟩ := fourCycle_relabel U hskew hcycle
    refine ⟨pi, Or.inr ?_⟩
    have hd (i : Fin 4) : tangentRelabel U pi i i = 0 := hdiag (pi i)
    have hs (i j : Fin 4) : tangentRelabel U pi i j = -tangentRelabel U pi j i :=
      hskew (pi i) (pi j)
    intro i j
    change tangentRelabel U pi i j ≠ 0 ↔ coordinateFourCycleAdj i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinateFourCycleAdj, hd, hs 1 0, hs 2 0, hs 3 0,
        hs 2 1, hs 3 1, hs 3 2, h01, h23, h02, h03, h12, h13]

/-- A transitive semilinear action on the actual tangent matrix forces
matching or four-cycle support, including the literal common valence 1 or 2.
No infinite-field hypothesis is needed for this graph assertion. -/
theorem zero_entry_transitive_skew_support_graph
    (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0) (hskew : ∀ i j, U i j = -U j i)
    (hcov : ∀ i j : Fin 4,
      ∃ (p : Equiv.Perm (Fin 4)) (sigma : K ≃+* K) (r s : Fin 4 → K),
        p i = j ∧ (∀ m, r m ≠ 0) ∧ (∀ m, s m ≠ 0) ∧
        ∀ m n, sigma (U m n) = r m * s n * U (p m) (p n))
    (hrow : ∀ i, ∃ j, U i j ≠ 0)
    (hmissing : ∃ i j, i ≠ j ∧ U i j = 0) :
    ZeroEntryTangentSupportClassification U :=
  zeroEntry_support_classification_of_regular U hdiag hskew
    (transitive_covariance_regular U hcov) hrow hmissing

/-- The actual normalized support graph has the same valence and shape.
The original covariance is used only to derive its regularity internally. -/
theorem zero_entry_rescaled_transitive_skew_support_graph
    (U : Fin 4 → Fin 4 → K) (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0)
    (hdiag : ∀ i, U i i = 0)
    (hskew : ∀ i j, rescaleTangentDirections l U i j = -rescaleTangentDirections l U j i)
    (hcov : ∀ i j : Fin 4,
      ∃ (p : Equiv.Perm (Fin 4)) (sigma : K ≃+* K) (r s : Fin 4 → K),
        p i = j ∧ (∀ m, r m ≠ 0) ∧ (∀ m, s m ≠ 0) ∧
        ∀ m n, sigma (U m n) = r m * s n * U (p m) (p n))
    (hrow : ∀ i, ∃ j, U i j ≠ 0)
    (hmissing : ∃ i j, i ≠ j ∧ rescaleTangentDirections l U i j = 0) :
    ZeroEntryTangentSupportClassification (rescaleTangentDirections l U) := by
  have hregular : ∀ i j, supportDegree (rescaleTangentDirections l U) i =
      supportDegree (rescaleTangentDirections l U) j := by
    intro i j
    rw [rescale_supportDegree l hl U i, rescale_supportDegree l hl U j]
    exact transitive_covariance_regular U hcov i j
  have hrows : ∀ i, ∃ j, rescaleTangentDirections l U i j ≠ 0 := by
    intro i
    obtain ⟨j, hj⟩ := hrow i
    exact ⟨j, mul_ne_zero (hl i) hj⟩
  exact zeroEntry_support_classification_of_regular _
    (fun i => by simp [rescaleTangentDirections, hdiag i]) hskew hregular hrows hmissing

end PfaffianDescent.QuarticNet
