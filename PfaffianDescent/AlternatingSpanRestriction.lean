import PfaffianDescent.IncidenceGraphCoordinates

namespace PfaffianDescent
section
variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Alternating restriction is zero exactly when all pairs of vectors in the submodule evaluate to zero. -/
lemma alternatingRestriction_eq_zero_iff_pairs (W : Submodule R V) (B : AlternatingTwoForms R V) :
    alternatingRestriction R V W B = 0 ↔ ∀ x ∈ W, ∀ y ∈ W, B ![x, y] = 0 := by
  constructor
  · intro h x hx y hy
    have hh := DFunLike.congr_fun h ![⟨x, hx⟩, ⟨y, hy⟩]
    change (B.compLinearMap W.subtype) _ = 0 at hh
    rw [alternating_comp_pair] at hh
    exact hh
  · intro h
    ext v
    change B (fun i => (v i).1) = 0
    have he : (fun i => (v i).1) = ![(v 0).1, (v 1).1] := by
      funext i
      fin_cases i <;> rfl
    rw [he]
    exact h _ (v 0).2 _ (v 1).2

/-- Restriction to a generated submodule is cut out by the pair evaluations on its generators. -/
lemma alternatingRestriction_span_eq_zero_iff (v : ι → V) (B : AlternatingTwoForms R V) :
    alternatingRestriction R V (Submodule.span R (Set.range v)) B = 0 ↔
      ∀ i j, B ![v i, v j] = 0 := by
  rw [alternatingRestriction_eq_zero_iff_pairs]
  constructor
  · intro h i j
    exact h _ (Submodule.subset_span ⟨i, rfl⟩) _ (Submodule.subset_span ⟨j, rfl⟩)
  · intro h x hx y hy
    have hi (i : ι) : Submodule.span R (Set.range v) ≤ (alternatingBilinear B (v i)).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact h i j
    have hj : Submodule.span R (Set.range v) ≤ ((alternatingBilinear B).flip y).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hi i hy
    exact hj hx

end
end PfaffianDescent
