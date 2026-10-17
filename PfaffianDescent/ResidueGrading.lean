import PfaffianDescent.ScalarExtensionBasis
import PfaffianDescent.FrameMinimality

namespace PfaffianDescent
open Module ModuleCat MvPolynomial
open scoped TensorProduct ChangeOfRings
section
variable {K : Type*} [Field K] {M : ModuleCat (MvPolynomial (Fin 4) K)} {ι : Type*}
    (b : Basis ι (MvPolynomial (Fin 4) K) M)

/-- The degree-`d` part after tensoring a free module, whose basis has degree
`s`, with the residue field. It is the span of actual homogeneous tensor images. -/
noncomputable def homogeneousResidueSpan (s d : ℕ) :
    Submodule K ((extendScalars (constantCoeff : MvPolynomial (Fin 4) K →+* K)).obj M) :=
  if s ≤ d then Submodule.span K {v | ∃ m : M,
    (∀ i, (b.repr m i).IsHomogeneous (d-s)) ∧
      v = (1 : K) ⊗ₜ[MvPolynomial (Fin 4) K,constantCoeff] m} else ⊥

/-- In the basis degree, the homogeneous tensors span the whole residue fiber. -/
theorem homogeneousResidueSpan_self (s : ℕ) : homogeneousResidueSpan b s s = ⊤ := by
  classical
  apply top_unique
  rw [← (scalarExtensionBasis (constantCoeff : MvPolynomial (Fin 4) K →+* K) b).span_eq]
  apply Submodule.span_le.mpr
  rintro v ⟨i, rfl⟩
  rw [homogeneousResidueSpan, if_pos le_rfl, Nat.sub_self, scalarExtensionBasis_apply]
  apply Submodule.subset_span
  refine ⟨b i, ?_, rfl⟩
  intro j
  rw [b.repr_self_apply]
  split_ifs
  · exact isHomogeneous_one (Fin 4) K
  · exact isHomogeneous_zero (Fin 4) K 0

/-- Positive-degree polynomial coefficients disappear in the residue field. -/
theorem homogeneousResidueSpan_high (s d : ℕ) (h : s < d) :
    homogeneousResidueSpan b s d = ⊥ := by
  apply le_antisymm ?_ bot_le
  rw [homogeneousResidueSpan, if_pos h.le]
  apply Submodule.span_le.mpr
  rintro v ⟨m, hm, rfl⟩
  change (1 : K) ⊗ₜ[MvPolynomial (Fin 4) K,constantCoeff] m = 0
  apply (scalarExtensionBasis (constantCoeff : MvPolynomial (Fin 4) K →+* K) b).repr.injective
  ext i
  change (scalarExtensionBasis (constantCoeff : MvPolynomial (Fin 4) K →+* K) b).repr
    ((1 : K) ⊗ₜ[MvPolynomial (Fin 4) K,constantCoeff] m) i = 0
  exact (scalarExtensionBasis_repr (constantCoeff : MvPolynomial (Fin 4) K →+* K) b 1 m i).trans
    (by rw [homogeneous_constantCoeff_zero (hm i) (by omega), zero_mul])

/-- The reduced graded free module is concentrated in the degree of its basis. -/
theorem homogeneousResidueSpan_eq (s d : ℕ) :
    homogeneousResidueSpan b s d = if d = s then ⊤ else ⊥ := by
  by_cases h : d = s
  · subst d
    rw [if_pos rfl, homogeneousResidueSpan_self]
  · rw [if_neg h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · simp only [homogeneousResidueSpan, not_le.mpr hlt, ↓reduceIte]
    · exact homogeneousResidueSpan_high b s d hgt

end
end PfaffianDescent
