import PfaffianDescent.CubicLineResidualConjugate

/-!
# Independence of the two conjugate affine parameter triples

After extension to a field containing the two distinct residual roots, the
six Weil parameters give two independent triples of tangent coordinates.
The inverse is explicit, so this step does not assume dominance.
-/

namespace PfaffianDescent

universe u

section

variable {L : Type u} [Field L]

/-- Splitting the six affine parameters at two residual roots. -/
def conjugateAffinePair (a b : L)
    (uv : (Fin 3 → L) × (Fin 3 → L)) :
    (Fin 3 → L) × (Fin 3 → L) :=
  (uv.1 + a • uv.2, uv.1 + b • uv.2)

/-- The explicit inverse to the split parameter map. -/
noncomputable def conjugateAffinePairInverse (a b : L)
    (xy : (Fin 3 → L) × (Fin 3 → L)) :
    (Fin 3 → L) × (Fin 3 → L) :=
  ((b - a)⁻¹ • (b • xy.1 - a • xy.2),
    (b - a)⁻¹ • (xy.2 - xy.1))

theorem conjugateAffinePairInverse_leftInverse
    (a b : L) (hab : a ≠ b) :
    Function.LeftInverse (conjugateAffinePairInverse a b) (conjugateAffinePair a b) := by
  intro uv
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  apply Prod.ext <;> funext i <;>
    simp only [conjugateAffinePairInverse, conjugateAffinePair,
      Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul] <;>
    field_simp [hba] <;> ring

theorem conjugateAffinePairInverse_rightInverse
    (a b : L) (hab : a ≠ b) :
    Function.RightInverse (conjugateAffinePairInverse a b) (conjugateAffinePair a b) := by
  intro xy
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  apply Prod.ext <;> funext i <;>
    simp only [conjugateAffinePairInverse, conjugateAffinePair,
      Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul] <;>
    field_simp [hba] <;> ring

/-- The split six-parameter map is bijective in all characteristics. -/
theorem conjugateAffinePair_bijective
    (a b : L) (hab : a ≠ b) : Function.Bijective (conjugateAffinePair a b) :=
  ⟨(conjugateAffinePairInverse_leftInverse a b hab).injective,
    (conjugateAffinePairInverse_rightInverse a b hab).surjective⟩

end

/-- The actual residual root and its nontrivial conjugate give the required
independent tangent-parameter triples. -/
theorem conjugateAffinePair_bijective_adjoinRoot
    {K : Type u} [Field K] (q : Polynomial K) [Fact (Irreducible q)]
    (σ : AdjoinRoot q ≃ₐ[K] AdjoinRoot q) (hσ : σ ≠ AlgEquiv.refl) :
    Function.Bijective
      (conjugateAffinePair (AdjoinRoot.root q) (σ (AdjoinRoot.root q))) := by
  apply conjugateAffinePair_bijective
  exact (Cubic.adjoinRoot_root_ne_of_algEquiv_ne_refl q σ hσ).symm

end PfaffianDescent
