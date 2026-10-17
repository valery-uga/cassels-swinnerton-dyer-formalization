import Mathlib.RingTheory.Extension.Presentation.Submersive

namespace PfaffianDescent
open Algebra MvPolynomial

section
variable (K ι σ : Type*) [CommRing K]
  [Algebra (MvPolynomial ι K) (MvPolynomial σ K)]
  [IsScalarTower K (MvPolynomial ι K) (MvPolynomial σ K)]

/-- The evaluation presenting the source polynomial algebra over the target polynomial algebra. -/
noncomputable def polynomialMapEvaluation :
    MvPolynomial σ (MvPolynomial ι K) →ₐ[MvPolynomial ι K] MvPolynomial σ K := aeval X

/-- The coefficient lift is a section of the presentation evaluation. -/
lemma polynomialMapEvaluation_section (p : MvPolynomial σ K) :
    polynomialMapEvaluation K ι σ (MvPolynomial.map (algebraMap K (MvPolynomial ι K)) p) = p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [polynomialMapEvaluation, MvPolynomial.map_C, aeval_C]
    exact (IsScalarTower.algebraMap_apply K (MvPolynomial ι K) (MvPolynomial σ K) a).symm
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, map_X, polynomialMapEvaluation, aeval_X] at *; rw [hp]

/-- The equations of the graph of a polynomial map, one for every target coordinate. -/
noncomputable def polynomialMapRelation (i : ι) : MvPolynomial σ (MvPolynomial ι K) :=
  MvPolynomial.map (algebraMap K (MvPolynomial ι K))
    (algebraMap (MvPolynomial ι K) (MvPolynomial σ K) (X i)) - C (X i)

lemma polynomialMapEvaluation_relation (i : ι) :
    polynomialMapEvaluation K ι σ (polynomialMapRelation K ι σ i) = 0 := by
  rw [polynomialMapRelation, map_sub, polynomialMapEvaluation_section]
  change algebraMap (MvPolynomial ι K) (MvPolynomial σ K) (X i) -
    aeval X (C (X i)) = 0
  rw [aeval_C, sub_self]

/-- The graph equations generate the entire kernel, over any coefficient ring. -/
theorem polynomialMapEvaluation_ker :
    RingHom.ker (polynomialMapEvaluation K ι σ).toRingHom =
      Ideal.span (Set.range (polynomialMapRelation K ι σ)) := by
  let J := Ideal.span (Set.range (polynomialMapRelation K ι σ))
  let q : MvPolynomial σ (MvPolynomial ι K) →+* _ := Ideal.Quotient.mk J
  let t : MvPolynomial σ K →+* _ := q.comp (MvPolynomial.map (algebraMap K (MvPolynomial ι K)))
  have hrel (i : ι) :
      t (algebraMap (MvPolynomial ι K) (MvPolynomial σ K) (X i)) = q (C (X i)) := by
    apply sub_eq_zero.mp
    change q (MvPolynomial.map (algebraMap K (MvPolynomial ι K))
      (algebraMap (MvPolynomial ι K) (MvPolynomial σ K) (X i))) - q (C (X i)) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have he : t.comp (polynomialMapEvaluation K ι σ).toRingHom = q := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext'
      · ext a
        change t (polynomialMapEvaluation K ι σ (C (C a))) = q (C (C a))
        rw [polynomialMapEvaluation, aeval_C]
        have h := (IsScalarTower.algebraMap_apply K (MvPolynomial ι K) (MvPolynomial σ K) a).symm
        change algebraMap (MvPolynomial ι K) (MvPolynomial σ K) (C a) = C a at h
        rw [h]
        exact congrArg q (MvPolynomial.map_C _ _)
      · intro i
        change t (polynomialMapEvaluation K ι σ (C (X i))) = q (C (X i))
        rw [polynomialMapEvaluation, aeval_C]
        exact hrel i
    · intro i
      change t (aeval X (X i)) = q (X i)
      rw [aeval_X]
      exact congrArg q (MvPolynomial.map_X _ _)
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := RingHom.congr_fun he p
    change t (polynomialMapEvaluation K ι σ p) = q p at h
    change polynomialMapEvaluation K ι σ p = 0 at hp
    rw [hp, map_zero] at h
    exact h.symm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact polynomialMapEvaluation_relation K ι σ i

/-- A polynomial map has one generator for each source coordinate and one relation for each target coordinate. -/
noncomputable def polynomialMapPresentation :
    Algebra.Presentation (MvPolynomial ι K) (MvPolynomial σ K) σ ι where
  val := X
  σ' := MvPolynomial.map (algebraMap K (MvPolynomial ι K))
  aeval_val_σ' := polynomialMapEvaluation_section K ι σ
  relation := polynomialMapRelation K ι σ
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val]
    exact (polynomialMapEvaluation_ker K ι σ).symm

/-- Equal-dimensional polynomial source and target give a square presentation. -/
noncomputable def polynomialMapSquarePresentation (e : ι ≃ σ) :
    Algebra.PreSubmersivePresentation (MvPolynomial ι K) (MvPolynomial σ K) σ ι where
  __ := polynomialMapPresentation K ι σ
  map := e
  map_inj := e.injective

lemma polynomialMapSquarePresentation_dimension (e : ι ≃ σ) :
    (polynomialMapSquarePresentation K ι σ e).dimension = 0 := by
  change Nat.card σ - Nat.card ι = 0
  rw [Nat.card_congr e, Nat.sub_self]

end
end PfaffianDescent
