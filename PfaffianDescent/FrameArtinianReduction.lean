import PfaffianDescent.FrameHilbertFunction
import PfaffianDescent.FrameQuotientSocle

namespace PfaffianDescent
open scoped BigOperators

section
variable {K : Type*} [Field K]

noncomputable def frameLinearForm : MvPolynomial (Fin 4) K := ∑ i : Fin 4, MvPolynomial.X i

private theorem last_frameArtinRelation : frameArtinRelations (K := K) 5 = frameLinearForm := by
  change MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.X 3 =
    ∑ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.X 3 : MvPolynomial (Fin 4) K) =
    MvPolynomial.X 0 + (MvPolynomial.X 1 + (MvPolynomial.X 2 + MvPolynomial.X 3))
  ring

private theorem frameRelations_cast (i : Fin 5) :
    frameRelations (K := K) i = frameArtinRelations i.castSucc := by
  fin_cases i <;> rfl

private theorem frameArtinRelations_range :
    Set.range (frameArtinRelations (K := K)) = Set.range frameRelations ∪ {frameLinearForm} := by
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inr last_frameArtinRelation
  · rintro (⟨i, rfl⟩ | h)
    · exact ⟨i.castSucc, (frameRelations_cast i).symm⟩
    · exact ⟨5, last_frameArtinRelation.trans h.symm⟩

theorem frameArtinIdeal_eq_sup : frameArtinIdeal (K := K) =
    frameIdeal ⊔ Ideal.span {frameLinearForm} := by
  rw [frameArtinIdeal, frameArtinRelations_range, Ideal.span_union]
  rfl

theorem frameLinearForm_mk : Ideal.Quotient.mkₐ K (frameIdeal (K := K)) frameLinearForm =
    FrameCoordinateRing.ell := by
  simp only [frameLinearForm, map_sum, FrameCoordinateRing.ell, FrameCoordinateRing.x]

theorem frameLinearIdeal_map :
    (Ideal.span {frameLinearForm (K := K)}).map (Ideal.Quotient.mkₐ K (frameIdeal (K := K))) =
    Ideal.span {FrameCoordinateRing.ell} := by
  rw [Ideal.map_span, Set.image_singleton, frameLinearForm_mk]

/-- Quotienting the homogeneous coordinate ring by the regular linear form is exactly the
polynomial quotient used in the Artinian socle calculation. -/
noncomputable def frameArtinianReductionEquiv :
    (FrameCoordinateRing K ⧸ Ideal.span {FrameCoordinateRing.ell}) ≃ₐ[K] FrameQuotient K :=
  ((Ideal.quotientEquivAlgOfEq K (frameLinearIdeal_map (K := K)).symm).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ K (frameIdeal (K := K)) (Ideal.span {frameLinearForm}))).trans
      (Ideal.quotientEquivAlgOfEq K frameArtinIdeal_eq_sup.symm)

end
end PfaffianDescent
