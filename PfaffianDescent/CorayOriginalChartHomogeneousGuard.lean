import PfaffianDescent.CorayOriginalChartFunctionFieldGeneration

/-! Every SAME original chart function has an actual homogeneous
ORIGINAL-K polynomial representative of some degree. Nonzero actual
field evaluation produces a genuine guard nonzero modulo original p. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Homogeneous localization itself constructs a SAME-degree original-K
polynomial whose normalized original chart evaluation is exactly h. -/
theorem cubicChartFunction_exists_homogeneousOriginalPolynomial001
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (h : ChartRing (equationIdeal p hp) j) :
    ∃ d : ℕ, ∃ Q : MvPolynomial (Fin 4) K,
      Q.IsHomogeneous d ∧ Q.eval₂ (chartBaseMap (equationIdeal p hp) j)
        (chartCoordinate (equationIdeal p hp) j) = h := by
  let I := equationIdeal p hp
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective (grading I) (coordinate_mem I j) h
  have ha' : a ∈ grading I d := by simpa using ha
  obtain ⟨Q, hQ, rfl⟩ := ha'
  exact ⟨d, Q, hQ, eval₂_chartCoordinate_eq_fraction I j Q hQ⟩

/-- The original coefficient square and exact representative equality
prove generic nonvanishing and nonmembership in the ORIGINAL cubic
ideal, rather than supplying a polynomial or divisor certificate. -/
theorem cubicChartFunction_fieldNonzero_exists_homogeneousOriginalGuard001
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (g : ChartRing (equationIdeal p hp) j →+* M)
    (hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M)
    (h : ChartRing (equationIdeal p hp) j) (hh : g h ≠ 0) :
    ∃ d : ℕ, ∃ Q : MvPolynomial (Fin 4) K,
      Q.IsHomogeneous d ∧ Q.eval₂ (chartBaseMap (equationIdeal p hp) j)
        (chartCoordinate (equationIdeal p hp) j) = h ∧
      Q ∉ (equationIdeal p hp).toIdeal ∧
      Q.eval₂ (algebraMap K M) (fun t => g (chartCoordinate (equationIdeal p hp) j t)) ≠ 0 := by
  obtain ⟨d, Q, hQ, hExact⟩ := cubicChartFunction_exists_homogeneousOriginalPolynomial001 p hp j h
  have hNotMem : Q ∉ (equationIdeal p hp).toIdeal := by
    intro hMem
    have hZero : h = 0 := hExact.symm.trans
      (eval₂_chartCoordinate_eq_zero_of_mem (equationIdeal p hp) j Q hMem)
    exact hh (by rw [hZero, map_zero])
  have hField : Q.eval₂ (algebraMap K M) (fun t => g (chartCoordinate (equationIdeal p hp) j t)) = g h := by
    have hMap := MvPolynomial.hom_eval₂ Q (chartBaseMap (equationIdeal p hp) j) g
      (chartCoordinate (equationIdeal p hp) j)
    rw [hBase] at hMap
    exact hMap.symm.trans (congrArg g hExact)
  refine ⟨d, Q, hQ, hExact, hNotMem, ?_⟩
  rw [hField]
  exact hh

end PfaffianDescent.Coray
end
