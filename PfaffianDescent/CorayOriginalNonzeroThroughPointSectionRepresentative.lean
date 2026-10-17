import PfaffianDescent.CorayBoundedOriginalSectionFamily

noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Any nonzero section of the SAME original through-point module has a
fresh homogeneous ORIGINAL-K polynomial representative through that point.
In particular this applies to the SAME basis member b(a), without changing
its chart, basis or normalized evaluation. -/
theorem originalNonzeroThroughPointSection_exists_fresh_polynomial_representative001
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (s : cubicThroughCoordinateSections p hp n y hpy) (hs : s ≠ 0) :
    ∃ q : MvPolynomial (Fin 4) K, q.IsHomogeneous n ∧
      q.eval₂ (algebraMap K L) y = 0 ∧
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = s.1.1 := by
  obtain ⟨q, hq, hy, hRep⟩ :=
    (cubicThroughCoordinateSections_mem_iff p hp n y hpy s.1).mp s.2
  refine ⟨q, hq, hy, ?_, hRep⟩
  intro h
  have hqZero : Ideal.Quotient.mk (equationIdeal p hp).toIdeal q = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr h
  apply hs
  apply Subtype.ext
  apply Subtype.ext
  exact hRep.symm.trans hqZero

end PfaffianDescent.Coray
