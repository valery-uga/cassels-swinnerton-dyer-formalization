import AllCharacteristics.ProjectivePoints
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

namespace AllCharacteristics.HomogeneousProjective

open AlgebraicGeometry TopologicalSpace

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A prime homogeneous quotient with an actual projective point is
irreducible: the bottom homogeneous prime is its generic point. -/
theorem irreducibleSpace_of_prime_and_point
    {k : Type u} [Field k] {σ : Type}
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k))
    (hprime : I.toIdeal.IsPrime) (P : scheme I) :
    IrreducibleSpace (scheme I) := by
  letI : IsDomain (CoordinateRing I) :=
    (Ideal.Quotient.isDomain_iff_prime I.toIdeal).mpr hprime
  have hrel : ¬ HomogeneousIdeal.irrelevant (grading I) ≤
      (⊥ : HomogeneousIdeal (grading I)) := by
    intro h
    exact P.not_irrelevant_le (h.trans bot_le)
  let eta : ProjectiveSpectrum (grading I) :=
    ⟨⊥, by simpa using (Ideal.isPrime_bot (α := CoordinateRing I)), hrel⟩
  have hclosure : closure ({eta} : Set (ProjectiveSpectrum (grading I))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    apply (ProjectiveSpectrum.le_iff_mem_closure (grading I) eta x).mp
    change (⊥ : HomogeneousIdeal (grading I)) ≤ x.asHomogeneousIdeal
    exact bot_le
  apply (irreducibleSpace_def (scheme I)).mpr
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum (grading I)))
  rw [← hclosure]
  exact isIrreducible_singleton.closure

end AllCharacteristics.HomogeneousProjective
