import PfaffianDescent.ProjectiveFiniteOfHilbertBound
import Mathlib.Algebra.Module.Submodule.Union

namespace PfaffianDescent
open AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [Field K] [Infinite K] {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite projective polynomial quotient over an infinite field admits
a degree-one element nonvanishing at every projective point. -/
theorem finite_projective_exists_nowhere_vanishing_linear
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    [IsFinite (toBase I)] :
    ∃ z ∈ grading I 1, ∀ x : ProjectiveSpectrum (grading I), z ∉ x.asHomogeneousIdeal := by
  have : IsLocallyArtinian (scheme I) := IsLocallyArtinian.of_locallyQuasiFinite (toBase I)
  have : CompactSpace (scheme I) := QuasiCompact.compactSpace_of_compactSpace (toBase I)
  have : IsArtinianScheme (scheme I) := ⟨⟩
  have : Finite (ProjectiveSpectrum (grading I)) := inferInstanceAs (Finite (scheme I))
  let bad (x : ProjectiveSpectrum (grading I)) : Submodule K (grading I 1) :=
    (x.asHomogeneousIdeal.toIdeal.restrictScalars K).comap (grading I 1).subtype
  have hbad (x : ProjectiveSpectrum (grading I)) : bad x ≠ ⊤ := by
    intro hx
    apply x.not_irrelevant_le
    change (HomogeneousIdeal.irrelevant (grading I)).toIdeal ≤ x.asHomogeneousIdeal.toIdeal
    rw [irrelevant_eq_coordinateIdeal]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hj : (⟨coordinate I j, coordinate_mem I j⟩ : grading I 1) ∈ bad x := by
      rw [hx]
      trivial
    exact hj
  obtain ⟨z, hz⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  exact ⟨z, z.2, hz⟩

end
end PfaffianDescent
