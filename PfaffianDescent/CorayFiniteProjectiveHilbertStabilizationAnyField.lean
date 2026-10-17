import PfaffianDescent.CorayFiniteProjectiveHilbertStabilization
import PfaffianDescent.CorayComponentHilbertCoefficientInvariance
import AllCharacteristics.ProjectiveBaseChangeFiniteRank
import AllCharacteristics.HomogeneousProjectiveAmbient
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! SOURCE ONLY / UNVERIFIED. Whole finite-projective Hilbert stabilization
over ANY original field, by actual algebraic-closure extension and exact
whole-ideal grade/rank descent. No Infinite/Perfect/GI/prime/genus premise;
nilpotents in the actual finite quotient are retained. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual finite projective quotient stabilization descends from its WHOLE
literal coefficient extension. No geometric component is selected after
extension, and no Hilbert value/rank comparison is supplied as a premise. -/
theorem finiteProjectiveHomogeneousIdeal_hilbertFunction_eventually_eq_rank_anyField
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    [IsFinite (toBase I)] :
    ∃ N : ℕ, ∀ m, N ≤ m →
      finrank K (grading I m) = finiteSchemeRank (toBase I) := by
  let Ω := AlgebraicClosure K
  let J := I.map (ambientCoefficientGradedRingHom (algebraMap K Ω))
  have hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap K Ω)) = J.toIdeal := rfl
  let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let e := projectiveBaseChangeIso (algebraMap K Ω) I J hIJ
  letI : IsFinite (toBase J) := by
    have hf : IsFinite (e.hom ≫ pullback.snd (toBase I) b) := inferInstance
    have hbase : e.hom ≫ pullback.snd (toBase I) b = toBase J :=
      projectiveBaseChangeIso_hom_snd (algebraMap K Ω) I J hIJ
    rw [hbase] at hf
    exact hf
  obtain ⟨N, hN⟩ := finiteProjectiveHomogeneousIdeal_hilbertFunction_eventually_eq_rank J
  have hrank : finiteSchemeRank (toBase I) = finiteSchemeRank (toBase J) :=
    projective_finiteSchemeRank_baseChange I J hIJ
  refine ⟨N, ?_⟩
  intro m hm
  rw [← actualComponentGrade_finrank_eq_coefficientExtension I J hIJ m,
    hN m hm, ← hrank]

end PfaffianDescent.Coray
