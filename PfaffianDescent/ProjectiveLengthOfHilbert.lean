import PfaffianDescent.HomogeneousChartLength
import PfaffianDescent.FiniteProjectiveHyperplane
import AllCharacteristics.FiniteFlatCycle

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [Field K] [Infinite K] {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

/-- The length of a finite projective polynomial quotient is the eventual
constant value of its actual homogeneous Hilbert function. -/
theorem projective_length_of_eventual_hilbert
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) [IsFinite (toBase I)]
    (M D : ℕ) (hdim : ∀ n, M ≤ n → finrank K (grading I n) = D) :
    AllCharacteristics.finiteSchemeRank (toBase I) = D := by
  have : ∀ n, Module.Finite K (grading I n) := polynomialQuotientGrade_finite I
  obtain ⟨z, hz, hnz⟩ := finite_projective_exists_nowhere_vanishing_linear I
  obtain ⟨N, hMN, hN⟩ := quotient_grade_eventually_bijective I z hz hnz M D hdim
  have hdim' : ∀ n, N ≤ n → finrank K (grading I n) = D :=
    fun n hn => hdim n (hMN.trans hn)
  have hfin : Module.Finite K (Away (grading I) z) :=
    (homogeneousChart_finite_of_bounded (grading I) z hz N D
      (fun n hn => (hdim' n hn).le)).1
  have hlen : finrank K (Away (grading I) z) = D :=
    homogeneousChart_finrank_of_stable (grading I) hz N D hdim' (fun n hn => (hN n hn).1)
  let j : Spec (.of (Away (grading I) z)) ⟶ scheme I := Proj.awayι (grading I) z hz (by decide : 0 < 1)
  have : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (Proj.awayι (grading I) z hz (by decide : 0 < 1)))
  have hj : IsIso j := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    change (Proj.awayι (grading I) z hz (by decide : 0 < 1)).opensRange = ⊤
    rw [Proj.opensRange_awayι]
    apply top_unique
    intro x _
    exact hnz x
  have hcomp : j ≫ toBase I =
      Spec.map (CommRingCat.ofHom (algebraMap K (Away (grading I) z))) := by
    change Proj.awayι (grading I) z hz (by decide : 0 < 1) ≫
        (Proj.toSpecZero (grading I) ≫ Spec.map (CommRingCat.ofHom (algebraMap K (grading I 0)))) = _
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl
  have : AlgebraicGeometry.Flat (toBase I) :=
    (inferInstance : @AlgebraicGeometry.Flat (scheme I) (Spec (.of K)) (toBase I))
  rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
  rw [← Scheme.Hom.finrank_comp_left_of_isIso j (toBase I), hcomp,
    Scheme.Hom.finrank_SpecMap_algebraMap]
  exact (congrFun (Module.rankAtStalk_eq_finrank_of_free
    (R := K) (M := Away (grading I) z)) _).trans hlen

end
end PfaffianDescent
