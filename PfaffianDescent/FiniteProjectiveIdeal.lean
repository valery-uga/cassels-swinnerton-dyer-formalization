import PfaffianDescent.ProjectiveSubschemeIdeal
import PfaffianDescent.AlgebraVectorHomogeneous

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ideal of an actual reduced projective subscheme is exactly the
homogeneous kernel of its normalized global coordinates. -/
theorem projectiveSubschemeIdeal_eq_algebraVectorIdeal
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {Z : Scheme.{u}} [IsAffine Z] [AlgebraicGeometry.IsReduced Z]
    [Algebra K Γ(Z, ⊤)] (i : Z ⟶ scheme I)
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (g : Away (grading I) z →+* Γ(Z, ⊤))
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I) (z := z)) =
      algebraMap K Γ(Z, ⊤))
    (hg : Spec.map (CommRingCat.ofHom g) ≫ Proj.awayι (grading I) z hz (by decide : 0 < 1) =
      Z.isoSpec.inv ≫ i) :
    (projectiveSubschemeIdeal I i).toIdeal =
      algebraVectorIdeal (K := K) (fun j => g (linearChartCoordinate I z hz j)) := by
  change (projectiveSubschemeIdeal I i).toIdeal =
    (algebraVectorHomogeneousIdeal (K := K) (fun j => g (linearChartCoordinate I z hz j))).toIdeal
  apply congrArg HomogeneousIdeal.toIdeal
  apply HomogeneousIdeal.ext'
  intro d f hf
  rw [projectiveSubschemeIdeal_chart_membership I i z hz g hg f hf]
  change _ ↔ f ∈ algebraVectorIdeal (K := K) (fun j => g (linearChartCoordinate I z hz j))
  rw [mem_algebraVectorIdeal_of_homogeneous _ f hf, hom_eval₂, hbase]

/-- A finite reduced closed subscheme admits generating normalized coordinates
whose homogeneous ideal is the actual embedded subscheme's vanishing ideal. -/
theorem finite_reduced_projective_subscheme_ideal [Infinite K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {Z : Scheme.{u}} [AlgebraicGeometry.IsReduced Z]
    (i : Z ⟶ scheme I) [IsClosedImmersion i] [IsFinite (i ≫ toBase I)] :
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    ∃ p : Fin 4 → Γ(Z, ⊤), Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) p) ∧
      (projectiveSubschemeIdeal I i).toIdeal = algebraVectorIdeal (K := K) p := by
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  have : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  obtain ⟨z, hz, g, hgs, hg, hdiag⟩ := finite_projective_closed_subscheme_chart I i
  refine ⟨fun j => g (linearChartCoordinate I z hz j), ?_,
    projectiveSubschemeIdeal_eq_algebraVectorIdeal I i z hz g hg hdiag⟩
  have he : eval₂Hom (algebraMap K Γ(Z, ⊤)) (fun j => g (linearChartCoordinate I z hz j)) =
      g.comp (eval₂Hom (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))
        (linearChartCoordinate I z hz)) := by
    apply RingHom.ext
    intro q
    change q.eval₂ _ _ = g (q.eval₂ _ _)
    rw [hom_eval₂, hg]
  rw [he]
  exact hgs.comp (eval₂_linearChartCoordinate_surjective I z hz)

end
end PfaffianDescent
