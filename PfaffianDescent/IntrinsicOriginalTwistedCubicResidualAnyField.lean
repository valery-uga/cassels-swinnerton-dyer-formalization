import PfaffianDescent.IntrinsicOriginalTwistedCubicIntersectionLift
import PfaffianDescent.GroundTwistedCubicCubicIntersectionAnyField
import PfaffianDescent.QuarticExceptionalResidual

/-! The direct scheme-theoretic exceptional proof
over ANY ground field, including its actual contained-or-rank-nine scheme
alternative.  No finite-field point shortcut is needed in this module. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem intrinsicOriginalTwistedFullBase_cubic_intersection_alternative_anyField
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface F hF) [IsClosedImmersion i]
    (hTwisted : QuarticNet.GroundTwistedCubicPresentation
      (intrinsicFullQuadraticBaseIdeal (i ≫ hypersurfaceToAmbient F hF))) :
    (∃ c : scheme (intrinsicFullQuadraticBaseIdeal
        (i ≫ hypersurfaceToAmbient F hF)) ⟶ hypersurface F hF,
      c ≫ hypersurfaceToAmbient F hF = quotientProjMap
        (intrinsicFullQuadraticBaseIdeal (i ≫ hypersurfaceToAmbient F hF)) ∧
      c ≫ hypersurfaceToBase F hF = toBase
        (intrinsicFullQuadraticBaseIdeal (i ≫ hypersurfaceToAmbient F hF)) ∧
      ∃ s : Spec (.of k) ⟶ hypersurface F hF,
        s ≫ hypersurfaceToBase F hF = 𝟙 _) ∨
    (∃ hfinite : IsFinite (toBase (intrinsicOriginalCubicFullBaseIntersectionIdeal F hF i)),
      @AllCharacteristics.finiteSchemeRank k _ _
        (toBase (intrinsicOriginalCubicFullBaseIntersectionIdeal F hF i)) hfinite = 9 ∧
      ∃ l : Z ⟶ scheme (intrinsicOriginalCubicFullBaseIntersectionIdeal F hF i),
        IsClosedImmersion l ∧
        l ≫ intrinsicOriginalCubicFullBaseIntersectionToSurface F hF i = i ∧
        l ≫ quotientProjMap (intrinsicOriginalCubicFullBaseIntersectionIdeal F hF i) =
          i ≫ hypersurfaceToAmbient F hF ∧
        l ≫ toBase (intrinsicOriginalCubicFullBaseIntersectionIdeal F hF i) =
          i ≫ hypersurfaceToBase F hF) := by
  classical
  let B := intrinsicFullQuadraticBaseIdeal (i ≫ hypersurfaceToAmbient F hF)
  by_cases hmem : F ∈ B.toIdeal
  · exact Or.inl (hTwisted.contained_cubic_section F hF hmem)
  · obtain ⟨hfinite, hX⟩ :=
      hTwisted.cubicIntersection_finite_rank_nine_anyField F hF hmem
    obtain ⟨l, lB, hl, hlB, hc, hcurve, hB, hambient, hbase⟩ :=
      intrinsicOriginalCubicFullBaseIntersection_original_lift F hF i
    exact Or.inr ⟨hfinite, hX, l, hl, hc, hambient, hbase⟩

/-- Direct exceptional-branch endpoint over every field.  Its structural
hypotheses are the ORIGINAL cubic, ORIGINAL closed finite rank-eight Z, and
the ground twisted presentation of their FULL intrinsic quadratic base.
It derives the actual intersection and its rank, retains the exact original
Z embedding, and invokes residual rank one internally. -/
theorem sectionFour_section_of_cubic_of_twisted_intrinsic_full_quadratic_base_direct
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface F hF) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase F hF)]
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ hypersurfaceToBase F hF) = 8)
    (hTwisted : QuarticNet.GroundTwistedCubicPresentation
      (intrinsicFullQuadraticBaseIdeal (i ≫ hypersurfaceToAmbient F hF))) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  rcases intrinsicOriginalTwistedFullBase_cubic_intersection_alternative_anyField
      F hF i hTwisted with ⟨c, hcAmbient, hcBase, s, hs⟩ |
      ⟨hfinite, hX, l, hl, hc, hambient, hbase⟩
  · exact ⟨s, hs⟩
  · letI := hfinite
    letI := hl
    let c := intrinsicOriginalCubicFullBaseIntersectionToSurface F hF i
    have hcBase : c ≫ hypersurfaceToBase F hF =
        toBase (intrinsicOriginalCubicFullBaseIntersectionIdeal F hF i) :=
      intrinsicOriginalCubicFullBaseIntersectionToSurface_toBase F hF i
    letI : IsFinite (c ≫ hypersurfaceToBase F hF) := by
      rw [hcBase]
      infer_instance
    have hXactual : AllCharacteristics.finiteSchemeRank
        (c ≫ hypersurfaceToBase F hF) = 9 := by
      rw [AllCharacteristics.finiteSchemeRank_eq_finrank, hcBase,
        ← AllCharacteristics.finiteSchemeRank_eq_finrank]
      exact hX
    have hZmap : l ≫ c ≫ hypersurfaceToBase F hF = i ≫ hypersurfaceToBase F hF := by
      rw [← Category.assoc, hc]
    have hZactual : AllCharacteristics.finiteSchemeRank
        (l ≫ c ≫ hypersurfaceToBase F hF) = 8 := by
      rw [AllCharacteristics.finiteSchemeRank_eq_finrank, hZmap,
        ← AllCharacteristics.finiteSchemeRank_eq_finrank]
      exact hZ
    exact QuarticNet.cubic_section_of_rank_nine_exceptional_intersection
      F hF c l hXactual hZactual

end PfaffianDescent
