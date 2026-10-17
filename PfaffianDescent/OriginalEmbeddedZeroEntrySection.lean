import PfaffianDescent.OriginalEmbeddedZeroEntryGeometry
import PfaffianDescent.IntrinsicFullQuadraticBasePoint
import PfaffianDescent.ProjectiveDescent

/-! SOURCE ONLY, UNVERIFIED. INTERNAL proof-valued consumer of the actual
derived branches. Matching uses the derived ground coordinates; C4 uses the
derived finite FULL base and the accepted finite-full-base point theorem.
No stronger closed-degree-four point theorem replaces this geometric route. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem originalEmbeddedZeroEntryGeometry_has_section
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 8)
    (hGeometry : OriginalEmbeddedZeroEntryGeometry p hp
      (i ≫ quotientProjMap (equationIdeal p hp))) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  rcases hGeometry with hMatching | hFinite
  · obtain ⟨M, hM, lines, hClosed, hAmbient, a, ha, hpa⟩ := hMatching
    exact cubic_projective_section_of_coordinates p hp a ha hpa
  · letI : IsFinite (toBase (intrinsicFullQuadraticBaseIdeal
        (i ≫ hypersurfaceToAmbient p hp))) := hFinite
    exact sectionFour_section_of_cubic_of_finite_intrinsic_full_quadratic_base p hp i hZ

end PfaffianDescent
