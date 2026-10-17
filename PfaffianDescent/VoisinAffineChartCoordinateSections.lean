import PfaffianDescent.VoisinSelectedConfigurationAffineChart
import PfaffianDescent.LinearNormalizedProjectivePoint
import AllCharacteristics.SpecGlobalSectionEvaluation

/-!
# Regular coordinate sections on an affine ordered configuration chart

Each lift of a coordinate map into a fixed affine Proj chart pulls the
normalized homogeneous coordinate functions back to actual global
sections of the ordered chart. The resulting matrix is the input for the
relative quadratic evaluation minor.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The regular normalized coordinate function pulled back along a map to
the affine chart of a homogeneous ideal. -/
noncomputable def pulledLinearChartCoordinate
    {L : Type u} [Field L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (U : Scheme.{u})
    (t : U ⟶ Spec (.of (Away (grading I) z)))
    (j : Fin 4) : Γ(U, ⊤) :=
  t.appTop.hom
    ((StructureSheaf.globalSectionsIso (Away (grading I) z)).hom
      (linearChartCoordinate I z hz j))

/-- Specializing a pulled coordinate section at a field-valued point is
the same as evaluating the composite map into the affine Proj chart. -/
theorem pulledLinearChartCoordinate_specialize
    {K F : Type u} [Field K] [Field F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (U : Scheme.{u})
    (a : Spec (.of F) ⟶ U)
    (t : U ⟶ Spec (.of (Away (grading I) z)))
    (j : Fin 4) :
    a.appTop.hom (pulledLinearChartCoordinate I z hz U t j) =
      (a ≫ t).appTop.hom
        ((StructureSheaf.globalSectionsIso (Away (grading I) z)).hom
          (linearChartCoordinate I z hz j)) := by
  simp only [pulledLinearChartCoordinate, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp]
  rfl

/-- Once the composite point in the affine Proj chart is identified with
`Spec φ`, the pulled coordinate specializes to `φ` applied to the chart
coordinate element. -/
theorem pulledLinearChartCoordinate_value_of_chartMap
    {K F : Type u} [Field K] [Field F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (U : Scheme.{u})
    (a : Spec (.of F) ⟶ U)
    (t : U ⟶ Spec (.of (Away (grading I) z)))
    (φ : Away (grading I) z →+* F)
    (hmap : a ≫ t = Spec.map (CommRingCat.ofHom φ))
    (j : Fin 4) :
    a.appTop.hom (pulledLinearChartCoordinate I z hz U t j) =
      (StructureSheaf.globalSectionsIso F).hom
        (φ (linearChartCoordinate I z hz j)) := by
  rw [pulledLinearChartCoordinate_specialize, hmap]
  exact specMap_appTop_structureSheafSection_apply φ
    (linearChartCoordinate I z hz j)

/-- Eight lifts into one affine Proj chart give a regular eight-by-four
matrix of normalized coordinate sections on the ordered chart. -/
noncomputable def pulledEightLinearChartCoordinates
    {L : Type u} [Field L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (U : Scheme.{u})
    (t : Fin 8 → (U ⟶ Spec (.of (Away (grading I) z)))) :
    Fin 8 → Fin 4 → Γ(U, ⊤) :=
  fun i j => pulledLinearChartCoordinate I z hz U (t i) j

end PfaffianDescent
