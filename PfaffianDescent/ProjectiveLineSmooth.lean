import PfaffianDescent.LineGrassmannianProjIso
import PfaffianDescent.BundleSectionZeroLocus
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Smoothness of the Proj projective line

The projective-line parameter used by the Serre pencil is identified with the
rank-one Grassmannian.  Transporting the Grassmannian's smooth structure map
through that isomorphism supplies the flat, locally finitely presented base
needed for a global finite-flat pencil.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

section

variable (K : Type u) [CommRing K]

/-- The standard Proj projective line is smooth over its coefficient ring. -/
instance projectiveLineProjToBase_smooth : Smooth (projectiveLineProjToBase K) := by
  have h : projectiveLineProjToBase K =
      (lineGrassmannianProjIso K).inv ≫ grassmannianToBase K 1 1 := by
    rw [← lineGrassmannianProjIso_toBase]
    simp
  rw [h]
  infer_instance

/-- Consequently the projective-line parameter is flat over its base. -/
instance projectiveLineProjToBase_flat : Flat (projectiveLineProjToBase K) :=
  inferInstance

/-- The projective-line parameter is locally finitely presented over its
base, as required to apply the openness theorem for flat families. -/
instance projectiveLineProjToBase_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (projectiveLineProjToBase K) :=
  inferInstance

/-- The parameter line is universally open over its coefficient base. -/
instance projectiveLineProjToBase_universallyOpen :
    UniversallyOpen (projectiveLineProjToBase K) :=
  inferInstance

/-- The projective-line ambient space of a family over the coefficient base. -/
noncomputable abbrev projectiveLineAmbient {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) : Scheme.{u} :=
  pullback f (projectiveLineProjToBase K)

/-- Projection from the projective-line ambient space to the original
family. -/
noncomputable abbrev projectiveLineAmbientToScheme {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) : projectiveLineAmbient K f ⟶ X :=
  pullback.fst f (projectiveLineProjToBase K)

/-- Projection from the projective-line ambient space to its parameter line. -/
noncomputable abbrev projectiveLineAmbientToLine {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) : projectiveLineAmbient K f ⟶ projectiveLineProj K :=
  pullback.snd f (projectiveLineProjToBase K)

/-- The projective-line ambient space is the Cartesian base change of the
original family along the parameter line. -/
theorem projectiveLineAmbientIsPullback {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) :
    IsPullback (projectiveLineAmbientToScheme K f)
      (projectiveLineAmbientToLine K f) f (projectiveLineProjToBase K) :=
  IsPullback.of_hasPullback _ _

/-- The two standard projective-line charts pull back to a covering of the
ambient product.  These are the parameter charts on which the Serre-pencil
zero ideals will be defined and glued. -/
noncomputable def projectiveLineAmbientOpenCover {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) :
    (projectiveLineAmbient K f).OpenCover :=
  (lineProjOpenCover K).pullback₁ (projectiveLineAmbientToLine K f)

/-- Pulling the parameter line back to a family preserves its flatness. -/
instance projectiveLineAmbientToScheme_flat {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) : Flat (projectiveLineAmbientToScheme K f) :=
  inferInstance

/-- The ambient projection is locally finitely presented. -/
instance projectiveLineAmbientToScheme_locallyOfFinitePresentation
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) :
    LocallyOfFinitePresentation (projectiveLineAmbientToScheme K f) :=
  inferInstance

/-- The ambient projection is universally open, so every open parameter
chart remains an open chart after product with the original family. -/
instance projectiveLineAmbientToScheme_universallyOpen {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) : UniversallyOpen (projectiveLineAmbientToScheme K f) :=
  inferInstance

/-- The projection of the projective-line ambient space to the original
scheme is an open map. -/
theorem projectiveLineAmbientToScheme_isOpenMap {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) : IsOpenMap (projectiveLineAmbientToScheme K f) :=
  (projectiveLineAmbientToScheme K f).isOpenMap

/-- Pullback along the projective-line ambient projection preserves the unit
module.  This supplies the comparison isomorphism used to pull the two Serre
pencil sections onto the parameter space. -/
instance projectiveLineAmbientToScheme_pullbackUnitComparison_isIso {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) :
    IsIso (BundleSectionZeroLocus.pullbackUnitComparison
      (projectiveLineAmbientToScheme K f)) :=
  BundleSectionZeroLocus.isIso_pullbackUnitComparison_of_isOpenMap _
    (projectiveLineAmbientToScheme_isOpenMap K f)

end

end PfaffianDescent
