import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Basic

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- The original algebra projection is locally of finite presentation whenever
its actual coefficient algebra is finitely presented. -/
lemma nativeAlgebraSpecProjection_locallyOfFinitePresentation307
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] :
    LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  (LocallyOfFinitePresentation.SpecMap_iff
    (CommRingCat.ofHom (algebraMap R A))).mpr
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)

/-- Native source-open-cover locality; the actual caller supplies proved chart properties. -/
lemma nativeLocallyOfFinitePresentation_of_sourceOpenCover307
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.OpenCover.{u})
    (h : ∀ i, LocallyOfFinitePresentation (U.f i ≫ f)) :
    LocallyOfFinitePresentation f := by
  letI : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @LocallyOfFinitePresentation.{u}) (Q := RingHom.FinitePresentation)
  exact IsZariskiLocalAtSource.of_openCover
    (P := @LocallyOfFinitePresentation.{u}) (f := f) U h

end PfaffianDescent
end
