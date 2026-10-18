import PfaffianDescent.RepresentedFunctorArtinianSmoothCriterion
import PfaffianDescent.ProjectivePositiveHomogeneousGlobalHilbertRepresentingIso
import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterGluedFinitePresentation
import PfaffianDescent.OriginalNormalizedPolynomialGlobalHilbertSmoothMap

/-!
Apply the physical Artin lifting criterion to the original global Hilbert
representing object. The criterion takes lifting of every arbitrary
finite-flat family across every local Artin square-zero test as an explicit
hypothesis. `OriginalCubicPhysicalArtinianLifts` constructs this property
for the cubic surface application, yielding smoothness and flatness of the
same Hilbert object.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Direct application to the SAME globally representing Hilbert scheme.
Its representing dictionary and LFP are both the accepted constructions.
The only remaining new input is genuine physical197 lifting for EVERY
local Artin square-zero test and arbitrary finite-flat rank-n family. -/
theorem originalPositiveHomogeneousGlobalHilbert_smooth_of_physicalArtinianLifts001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {sigma : Type} [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma R))
    (n : ℕ) (hn : 0 < n)
    (hlift : PhysicalFunctorArtinianSquareZeroLifts001 R
      (relativeFiniteFlatHilbertFunctor197 (toBase I) n)) :
    Smooth (originalPositiveHomogeneousParameterGluedToBase001 I n hn) := by
  let H : Over (Spec (.of R)) :=
    Over.mk (originalPositiveHomogeneousParameterGluedToBase001 I n hn)
  letI : LocallyOfFinitePresentation H.hom :=
    originalPositiveHomogeneousParameterGluedToBase_locallyOfFinitePresentation001 I n hn
  exact representedPhysicalFunctor_smooth_of_artinianLifts001 R
    (relativeFiniteFlatHilbertFunctor197 (toBase I) n) H
    (originalPositiveHomogeneousGlobalHilbertRepresentingIso001 I n hn) hlift

/-- Global flatness of that SAME exact Hilbert structure map follows from
the derived global Smooth instance.  It is not another deformation premise. -/
theorem originalPositiveHomogeneousGlobalHilbert_smooth_flat_of_physicalArtinianLifts001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {sigma : Type} [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma R))
    (n : ℕ) (hn : 0 < n)
    (hlift : PhysicalFunctorArtinianSquareZeroLifts001 R
      (relativeFiniteFlatHilbertFunctor197 (toBase I) n)) :
    Smooth (originalPositiveHomogeneousParameterGluedToBase001 I n hn) ∧
      Flat (originalPositiveHomogeneousParameterGluedToBase001 I n hn) := by
  letI : Smooth (originalPositiveHomogeneousParameterGluedToBase001 I n hn) :=
    originalPositiveHomogeneousGlobalHilbert_smooth_of_physicalArtinianLifts001 I n hn hlift
  exact ⟨inferInstance, inferInstance⟩

/-- The literal original polynomial global-Hilbert object used in the
accepted Lemma5.2 route, with no object reselection or reduced-support
replacement.  This remains an explicit physical-lifting criterion. -/
theorem originalNormalizedPolynomialGlobalHilbert_smooth_flat_of_physicalArtinianLifts001
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
    (n : ℕ) (hn : 0 < n)
    (hlift : PhysicalFunctorArtinianSquareZeroLifts001 R
      (relativeFiniteFlatHilbertFunctor197 (toBase (equationIdeal p hp)) n)) :
    Smooth (originalNormalizedPolynomialGlobalHilbertObject001 p hp n hn).hom ∧
      Flat (originalNormalizedPolynomialGlobalHilbertObject001 p hp n hn).hom :=
  originalPositiveHomogeneousGlobalHilbert_smooth_flat_of_physicalArtinianLifts001
    (equationIdeal p hp) n hn hlift

end PfaffianDescent
end
