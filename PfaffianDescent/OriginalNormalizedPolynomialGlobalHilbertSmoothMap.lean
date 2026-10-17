import PfaffianDescent.OriginalNormalizedPolynomialGlobalHilbertChartIso
import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterGluedFinitePresentation
import PfaffianDescent.MonomialPolynomialLocusSmoothOpen312
import PfaffianDescent.OriginalNormalizedWholeOpenPoint317
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Ordinary exact-map transport for native smooth opens, before any
large original projective parameter scheme is substituted. -/
private theorem exactOriginalParameterMapSmoothLocusEquality001
    {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] (h : f = g) :
    f.smoothLocus = g.smoothLocus := by
  cases h
  rfl

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (p : MvPolynomial (Fin 4) R) {d : ℕ} (hp : p.IsHomogeneous d)
variable (j : Fin 4) (n : ℕ) (hn : 0 < n)

/-- SAME all-positive internally constructed global Hilbert parameter object
in the original R slice; no global model is supplied or reselected. -/
def originalNormalizedPolynomialGlobalHilbertObject001 : Over (Spec (.of R)) :=
  Over.mk (originalPositiveHomogeneousParameterGluedToBase001 (equationIdeal p hp) n hn)

/-- The original projective hypersurface is separated, derived from its
actual properness theorem317. Register this exact original-base instance
locally before constructing the slice chart inclusion, with no new premise. -/
private theorem originalNormalizedPolynomialWholeBase_isSeparated001 :
    IsSeparated (toBase (equationIdeal p hp)) :=
  originalNormalizedWholeOpen_separated317 p hp

attribute [local instance] originalNormalizedPolynomialWholeBase_isSeparated001

/-- Literal normalized312 classifier maps into its SAME chosen coordinate
chart by the constructed original-base Yoneda iso, then its actual gluing
inclusion maps into the SAME global parameter object. -/
def originalNormalizedPolynomialGlobalHilbertMap001 :
    monomialPolynomialContainmentRepresentingObject312 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j) ⟶
        originalNormalizedPolynomialGlobalHilbertObject001 p hp n hn :=
  (originalNormalizedPolynomialChosenChartOverIso001 p hp j n hn).hom ≫
    relativeOpenChartParameterGluedChartInclusionOver001 (toBase (equationIdeal p hp))
      (fun a : projectivePositiveHomogeneousChartIndex001 (grading (equationIdeal p hp)) =>
        Proj.basicOpen (grading (equationIdeal p hp)) a.val) n
      (originalPositiveHomogeneousChartIndexRepresentingObject001 (equationIdeal p hp) n hn)
      (originalPositiveHomogeneousChartIndexRepresentingIso001 (equationIdeal p hp) n hn)
      (originalNormalizedCoordinateChartIndex001 p hp j)

/-- Exact original R triangle of the constructed local-to-global map. -/
theorem originalNormalizedPolynomialGlobalHilbertMap_toOriginalBase001 :
    (originalNormalizedPolynomialGlobalHilbertMap001 p hp j n hn).left ≫
      (originalNormalizedPolynomialGlobalHilbertObject001 p hp n hn).hom =
        (monomialPolynomialContainmentRepresentingObject312 R 3 n
          (originalNormalizedHypersurfacePolynomial312 p j)).hom :=
  (originalNormalizedPolynomialGlobalHilbertMap001 p hp j n hn).w

/-- Its open immersion follows from the actual Scheme iso and constructed
native chart inclusion. No open immersion or image equality is assumed. -/
theorem originalNormalizedPolynomialGlobalHilbertMap_isOpenImmersion001 :
    IsOpenImmersion (originalNormalizedPolynomialGlobalHilbertMap001 p hp j n hn).left := by
  let E := originalNormalizedPolynomialChosenChartOverIso001 p hp j n hn
  let e := (Over.forget (Spec (.of R))).mapIso E
  let a := originalNormalizedCoordinateChartIndex001 p hp j
  let D := originalPositiveHomogeneousParameterSchemeGlueData001 (equationIdeal p hp) n hn
  have he : IsOpenImmersion e.hom := inferInstance
  have hD : IsOpenImmersion (D.ι a) := Scheme.GlueData.ι_isOpenImmersion D a
  change IsOpenImmersion (e.hom ≫ D.ι a)
  exact @IsOpenImmersion.comp _ _ _ e.hom (D.ι a) he hD

/-- Actual global LFP is DERIVED from accepted source-cover descent, before
forming its smooth locus. This adds no LFP input to any public header. -/
private theorem originalNormalizedPolynomialGlobalHilbertObject_lfp001 :
    LocallyOfFinitePresentation (originalNormalizedPolynomialGlobalHilbertObject001 p hp n hn).hom :=
  originalPositiveHomogeneousParameterGluedToBase_locallyOfFinitePresentation001
    (equationIdeal p hp) n hn

attribute [local instance] originalNormalizedPolynomialGlobalHilbertObject_lfp001

/-- The literal local polynomial representer's LFP is already proved312,
registered only locally for the exact smooth-open comparison below. -/
private theorem originalNormalizedPolynomialLocalHilbertObject_lfp001 :
    LocallyOfFinitePresentation (monomialPolynomialContainmentRepresentingObject312 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j)).hom :=
  monomialPolynomialContainmentLocusToBase_locallyOfFinitePresentation312 R 3 n
    (originalNormalizedHypersurfacePolynomial312 p j)

attribute [local instance] originalNormalizedPolynomialLocalHilbertObject_lfp001

/-- The GLOBAL smooth locus restricts to EXACTLY the actual local312
smooth open, via the derived open immersion and exact original-base map. -/
theorem originalNormalizedPolynomialGlobalHilbertMap_preimage_smoothLocus001 :
    (originalNormalizedPolynomialGlobalHilbertMap001 p hp j n hn).left ⁻¹ᵁ
      (originalNormalizedPolynomialGlobalHilbertObject001 p hp n hn).hom.smoothLocus =
        monomialPolynomialContainmentSmoothOpen312 R 3 n
          (originalNormalizedHypersurfacePolynomial312 p j) := by
  letI : IsOpenImmersion (originalNormalizedPolynomialGlobalHilbertMap001 p hp j n hn).left :=
    originalNormalizedPolynomialGlobalHilbertMap_isOpenImmersion001 p hp j n hn
  have h := Scheme.Hom.preimage_smoothLocus_eq
    (originalNormalizedPolynomialGlobalHilbertMap001 p hp j n hn).left
    (originalNormalizedPolynomialGlobalHilbertObject001 p hp n hn).hom
  exact h.trans (exactOriginalParameterMapSmoothLocusEquality001
    (originalNormalizedPolynomialGlobalHilbertMap_toOriginalBase001 p hp j n hn))

/-- Actual317 local coefficient smooth membership maps into the genuine
GLOBAL smooth open. Its original-point caller will DERIVE the local
membership from317, rather than supply global smoothness as a premise. -/
theorem originalNormalizedPolynomialGlobalHilbertMap_mem_smoothLocus001
    (x : (monomialPolynomialContainmentRepresentingObject312 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j)).left)
    (hx : x ∈ monomialPolynomialContainmentSmoothOpen312 R 3 n
      (originalNormalizedHypersurfacePolynomial312 p j)) :
    (originalNormalizedPolynomialGlobalHilbertMap001 p hp j n hn).left x ∈
      (originalNormalizedPolynomialGlobalHilbertObject001 p hp n hn).hom.smoothLocus := by
  change x ∈ (originalNormalizedPolynomialGlobalHilbertMap001 p hp j n hn).left ⁻¹ᵁ
    (originalNormalizedPolynomialGlobalHilbertObject001 p hp n hn).hom.smoothLocus
  rw [originalNormalizedPolynomialGlobalHilbertMap_preimage_smoothLocus001]
  exact hx

end PfaffianDescent
end
