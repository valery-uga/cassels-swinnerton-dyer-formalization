import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveCubicKernelPointSection
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernelPulledDerivative

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist IdealSheafDataModule BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

private theorem derivativeOfEqualSections
    {X : Scheme.{u}} (N : X.Modules) (s t : N.sections) (h : s = t)
    {V : Type u} (d : Γ(N, ⊤) → V) {z : V} (ht : d (t.val (Opposite.op ⊤)) = z) :
    d (s.val (Opposite.op ⊤)) = z :=
  (congrArg (fun a => d (a.val (Opposite.op ⊤))) h).trans ht

/-- The ACTUAL Gamma of the actual positive ideal point pullback has
literal derivative phi(q/ell^3).snd in the native fibre coordinate. -/
abbrev cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernel_pointDerivative
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {B : Type u} [CommRing B] (g : Away (grading I) (ell : CoordinateRing I) →+* B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)]
    (q : grading I 3)
    (hq : g (Away.mk (grading I) ell.2 3 (q : CoordinateRing I)
      (by simpa using q.2)) = 0)
    (v : SheafOfModules.unit (scheme I).ringCatSheaf ⟶
      closedImmersionIdealTwist
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)
        (positiveSheafOfModules (grading I) 3))
    (hv : v ≫ cubicClosedPointSerreSurfaceJetCotangent_positiveIdealInclusion I
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g) =
      (positiveSheafOfModules (grading I) 3).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (grading I) 3 q))

    {E : Type u} [Field E]
    (φ : Away (grading I) (ell : CoordinateRing I) →+* CubicSurfaceFirstJet E)
    (β : B →+* E)
    (hres : cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ = β.comp g) :=
  derivativeOfEqualSections
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
      (cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ)))).obj
      (closedImmersionModule (Spec.map (CommRingCat.ofHom g)))) _ _
    (cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernel_pointSection I ell g q hq v hv
      (Spec.map (CommRingCat.ofHom
        (cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ))))
    (cubicClosedPointSerreSurfaceJetCotangent_ringNativeIdealFiberDerivative φ g β hres)
    (cubicClosedPointSerreSurfaceJetCotangent_ringNativeIdealFiberDerivative_pulledSection φ g β hres
      ⟨Away.mk (grading I) ell.2 3 (q : CoordinateRing I) (by simpa using q.2), hq⟩)

end PfaffianDescent
