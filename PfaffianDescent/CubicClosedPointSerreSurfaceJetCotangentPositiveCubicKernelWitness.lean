import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveCubicKernelFiberApply
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveCubicKernelFiberMap

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist IdealSheafDataModule BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

private theorem existsUniqueWithProperty {A : Sort u} {P Q : A → Prop}
    (h : ∃! a, P a) (hq : ∀ a, P a → Q a) : ∃! a, P a ∧ Q a := by
  obtain ⟨a, ha, hu⟩ := h
  exact ⟨a, ⟨ha, hq a ha⟩, fun b hb => hu b hb.1⟩

/-- Native global cubic ideal lift AND its ACTUAL point-fibre derivative,
from only the literal ring vanishing and the actual mixed-field jet map. -/
abbrev cubicClosedPointSerreSurfaceJetCotangent_exists_positiveCubicKernel_globalFiberWitness
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {B : Type u} [CommRing B] (g : Away (grading I) (ell : CoordinateRing I) →+* B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)]
    (q : grading I 3)
    (hq : g (Away.mk (grading I) ell.2 3 (q : CoordinateRing I)
      (by simpa using q.2)) = 0)
    {E : Type u} [Field E]
    (φ : Away (grading I) (ell : CoordinateRing I) →+* CubicSurfaceFirstJet E)
    (β : B →+* E)
    (hres : cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ = β.comp g) :=
  existsUniqueWithProperty
    (cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernel_globalLift I ell g q hq)
    (fun v hv =>
      cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernelPointFiberDerivative_apply
        I ell g q hq v hv φ β hres)

end PfaffianDescent
