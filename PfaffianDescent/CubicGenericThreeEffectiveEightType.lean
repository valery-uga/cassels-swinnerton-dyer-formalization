import AllCharacteristics.VoisinGenericCubicConfiguration
import AllCharacteristics.FiniteSubschemeRank

/-! SOURCE ONLY / UNVERIFIED. Small exact result contract. No chart, Serre
bundle, evaluation, finite-support or desired-cycle certificate is introduced. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Exact cycle result already displayed at the end of the native inner
factory, abstracted over its original coefficient field and cubic. -/
def CubicGenericThreeEffectiveEightType
    {F : Type u} [Field F]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) : Prop :=
  ∃ hB : IsIntegral (cubicConfigurationBase P hP 3),
    letI := hB
    ∃ (a : CommRingCat.of F ⟶ CommRingCat.of (cubicConfigurationBase P hP 3).functionField)
      (ha : Spec.map a = cubicConfigurationGenericBaseMap P hP 3 ≫
        cubicConfigurationToBase P hP 3),
      ∃ z : EffectiveZeroCycle (hypersurface (P.map a.hom) (hP.map a.hom)),
        EffectiveZeroCycle.degree (hypersurfaceToBase (P.map a.hom) (hP.map a.hom)) z = 8

end PfaffianDescent
