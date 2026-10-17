import PfaffianDescent.RelativeIdealPushoutInjection
import PfaffianDescent.AffineIdealPullbackMonoOfTensorInjective

/-!
# Relative-flat affine ideal pullback

Combine the pushout exactness calculation with the affine sheaf comparison.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false in
/-- The actual affine ideal sheaf stays embedded under an arbitrary
parameter change whenever its quotient is flat over the parameters. -/
theorem affineQuotientIdealModulePullback_mono_of_quotient_flat_pushout
    {R S A B : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B]
    [Algebra S B] [IsScalarTower R S B]
    (g : A →+* B) (I : Ideal A)
    (hTower : letI : Algebra A B := g.toAlgebra
      IsScalarTower R A B)
    (hPushout : letI : Algebra A B := g.toAlgebra
      Algebra.IsPushout R S A B)
    [Module.Flat R (A ⧸ I)] :
    Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) := by
  apply affineQuotientIdealModulePullback_mono_of_tensor_injective g I
  exact idealBaseChangeLinearMap_injective_of_quotient_flat_pushout
    g I hTower hPushout

end PfaffianDescent
