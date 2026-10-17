import PfaffianDescent.ActualGlobalClosedConormalDifferentialMap
import PfaffianDescent.ActualPositiveTwistPullbackTensorIso

/- SOURCE ONLY / UNVERIFIED. Actual globally constructed conormal/Omega
map twisted by the GENUINE positive twist. Pullback tensor comparisons are
internally invertible via actual Proj chart generators, not input certificates. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def actualGlobalPositiveTwistConormalDifferentialMap
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (q : Z ⟶ scheme I) [IsClosedImmersion q] (m : ℕ) :
    (Scheme.Modules.pullback q).obj
      (closedImmersionIdealTwist q (positiveSheafOfModules (grading I) m)) ⟶
    (Scheme.Modules.pullback q).obj
      (schemeModuleTensor (schemeRelativeDifferentials (toBase I))
        (positiveSheafOfModules (grading I) m)) :=
  (actualPositiveTwistPullbackTensorIso I q (closedImmersionModule q) m).hom ≫
    schemeModuleTensorMap (actualGlobalClosedConormalDifferentialMap (toBase I) q)
      (𝟙 ((Scheme.Modules.pullback q).obj (positiveSheafOfModules (grading I) m))) ≫
    (actualPositiveTwistPullbackTensorIso I q (schemeRelativeDifferentials (toBase I)) m).inv

end PfaffianDescent
