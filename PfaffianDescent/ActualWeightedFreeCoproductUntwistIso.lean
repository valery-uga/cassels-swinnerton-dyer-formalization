import PfaffianDescent.GeneralP3UntwistPairing
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Untwist the SAME actual finite weighted positive term. Exactness of
its tensor functor follows from the already constructed P3 inverse-twist
equivalence, while the new all-degree multiplication gives every native
negative summand. No isomorphism or functor-exactness premise is supplied. -/
def p3WeightedFreeCoproductUntwistIso
    (K : Type u) [Field K] {ι : Type u} [Fintype ι]
    (B : ℕ) (d : ι → ℕ) (hd : ∀ i, d i ≤ B) :
    schemeModuleTensor
      (∐ fun i => positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) (B - d i))
      (sheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) B) ≅
      (∐ fun i => sheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) (d i)) := by
  let PS := MvPolynomial.homogeneousSubmodule (Fin 4) K
  let F := schemeModuleTensorRight (sheafOfModules PS B)
  letI : PreservesFiniteColimits F := by
    change PreservesFiniteColimits (p3TwistTensorRightEquivalence K B).functor
    infer_instance
  exact PreservesCoproduct.iso F
      (fun i => positiveSheafOfModules PS (B - d i)) ≪≫
    Sigma.mapIso (fun i => p3WeightedFreeTermUntwistIso K B (d i) (hd i))

end PfaffianDescent.ProjectiveNegativeTwist
