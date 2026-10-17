import PfaffianDescent.ActualP3IdealGlobalRestrictionKernel
import PfaffianDescent.P3HomogeneousGlobalSectionsLinear
import PfaffianDescent.LinearKernelPrecomposeEquiv

/-! SOURCE ONLY / UNVERIFIED. The genuine arbitrary closed immersion and
its actual tensor ideal are identified with a homogeneous-polynomial kernel
of their actual sheaf restriction. This does NOT yet identify that kernel
with the separately defined intrinsic four-chart quadratic submodule. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Polynomial restriction is the composite of the internally constructed
ambient global-section map and the actual twisted ideal quotient map. -/
def p3ClosedImmersionHomogeneousRestrictionLinearMap
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    [IsClosedImmersion i] (m : ℕ) :=
  (schemeModuleGlobalSectionsMap (ambientToBase (R := K) (σ := Fin 4))
    (p3ClosedImmersionPositiveRestriction i m)).comp
      (p3HomogeneousGlobalSectionLinearMap K m)

/-- Actual H0(I_Z(m)), for arbitrary closed Z, as its genuine polynomial
restriction kernel. Tensor exactness and ambient global equivalence are both
derived internally; neither is a certificate input. Nilpotents are retained. -/
def p3ClosedImmersionIdealHomogeneousKernelEquiv
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    [IsClosedImmersion i] (m : ℕ) (hm : 0 < m) :
    SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (MvPolynomial.homogeneousSubmodule (Fin 4) K) m)) ≃ₗ[K]
      (p3ClosedImmersionHomogeneousRestrictionLinearMap i m).ker :=
  (p3ClosedImmersionPositiveIdealGlobalKernelEquiv i m hm).trans
    (linearKernelPrecomposeEquiv (p3HomogeneousGlobalSectionsLinearEquiv K m hm)
      (schemeModuleGlobalSectionsMap (ambientToBase (R := K) (σ := Fin 4))
        (p3ClosedImmersionPositiveRestriction i m)))

end PfaffianDescent
