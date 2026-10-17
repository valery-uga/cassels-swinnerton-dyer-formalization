import PfaffianDescent.ActualQuarticPositiveTwoCotangentFiberDimension
import PfaffianDescent.QuarticTraceQuotient
import Mathlib.LinearAlgebra.Dimension.Free

/- SOURCE ONLY / UNVERIFIED. Literal Theta instantiated on the GENUINE
original Omega(2) fiber. Finite dimension is derived from actual smooth
cubic geometry; no dimension/fiber comparison certificate is a premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def actualOriginalPositiveTwoTraceDualEquiv
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (actualCubicPositiveTwoDifferentials p hp))
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    (E2 →ₗ[L] L) ≃ₗ[K] (E2 →ₗ[K] K) := by
  dsimp only
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) P
  let L := (hypersurface p hp).residueField P.1
  let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (actualCubicPositiveTwoDifferentials p hp))
  letI : Module K E2 := Module.compHom E2 (algebraMap K L)
  letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
  have hdim : finrank L E2 = 2 :=
    smoothCubic_originalPositiveTwoDifferentialFiber_finrank_two (K := K) (L := L) p hp hp0
      ((hypersurface p hp).fromSpecResidueField P.1)
      (AllCharacteristics.pointAlgebra_spec (hypersurfaceToBase p hp) P.1).symm
  letI : FiniteDimensional L E2 := FiniteDimensional.of_finrank_pos (by rw [hdim]; decide)
  letI : FiniteDimensional K E2 := Module.Finite.trans L E2
  exact LinearEquiv.ofBijective (QuarticNet.traceQuotientDualMap K L E2)
    (QuarticNet.traceQuotientDualMap_bijective K L E2)

@[simp] theorem actualOriginalPositiveTwoTraceDualEquiv_apply
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    let L := (hypersurface p hp).residueField P.1
    let E2 := (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField P.1)).obj
        (actualCubicPositiveTwoDifferentials p hp))
    letI : Module K E2 := Module.compHom E2 (algebraMap K L)
    letI : IsScalarTower K L E2 := IsScalarTower.of_compHom K L E2
    ∀ f : E2 →ₗ[L] L, ∀ e : E2,
      actualOriginalPositiveTwoTraceDualEquiv p hp hp0 P hP f e =
        Algebra.trace K L (f e) := by
  intros
  rfl

end PfaffianDescent
