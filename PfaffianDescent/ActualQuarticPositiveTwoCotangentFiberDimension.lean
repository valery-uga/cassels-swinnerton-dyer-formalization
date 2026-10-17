import PfaffianDescent.ActualCubicPositiveTwoDifferentialPointFiber
import AllCharacteristics.ClosedPointAlgebra
import Mathlib.LinearAlgebra.Dimension.Free

/- SOURCE ONLY / UNVERIFIED. Literal degree-four original-P dimension:
actual Omega(2) fiber has L-dimension 2 and ground dimension 8. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem smoothCubic_originalQuarticPositiveTwoDifferentialFiber_finrank_eight
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (h4 : (hypersurfaceToBase p hp).residueDegree x.1 = 4) :
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) x.1
    letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) x
    let L := (hypersurface p hp).residueField x.1
    let F := (moduleSpecΓFunctor (R := CommRingCat.of L)).obj
      ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField x.1)).obj
        (actualCubicPositiveTwoDifferentials p hp))
    letI : Module K F := Module.compHom F (algebraMap K L)
    Module.finrank K F = 8 := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) x.1
  letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) x
  let L := (hypersurface p hp).residueField x.1
  let F := (moduleSpecΓFunctor (R := CommRingCat.of L)).obj
    ((Scheme.Modules.pullback ((hypersurface p hp).fromSpecResidueField x.1)).obj
      (actualCubicPositiveTwoDifferentials p hp))
  letI : Module K F := Module.compHom F (algebraMap K L)
  letI : IsScalarTower K L F := IsScalarTower.of_compHom (A := L) K F
  have hL : Module.finrank K L = 4 :=
    (AllCharacteristics.closedPoint_finrank_eq_residueDegree
      (hypersurfaceToBase p hp) x).trans h4
  have hF : Module.finrank L F = 2 :=
    smoothCubic_originalPositiveTwoDifferentialFiber_finrank_two (K := K) (L := L) p hp hp0
      ((hypersurface p hp).fromSpecResidueField x.1)
      (AllCharacteristics.pointAlgebra_spec (hypersurfaceToBase p hp) x.1).symm
  have h := Module.finrank_mul_finrank K L F
  rw [hL, hF] at h
  exact h.symm

end PfaffianDescent
