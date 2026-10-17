import PfaffianDescent.PointGlobalTraceP3BasisKoszul
import PfaffianDescent.AmbientPointKoszulBiproductStalk

/-! # Actual stalk coordinates for arbitrary degree-one Koszul equations

The native negative-twist stalks are trivialized by any chosen degree-one
form which is a unit at the point. Actual multiplication becomes the
normalized local equation in the homogeneous local ring.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K
variable (f : Fin 4 → homogeneousSubmodule (Fin 4) K 1)

local instance pointGlobalTraceP3Basis_stalkPointIdeal_prime (x : Proj PS) :
    (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x

/-- Actual categorical negative-twist stalks in a chosen coordinate chart. -/
def pointGlobalTraceP3Basis_stalkCoordinate
    (j : Fin 4) (x : Proj PS) (hx : (f j).val ∈ (pointIdeal PS x).primeCompl) (m : ℕ) :
    (↑((schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS m)) : Type u) ≃+
      AtPrime PS (pointIdeal PS x) := by
  letI : (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x
  exact (stalkAddEquivFractionModule PS m x).trans
    (localTrivialization PS (pointIdeal PS x) (f j) hx m).toAddEquiv.symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual categorical degree-one multiplication stalk map becomes
multiplication by `fi/fj` in the homogeneous local ring. -/
theorem pointGlobalTraceP3Basis_stalkCoordinate_mul
    (i j : Fin 4) (x : Proj PS) (hx : (f j).val ∈ (pointIdeal PS x).primeCompl) (m : ℕ)
    (z : (schemeModuleStalkFunctor (Proj PS) x).obj (sheafOfModules PS (m + 1))) :
    pointGlobalTraceP3Basis_stalkCoordinate K f j x hx m
        ((schemeModuleStalkFunctor (Proj PS) x).map (pointGlobalTraceP3BasisMul K f i m) z) =
      localEquation PS (pointIdeal PS x) (f i)
        (f j) hx *
          pointGlobalTraceP3Basis_stalkCoordinate K f j x hx (m + 1) z := by
  letI : (pointIdeal PS x).IsPrime := ProjectiveSpectrum.isPrime x
  let t := localTrivialization PS (pointIdeal PS x) (f j) hx
  change (t m).symm
      (stalkToFractionModule PS m x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (mulHomogeneousPresheaf PS (f i) m) z)) =
    localEquation PS (pointIdeal PS x) (f i)
      (f j) hx *
        (t (m + 1)).symm (stalkToFractionModule PS (m + 1) x z)
  rw [stalkToFractionModule_stalkMap]
  rw [← (t (m + 1)).apply_symm_apply (stalkToFractionModule PS (m + 1) x z)]
  rw [mulHomogeneousStalk_localTrivialization_apply]
  dsimp only [t]
  simp only [LinearEquiv.symm_apply_apply]

end PfaffianDescent.ProjectiveNegativeTwist
