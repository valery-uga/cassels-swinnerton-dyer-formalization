import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridComponentVector
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridKernelScalarExtension
import AllCharacteristics.HomogeneousSpecialization

/-! Literal coordinate transport of native cubic kernel members to ordered
normalized vectors, including arbitrary homogeneous normalization. -/
noncomputable section
open MvPolynomial AlgebraicGeometry
open AllCharacteristics
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem voisinDegreeTenSelectedAvoidance_homogeneous_zero_of_normalizedRatios
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (q : MvPolynomial (Fin 4) K) {d : ℕ} (hq : q.IsHomogeneous d)
    (x y : Fin 4 → L) (j : Fin 4) (hxj : x j = 1)
    (hratios : ∀ i, (y j)⁻¹ * y i = (x j)⁻¹ * x i)
    (hzero : q.eval₂ (algebraMap K L) y = 0) :
    q.eval₂ (algebraMap K L) x = 0 := by
  have hx : x = (y j)⁻¹ • y := by
    funext i
    simpa only [hxj, inv_one, one_mul, Pi.smul_apply, smul_eq_mul] using
      (hratios i).symm
  rw [hx, eval₂_homogeneous_smul q hq, hzero, mul_zero]

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_nativeCubicKernel_eval_component
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (φ : A →ₐ[K] L) (x : Fin 4 → A)
    (q : homogeneousSubmodule (Fin 4) K 3)
    (hq : q ∈ LinearMap.ker (homogeneousSectionRestriction x 3)) :
    q.1.eval₂ (algebraMap K L) (fun i => φ (x i)) = 0 := by
  have hzero : q.1.eval₂ (algebraMap K A) x = 0 := by
    exact LinearMap.mem_ker.mp hq
  have heval := MvPolynomial.hom_eval₂ q.1 (algebraMap K A) φ.toRingHom x
  have hcomp : φ.toRingHom.comp (algebraMap K A) = algebraMap K L := by
    ext a
    exact φ.commutes a
  rw [hcomp] at heval
  change q.1.eval₂ (algebraMap K L) (fun i => φ.toRingHom (x i)) = 0
  rw [← heval, hzero, map_zero]

end PfaffianDescent
