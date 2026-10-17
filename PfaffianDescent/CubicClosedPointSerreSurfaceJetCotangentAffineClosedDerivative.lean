import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentAffineClosedFiber
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentTensor

noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace PfaffianDescent
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
set_option backward.isDefEq.respectTransparency false

/-- Native derivative on actual Gamma of the point pullback of an actual affine closed ideal.
Its H is the literal kernel of the actual immersion's coordinate-ring map. -/
def cubicClosedPointSerreSurfaceJetCotangent_affineClosedFiberDerivative
    (φ : A →ₐ[K] CubicSurfaceFirstJet K)
    {Z : Scheme.{u}} (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i]
    (hH : RingHom.ker
      (cubicClosedPointSerreSurfaceJetCotangent_affineClosedImmersionRingMap i) ≤
      cubicClosedPointSerreSurfaceJetCotangent_ideal φ) :
    (moduleSpecΓFunctor (R := CommRingCat.of K)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
        (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom))).obj
        (IdealSheafDataModule.closedImmersionModule i)) →ₗ[K] (Fin 2 → K) := by
  let r := (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom
  letI : Algebra A K := r.toAlgebra
  exact (cubicClosedPointSerreSurfaceJetCotangent_idealTensorDerivative φ _ hH).comp
    (cubicClosedPointSerreSurfaceJetCotangent_affineClosedFiberSectionsEquiv i r).toLinearMap

/-- Exact scalar formula on the actual native fibre coordinate, retaining H. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_affineClosedFiberDerivative_tmul
    (φ : A →ₐ[K] CubicSurfaceFirstJet K)
    {Z : Scheme.{u}} (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i]
    (hH : RingHom.ker
      (cubicClosedPointSerreSurfaceJetCotangent_affineClosedImmersionRingMap i) ≤
      cubicClosedPointSerreSurfaceJetCotangent_ideal φ)
    (c : K) (a : RingHom.ker
      (cubicClosedPointSerreSurfaceJetCotangent_affineClosedImmersionRingMap i)) :
    let r := (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom
    letI : Algebra A K := r.toAlgebra
    cubicClosedPointSerreSurfaceJetCotangent_affineClosedFiberDerivative φ i hH
      ((cubicClosedPointSerreSurfaceJetCotangent_affineClosedFiberSectionsEquiv i r).symm
        (c ⊗ₜ[A] a)) = c • (φ a.1).snd := by
  let r := (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom
  letI : Algebra A K := r.toAlgebra
  change cubicClosedPointSerreSurfaceJetCotangent_idealTensorDerivative φ _ hH
    ((cubicClosedPointSerreSurfaceJetCotangent_affineClosedFiberSectionsEquiv i r)
      ((cubicClosedPointSerreSurfaceJetCotangent_affineClosedFiberSectionsEquiv i r).symm
        (c ⊗ₜ[A] a))) = _
  rw [LinearEquiv.apply_symm_apply,
    cubicClosedPointSerreSurfaceJetCotangent_idealTensorDerivative_tmul]

end PfaffianDescent
