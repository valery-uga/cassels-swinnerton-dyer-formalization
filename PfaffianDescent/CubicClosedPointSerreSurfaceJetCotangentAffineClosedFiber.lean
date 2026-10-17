import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentAffineClosedImmersion

noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace PfaffianDescent
universe u
variable {A K : Type u} [CommRing A] [Field K]
set_option backward.isDefEq.respectTransparency false

/-- Global sections of the ACTUAL point pullback of the ACTUAL affine
closed ideal are the scalar extension of its literal actual kernel H.
No flatness of the point map and no quotient-source presentation is supplied. -/
def cubicClosedPointSerreSurfaceJetCotangent_affineClosedFiberSectionsEquiv
    {Z : Scheme.{u}} (i : Z ⟶ Spec (CommRingCat.of A)) [IsClosedImmersion i]
    (r : A →+* K) :
    letI : Algebra A K := r.toAlgebra
    (moduleSpecΓFunctor (R := CommRingCat.of K)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom r))).obj
        (IdealSheafDataModule.closedImmersionModule i)) ≃ₗ[K]
      K ⊗[A] RingHom.ker
        (cubicClosedPointSerreSurfaceJetCotangent_affineClosedImmersionRingMap i) := by
  letI : Algebra A K := r.toAlgebra
  exact ((moduleSpecΓFunctor (R := CommRingCat.of K)).mapIso
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom r))).mapIso
        (cubicClosedPointSerreSurfaceJetCotangent_affineClosedImmersionTildeIso i))).toLinearEquiv ≪≫ₗ
    cubicClosedPointSerreSurfaceJetCotangent_fiberSectionsEquiv r _

end PfaffianDescent
