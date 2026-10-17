import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangent
import PfaffianDescent.AffineGammaPushforward

/-! The actual affine point pullback of an ideal sheaf has the literal
scalar-extension module as its global sections. No flatness is needed. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace PfaffianDescent
universe u
variable {A K : Type u} [CommRing A] [Field K]

/-- This comparison applies to the actual point pullback, even though the
pulled-back ideal inclusion need not be injective. -/
def cubicClosedPointSerreSurfaceJetCotangent_fiberSectionsEquiv
    (g : A →+* K) (I : Ideal A) :
    letI : Algebra A K := g.toAlgebra
    (moduleSpecΓFunctor (R := CommRingCat.of K)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).obj
        ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A I))) ≃ₗ[K]
      K ⊗[A] I := by
  letI : Algebra A K := g.toAlgebra
  exact ((moduleSpecΓFunctor (R := CommRingCat.of K)).mapIso
      (affineIdealTildePullbackIso g I)).toLinearEquiv ≪≫ₗ
    ((tilde.toTildeΓNatIso (R := CommRingCat.of K)).app
      (ModuleCat.of K (K ⊗[A] I))).toLinearEquiv.symm

/-- The source is the actual ideal module of the affine closed immersion,
rather than an externally supplied tilde identification. -/
def cubicClosedPointSerreSurfaceJetCotangent_closedIdealFiberSectionsEquiv
    (g : A →+* K) (I : Ideal A) :
    letI : Algebra A K := g.toAlgebra
    (moduleSpecΓFunctor (R := CommRingCat.of K)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).obj
        (IdealSheafDataModule.closedImmersionModule
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) ≃ₗ[K]
      K ⊗[A] I := by
  letI : Algebra A K := g.toAlgebra
  exact ((moduleSpecΓFunctor (R := CommRingCat.of K)).mapIso
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).mapIso
        (affineQuotientIdealTildeClosedImmersionModuleIso I).symm)).toLinearEquiv ≪≫ₗ
    cubicClosedPointSerreSurfaceJetCotangent_fiberSectionsEquiv g I

end PfaffianDescent
