import PfaffianDescent.AffineGammaPushforward
import Mathlib.RingTheory.Kaehler.Basic

/- SOURCE ONLY / UNVERIFIED. An actual affine module sheaf and actual
point pullback; this leaf does not assert a global scheme Omega comparison. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable {k R L : Type u} [CommRing k] [CommRing R] [CommRing L] [Algebra k R]

def affineKaehlerModuleSheaf : (Spec (CommRingCat.of R)).Modules :=
  (tilde.functor (CommRingCat.of R)).obj
    (ModuleCat.of R (KaehlerDifferential k R))

/-- Global sections of the genuine point pullback of the affine differential
module sheaf are the literal Kaehler fiber. No flatness of the point is assumed. -/
def affineKaehlerSheafPointFiberEquiv (rho : R →+* L) :
    letI : Algebra R L := rho.toAlgebra
    (moduleSpecΓFunctor (R := CommRingCat.of L)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).obj
        (affineKaehlerModuleSheaf (k := k) (R := R))) ≃ₗ[L]
      L ⊗[R] KaehlerDifferential k R := by
  letI : Algebra R L := rho.toAlgebra
  exact ((moduleSpecΓFunctor (R := CommRingCat.of L)).mapIso
      ((affineTildePullbackNatIso (CommRingCat.ofHom rho)).app
        (ModuleCat.of R (KaehlerDifferential k R)))).toLinearEquiv ≪≫ₗ
    ((tilde.toTildeΓNatIso (R := CommRingCat.of L)).app
      (ModuleCat.of L (L ⊗[R] KaehlerDifferential k R))).toLinearEquiv.symm

end PfaffianDescent
