import PfaffianDescent.ActualAffineDifferentialTildeToGenuineSheafIso
import PfaffianDescent.ActualAffineGenuineDifferentialForwardTildeComparison

/- The original forward map into the genuine scheme differential fiber
is bijective, using the original tilde adjoint and its actual pullback. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable {k R L : Type u} [CommRing k] [CommRing R] [Field L] [Algebra k R]

lemma actualAffineGenuineDifferentialForwardPointMap_bijective (rho : R →+* L) :
    letI : Algebra R L := rho.toAlgebra
    Function.Bijective (actualAffineGenuineDifferentialForwardPointMap (k := k) rho) := by
  letI : Algebra R L := rho.toAlgebra
  let A := actualAffineDifferentialTildeToGenuineSheaf (k := k) (R := R)
  let P := Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))
  let H := moduleSpecΓFunctor (R := CommRingCat.of L)
  letI : IsIso A := actualAffineDifferentialTildeToGenuineSheaf_isIso (k := k) (R := R)
  have hU : Function.Bijective (H.map (P.map A)) :=
    ConcreteCategory.bijective_of_isIso _
  have hE := (affineTildeActualPointFiberEquiv (CommRingCat.ofHom rho)
    (ModuleCat.of R (KaehlerDifferential k R))).symm.bijective
  rw [actualAffineGenuineDifferentialForwardPointMap_eq_tildePullback (k := k) rho]
  exact hU.comp hE

def actualAffineGenuineDifferentialForwardPointEquiv (rho : R →+* L) :
    letI : Algebra R L := rho.toAlgebra
    (L ⊗[R] KaehlerDifferential k R) ≃ₗ[L]
      (moduleSpecΓFunctor (R := CommRingCat.of L)).obj
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).obj
          (schemeRelativeDifferentials
            (Spec.map (CommRingCat.ofHom (algebraMap k R))))) := by
  letI : Algebra R L := rho.toAlgebra
  exact LinearEquiv.ofBijective
    (actualAffineGenuineDifferentialForwardPointMap (k := k) rho)
    (actualAffineGenuineDifferentialForwardPointMap_bijective (k := k) rho)

end PfaffianDescent
