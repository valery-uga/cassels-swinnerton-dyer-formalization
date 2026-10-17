import PfaffianDescent.ActualAffineDifferentialTildeToGenuineSheafIso

/- SOURCE ONLY / UNVERIFIED. The actual sheaf point fiber of the SAME
actual affine scheme agrees with the literal Kähler scalar extension. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable {k R L : Type u} [CommRing k] [CommRing R] [CommRing L] [Algebra k R]

/-- No sheaf-comparison or fiber certificate is supplied. -/
def actualAffineSchemeDifferentialPointFiberEquiv (rho : R →+* L) :
    letI : Algebra R L := rho.toAlgebra
    (moduleSpecΓFunctor (R := CommRingCat.of L)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).obj
        (schemeRelativeDifferentials
          (Spec.map (CommRingCat.ofHom (algebraMap k R))))) ≃ₗ[L]
      L ⊗[R] KaehlerDifferential k R := by
  letI : Algebra R L := rho.toAlgebra
  let A := actualAffineDifferentialTildeToGenuineSheaf (k := k) (R := R)
  letI : IsIso A := actualAffineDifferentialTildeToGenuineSheaf_isIso (k := k) (R := R)
  let e := (moduleSpecΓFunctor (R := CommRingCat.of L)).mapIso
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).mapIso (asIso A))
  exact e.toLinearEquiv.symm ≪≫ₗ affineTildeActualPointFiberEquiv
    (CommRingCat.ofHom rho) (ModuleCat.of R (KaehlerDifferential k R))

end PfaffianDescent
