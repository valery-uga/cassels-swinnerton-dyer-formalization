import PfaffianDescent.SurjectiveAffineActualIdealTildeIso
import PfaffianDescent.AffineTildeActualPointClass
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealOpenRestriction
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointRestrictSection

/- SOURCE ONLY / UNVERIFIED. The genuine global conormal object is the
actual pullback of the SAME closed-immersion ideal. Its native affine
restriction and point fiber are derived through actual geometric maps.
No conormal/fiber/ideal comparison certificate is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u

/-- The standard conormal sheaf: actual pullback of the actual ideal module.
Its affine I/I^2 interpretation is a theorem below, not its definition. -/
def actualClosedImmersionConormalModule
    {X Z : Scheme.{u}} (i : Z ⟶ X) : Z.Modules :=
  (Scheme.Modules.pullback i).obj (IdealSheafDataModule.closedImmersionModule i)

def actualClosedPointConormalNativeTensorFiberEquiv
    {R L : Type u} [CommRing R] [Field L] {X : Scheme.{u}}
    (f : Spec (.of R) ⟶ X) [IsOpenImmersion f]
    (rho : R →+* L) (hrho : Function.Surjective rho)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom rho) ≫ f)] :
    letI : Algebra R L := rho.toAlgebra
    (moduleSpecΓFunctor (R := .of L)).obj
      (actualClosedImmersionConormalModule (Spec.map (CommRingCat.ofHom rho) ≫ f)) ≃ₗ[L]
        L ⊗[R] RingHom.ker rho := by
  letI : Algebra R L := rho.toAlgebra
  let j := Spec.map (CommRingCat.ofHom rho)
  letI : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective _ hrho
  let J := IdealSheafDataModule.closedImmersionModule (j ≫ f)
  let e₁ := cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso f j J
  let e₂ := (Scheme.Modules.pullback j).mapIso
    (cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso f j)
  let e₃ := (Scheme.Modules.pullback j).mapIso
    (surjectiveAffineActualIdealTildeIso rho hrho).symm
  exact ((moduleSpecΓFunctor (R := .of L)).mapIso (e₁ ≪≫ e₂ ≪≫ e₃)).toLinearEquiv ≪≫ₗ
    affineTildeActualPointFiberEquiv (CommRingCat.ofHom rho)
      (ModuleCat.of R (RingHom.ker rho))

end PfaffianDescent

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u

def actualClosedPointConormalNativeTensorFiberEquiv_of_factorization
    {R L : Type u} [CommRing R] [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) [IsClosedImmersion q]
    (f : Spec (.of R) ⟶ X) [IsOpenImmersion f]
    (rho : R →+* L) (hrho : Function.Surjective rho)
    (hfac : Spec.map (CommRingCat.ofHom rho) ≫ f = q) :
    letI : Algebra R L := rho.toAlgebra
    (moduleSpecΓFunctor (R := .of L)).obj
      (actualClosedImmersionConormalModule q) ≃ₗ[L]
        L ⊗[R] RingHom.ker rho := by
  letI : Algebra R L := rho.toAlgebra
  let j := Spec.map (CommRingCat.ofHom rho)
  letI : IsClosedImmersion (j ≫ f) := hfac.symm ▸ inferInstanceAs (IsClosedImmersion q)
  let eJ := eqToIso (congrArg IdealSheafDataModule.closedImmersionModule hfac.symm)
  let e := (Scheme.Modules.pullback q).mapIso eJ ≪≫
    (Scheme.Modules.pullbackCongr hfac.symm).app
      (IdealSheafDataModule.closedImmersionModule (j ≫ f))
  exact ((moduleSpecΓFunctor (R := .of L)).mapIso e).toLinearEquiv ≪≫ₗ
    actualClosedPointConormalNativeTensorFiberEquiv f rho hrho

end PfaffianDescent
