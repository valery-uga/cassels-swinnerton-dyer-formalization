import PfaffianDescent.ActualAffineConormalNativeSectionClass
import PfaffianDescent.ActualAffineDifferentialPointUniversalDerivation
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Kaehler.Basic

/-! SOURCE ONLY / UNVERIFIED. The actual affine conormal point fiber maps
L-linearly to the genuinely sheafified differential point fiber. Its action
on actual ideal sections is the actual pulled-back universal differential,
with both section/evaluation comparisons derived upstream. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open IdealSheafDataModule
open scoped TensorProduct
universe u
variable {k R L : Type u} [CommRing k] [CommRing R] [Field L] [Algebra k R]

def actualAffineConormalDifferentialFiberMap
    (rho : R →+* L) (hrho : Function.Surjective rho) :
    letI : Algebra R L := rho.toAlgebra
    (moduleSpecΓFunctor (R := .of L)).obj
        (actualClosedImmersionConormalModule (Spec.map (CommRingCat.ofHom rho))) →ₗ[L]
      (moduleSpecΓFunctor (R := .of L)).obj
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).obj
          (schemeRelativeDifferentials
            (Spec.map (CommRingCat.ofHom (algebraMap k R))))) := by
  letI : Algebra R L := rho.toAlgebra
  exact (actualAffineSchemeDifferentialPointFiberEquiv (k := k) rho).symm.toLinearMap.comp
    ((LinearMap.liftBaseChange L (KaehlerDifferential.kerToTensor k R L)).comp
      (actualAffineConormalTensorEquiv rho hrho).toLinearMap)

theorem actualAffineConormalDifferentialFiberMap_nativeSection
    (rho : R →+* L) (hrho : Function.Surjective rho) (x : RingHom.ker rho) :
    letI : Algebra R L := rho.toAlgebra
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
      IsClosedImmersion.spec_of_surjective _ hrho
    actualAffineConormalDifferentialFiberMap (k := k) rho hrho
      (actualModulePointSectionClass (Spec.map (CommRingCat.ofHom rho))
        (closedImmersionModule (Spec.map (CommRingCat.ofHom rho)))
        (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x)) =
      actualAffineDifferentialPointClass (k := k) rho x.1 := by
  dsimp only
  letI : Algebra R L := rho.toAlgebra
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
    IsClosedImmersion.spec_of_surjective _ hrho
  let E := actualAffineSchemeDifferentialPointFiberEquiv (k := k) rho
  let T := actualAffineConormalTensorEquiv rho hrho
  let b := LinearMap.liftBaseChange L (KaehlerDifferential.kerToTensor k R L)
  let z := actualModulePointSectionClass (Spec.map (CommRingCat.ofHom rho))
    (closedImmersionModule (Spec.map (CommRingCat.ofHom rho)))
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x)
  have ht := actualAffineConormalTensorEquiv_nativeSection rho hrho x
  have hb : b ((1 : L) ⊗ₜ[R] x) =
      (1 : L) ⊗ₜ[R] KaehlerDifferential.D k R x.1 :=
    LinearMap.liftBaseChange_one_tmul L (KaehlerDifferential.kerToTensor k R L) x
  have hp := actualAffineDifferentialPointFiberEquiv_pointClass (k := k) rho x.1
  have hv : b (T z) = E (actualAffineDifferentialPointClass (k := k) rho x.1) :=
    (congrArg (fun t => b t) ht).trans (hb.trans hp.symm)
  calc
    actualAffineConormalDifferentialFiberMap (k := k) rho hrho z =
        E.symm (b (T z)) := rfl
    _ = E.symm (E (actualAffineDifferentialPointClass (k := k) rho x.1)) :=
      congrArg (fun t => E.symm t) hv
    _ = actualAffineDifferentialPointClass (k := k) rho x.1 :=
      E.symm_apply_apply _

theorem actualAffineConormalDifferentialFiberMap_actualUniversalSection
    (rho : R →+* L) (hrho : Function.Surjective rho) (x : RingHom.ker rho) :
    letI : Algebra R L := rho.toAlgebra
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
      IsClosedImmersion.spec_of_surjective _ hrho
    actualAffineConormalDifferentialFiberMap (k := k) rho hrho
      (actualModulePointSectionClass (Spec.map (CommRingCat.ofHom rho))
        (closedImmersionModule (Spec.map (CommRingCat.ofHom rho)))
        (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x)) =
      actualAffineSheafPointClass (CommRingCat.ofHom rho)
        (schemeRelativeDifferentials (Spec.map (CommRingCat.ofHom (algebraMap k R))))
        (actualRelativeDifferentialSection
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤
          (algebraMap R Γ(Spec (.of R), ⊤) x.1)) := by
  dsimp only
  letI : Algebra R L := rho.toAlgebra
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
    IsClosedImmersion.spec_of_surjective _ hrho
  exact (actualAffineConormalDifferentialFiberMap_nativeSection (k := k) rho hrho x).trans
    (actualAffineDifferentialPointClass_eq_actualPullbackD (k := k) rho x.1)

end PfaffianDescent
