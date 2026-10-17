import PfaffianDescent.ActualAffineGlobalConormalNativeSection
import Mathlib.LinearAlgebra.TensorProduct.Basic

/- SOURCE ONLY / UNVERIFIED. Full actual GLOBAL-to-AFFINE fiber-map
comparison. Actual native ideal sections span the true tensor fiber, so
adjunction's generator identity determines the whole L-linear map. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule
open scoped TensorProduct
universe u
variable {k R L : Type u} [CommRing k] [CommRing R] [Field L] [Algebra k R]

lemma actualAffineGlobalConormalDifferentialFiberComparison
    (rho : R →+* L) (hrho : Function.Surjective rho) :
    letI : Algebra R L := rho.toAlgebra
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
      IsClosedImmersion.spec_of_surjective _ hrho
    ((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap
        (Spec.map (CommRingCat.ofHom (algebraMap k R)))
        (Spec.map (CommRingCat.ofHom rho)))).hom =
      actualAffineConormalDifferentialFiberMap (k := k) rho hrho := by
  dsimp only
  letI : Algebra R L := rho.toAlgebra
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
    IsClosedImmersion.spec_of_surjective _ hrho
  let E := actualAffineConormalTensorEquiv rho hrho
  let D := ((moduleSpecΓFunctor (R := .of L)).map
    (actualGlobalClosedConormalDifferentialMap
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (Spec.map (CommRingCat.ofHom rho)))).hom
  let F := actualAffineConormalDifferentialFiberMap (k := k) rho hrho
  have h : ∀ t : L ⊗[R] RingHom.ker rho, D (E.symm t) = F (E.symm t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x =>
      have he : E.symm ((1 : L) ⊗ₜ[R] x) =
          actualModulePointSectionClass (Spec.map (CommRingCat.ofHom rho))
            (closedImmersionModule (Spec.map (CommRingCat.ofHom rho)))
            (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x) := by
        apply E.injective
        rw [E.apply_symm_apply, actualAffineConormalTensorEquiv_nativeSection]
      have ht : a ⊗ₜ[R] x = a • ((1 : L) ⊗ₜ[R] x) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, E.symm.map_smul, D.map_smul, F.map_smul, he]
      exact congrArg (fun z => a • z)
        (actualAffineGlobalConormalDifferentialMap_nativeSection (k := k) rho hrho x)
    | add t s ht hs =>
      simp only [map_add, ht, hs]
  apply LinearMap.ext
  intro z
  simpa only [E.symm_apply_apply] using h (E z)

end PfaffianDescent
