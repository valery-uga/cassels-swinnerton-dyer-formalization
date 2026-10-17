import PfaffianDescent.ActualAffineModulePointSectionEvaluation
import PfaffianDescent.SurjectiveResidueTensorConormal
import PfaffianDescent.ActualClosedPointConormalNativeTensorFiber
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernelSectionHom

/- SOURCE ONLY / UNVERIFIED. The ACTUAL affine conormal section under
its genuine point-pullback and ideal-sheaf comparison is the SAME x mod I².
No fiber equality or derivative comparison certificate is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open IdealSheafDataModule
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u

def actualAffineConormalTensorEquiv
    {R L : Type u} [CommRing R] [Field L]
    (rho : R →+* L) (hrho : Function.Surjective rho) :
    letI : Algebra R L := rho.toAlgebra
    (moduleSpecΓFunctor (R := .of L)).obj
      (actualClosedImmersionConormalModule (Spec.map (CommRingCat.ofHom rho))) ≃ₗ[L]
        L ⊗[R] RingHom.ker rho := by
  letI : Algebra R L := rho.toAlgebra
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
    IsClosedImmersion.spec_of_surjective _ hrho
  exact cubicClosedPointSerreSurfaceJetCotangent_nativeIdealFiberSectionsEquiv rho rho

lemma actualAffineConormalTensorEquiv_eq_native
    {R L : Type u} [CommRing R] [Field L]
    (rho : R →+* L) (hrho : Function.Surjective rho) :
    letI : Algebra R L := rho.toAlgebra
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
      IsClosedImmersion.spec_of_surjective _ hrho
    actualAffineConormalTensorEquiv rho hrho =
      cubicClosedPointSerreSurfaceJetCotangent_nativeIdealFiberSectionsEquiv rho rho := by
  dsimp only
  letI : Algebra R L := rho.toAlgebra
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
    IsClosedImmersion.spec_of_surjective _ hrho
  rfl

lemma actualAffineConormalTensorEquiv_nativeSection
    {R L : Type u} [CommRing R] [Field L]
    (rho : R →+* L) (hrho : Function.Surjective rho) (x : RingHom.ker rho) :
    letI : Algebra R L := rho.toAlgebra
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
      IsClosedImmersion.spec_of_surjective _ hrho
    actualAffineConormalTensorEquiv rho hrho
      (actualModulePointSectionClass (Spec.map (CommRingCat.ofHom rho))
        (closedImmersionModule (Spec.map (CommRingCat.ofHom rho)))
        (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x)) =
      (1 : L) ⊗ₜ[R] x := by
  dsimp only
  letI : Algebra R L := rho.toAlgebra
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
    IsClosedImmersion.spec_of_surjective _ hrho
  let q := Spec.map (CommRingCat.ofHom rho)
  let M : (Spec (.of R)).Modules := closedImmersionModule q
  let G := moduleSpecΓFunctor (R := CommRingCat.of R)
  let N := (moduleSpecΓFunctor (R := CommRingCat.of L)).obj
    ((Scheme.Modules.pullback q).obj M)
  let z : G.obj M :=
    cubicClosedPointSerreSurfaceJetCotangent_nativeIdealGlobalSectionsEquiv rho x
  let s : schemeModuleUnit (Spec (.of R)) ⟶ M :=
    cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x
  let v : G.obj M ⟶ (ModuleCat.restrictScalars rho).obj N :=
    cubicClosedPointSerreSurfaceJetCotangent_affineModulePointEvaluation
      (CommRingCat.ofHom rho) M
  let E : N ≃ₗ[L] L ⊗[R] RingHom.ker rho :=
    cubicClosedPointSerreSurfaceJetCotangent_nativeIdealFiberSectionsEquiv rho rho
  have htop : s.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤)) = z :=
    cubicClosedPointSerreSurfaceJetCotangent_sectionHomOfTop_one M z
  have hclass : actualModulePointSectionClass q M s =
      v.hom (s.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤))) :=
    actualAffineModulePointSectionClass_eq_evaluation rho M s
  have hvalue : E (v.hom (s.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤)))) =
      E (v.hom z) :=
    congrArg (fun a : G.obj M => E (v.hom a)) htop
  have hnative : E (v.hom z) = (1 : L) ⊗ₜ[R] x :=
    cubicClosedPointSerreSurfaceJetCotangent_nativeIdealPointEvaluation_apply rho rho x
  change E (actualModulePointSectionClass q M s) = (1 : L) ⊗ₜ[R] x
  exact (congrArg (fun a : N => E a) hclass).trans (hvalue.trans hnative)

lemma actualAffineConormalClass_nativeSection
    {R L : Type u} [CommRing R] [Field L]
    (rho : R →+* L) (hrho : Function.Surjective rho) (x : RingHom.ker rho) :
    letI : Algebra R L := rho.toAlgebra
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
      IsClosedImmersion.spec_of_surjective _ hrho
    surjectiveResidueTensorConormalEquiv rho hrho
      (actualAffineConormalTensorEquiv rho hrho
        (actualModulePointSectionClass (Spec.map (CommRingCat.ofHom rho))
          (closedImmersionModule (Spec.map (CommRingCat.ofHom rho)))
          (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x))) =
      (RingHom.ker rho).toCotangent x := by
  dsimp only
  letI : Algebra R L := rho.toAlgebra
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
    IsClosedImmersion.spec_of_surjective _ hrho
  rw [actualAffineConormalTensorEquiv_nativeSection]
  exact surjectiveResidueTensorConormalEquiv_one_tmul rho hrho x

end PfaffianDescent
