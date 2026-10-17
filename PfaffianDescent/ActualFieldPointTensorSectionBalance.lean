import PfaffianDescent.ActualFieldGammaSectionLinearEquiv
import PfaffianDescent.SchemeModuleGlobalSections

/- SOURCE ONLY / UNVERIFIED. Tensor pairing on the ACTUAL sheaves of
modules at a field point. Balance is proved from the actual tensor section
construction; no tensor/section comparison certificate is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

def actualFieldPointTensorSection
    {L : Type u} [Field L] (M N : (Spec (.of L)).Modules)
    (s : (moduleSpecΓFunctor (R := .of L)).obj M)
    (t : (moduleSpecΓFunctor (R := .of L)).obj N) :
    (moduleSpecΓFunctor (R := .of L)).obj (schemeModuleTensor M N) :=
  actualFieldGammaSectionLinearEquiv (schemeModuleTensor M N)
    (schemeModuleTensorGlobalSection (𝟙 (Spec (.of L))) M N
      ((actualFieldGammaSectionLinearEquiv M).symm s)
      ((actualFieldGammaSectionLinearEquiv N).symm t))

lemma actualFieldPointTensorSection_smul_first
    {L : Type u} [Field L] (M N : (Spec (.of L)).Modules)
    (c : L) (s : (moduleSpecΓFunctor (R := .of L)).obj M)
    (t : (moduleSpecΓFunctor (R := .of L)).obj N) :
    actualFieldPointTensorSection M N (c • s) t =
      c • actualFieldPointTensorSection M N s t := by
  unfold actualFieldPointTensorSection
  rw [LinearEquiv.map_smul, schemeModuleTensorGlobalSection_smul_first,
    LinearEquiv.map_smul]

lemma actualFieldPointTensorSection_smul_second
    {L : Type u} [Field L] (M N : (Spec (.of L)).Modules)
    (c : L) (s : (moduleSpecΓFunctor (R := .of L)).obj M)
    (t : (moduleSpecΓFunctor (R := .of L)).obj N) :
    actualFieldPointTensorSection M N s (c • t) =
      c • actualFieldPointTensorSection M N s t := by
  unfold actualFieldPointTensorSection
  rw [LinearEquiv.map_smul, schemeModuleTensorGlobalSection_smul_second,
    LinearEquiv.map_smul]

lemma actualFieldPointTensorSection_balance
    {L : Type u} [Field L] (M N : (Spec (.of L)).Modules)
    (c : L) (s : (moduleSpecΓFunctor (R := .of L)).obj M)
    (t : (moduleSpecΓFunctor (R := .of L)).obj N) :
    actualFieldPointTensorSection M N (c • s) t =
      actualFieldPointTensorSection M N s (c • t) := by
  rw [actualFieldPointTensorSection_smul_first, actualFieldPointTensorSection_smul_second]

end PfaffianDescent
