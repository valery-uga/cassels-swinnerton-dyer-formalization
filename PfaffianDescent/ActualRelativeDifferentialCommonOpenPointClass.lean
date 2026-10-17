import PfaffianDescent.ActualModuleOpenPointSectionClass
import PfaffianDescent.ActualRelativeDifferentialSectionLeibniz

/- SOURCE ONLY / UNVERIFIED. Leibniz in the GENUINE global differential
point fiber, evaluated through the literal SAME common open. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

def actualRelativeDifferentialCommonOpenPointClass
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of K)) (U : X.Opens)
    (q : Spec (.of L) ⟶ (U : Scheme)) (a : Γ(X, U)) :
    (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback (q ≫ U.ι)).obj (schemeRelativeDifferentials g)) :=
  actualModuleOpenPointSectionClass g U q (schemeRelativeDifferentials g)
    (actualRelativeDifferentialSection g U a)

lemma actualRelativeDifferentialCommonOpenPointClass_mul
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of K)) (U : X.Opens)
    (q : Spec (.of L) ⟶ (U : Scheme)) (a r : Γ(X, U)) :
    actualRelativeDifferentialCommonOpenPointClass g U q (a * r) =
      actualOpenPointResidue U q a • actualRelativeDifferentialCommonOpenPointClass g U q r +
      actualOpenPointResidue U q r • actualRelativeDifferentialCommonOpenPointClass g U q a := by
  unfold actualRelativeDifferentialCommonOpenPointClass
  rw [actualRelativeDifferentialSection_leibniz, map_add,
    actualModuleOpenPointSectionClass_smul, actualModuleOpenPointSectionClass_smul]

lemma actualRelativeDifferentialCommonOpenPointClass_mul_of_residue_zero
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of K)) (U : X.Opens)
    (q : Spec (.of L) ⟶ (U : Scheme)) (a r : Γ(X, U))
    (hr : actualOpenPointResidue U q r = 0) :
    actualRelativeDifferentialCommonOpenPointClass g U q (a * r) =
      actualOpenPointResidue U q a • actualRelativeDifferentialCommonOpenPointClass g U q r := by
  rw [actualRelativeDifferentialCommonOpenPointClass_mul, hr, zero_smul, add_zero]

end PfaffianDescent
