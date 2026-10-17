import PfaffianDescent.ActualPointLocalExistingOpenClassComparison
import PfaffianDescent.ActualPointLocalSectionClassNaturality
import PfaffianDescent.ActualGlobalConormalPointLocalSectionAction

/-! SOURCE ONLY, UNVERIFIED. The actual global conormal differential on
the existing open-point class is computed by the true local derivative. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule BundleSectionZeroLocus
universe u

lemma actualModulePointSectionClass_naturality
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) {M N : X.Modules} (a : M ⟶ N)
    (v : schemeModuleUnit X ⟶ M) :
    (moduleSpecΓFunctor (R := .of L)).map ((Scheme.Modules.pullback q).map a)
      (actualModulePointSectionClass q M v) =
      actualModulePointSectionClass q N (v ≫ a) := by
  let P := Scheme.Modules.pullback q
  let u := pullbackUnitComparison q
  letI : IsIso u := by
    dsimp only [u]
    exact isIso_pullbackUnitComparison q
  change (P.map a).val.app (op ⊤)
    ((inv u ≫ P.map v).val.app (op ⊤) (1 : Γ(Spec (.of L), ⊤))) =
      (inv u ≫ P.map (v ≫ a)).val.app (op ⊤) (1 : Γ(Spec (.of L), ⊤))
  rw [Functor.map_comp]
  rfl

lemma actualModuleOpenPointSectionClass_naturality
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of K)) (U : X.Opens)
    (j : Spec (.of L) ⟶ (U : Scheme)) {M N : X.Modules} (a : M ⟶ N)
    (z : Γ(M, U)) :
    (moduleSpecΓFunctor (R := .of L)).map ((Scheme.Modules.pullback (j ≫ U.ι)).map a)
      (actualModuleOpenPointSectionClass g U j M z) =
      actualModuleOpenPointSectionClass g U j N (a.val.app (op U) z) := by
  rw [← actualPointLocalExistingOpenClassComparison,
    ← actualPointLocalExistingOpenClassComparison]
  exact actualPointLocalSectionClass_naturality (j ≫ U.ι) a U _ z

lemma actualGlobalConormalExistingOpenPointAction
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of K)) (U : X.Opens)
    (j : Spec (.of L) ⟶ (U : Scheme)) [IsClosedImmersion (j ≫ U.ι)]
    (z : Γ(closedImmersionModule (j ≫ U.ι), U)) :
    (moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap g (j ≫ U.ι))
      (actualModuleOpenPointSectionClass g U j (closedImmersionModule (j ≫ U.ι)) z) =
    actualModuleOpenPointSectionClass g U j (schemeRelativeDifferentials g)
      (actualRelativeDifferentialSection g U
        ((closedImmersionModuleToUnit (j ≫ U.ι)).val.app (op U) z)) := by
  rw [← actualPointLocalExistingOpenClassComparison,
    ← actualPointLocalExistingOpenClassComparison]
  exact actualGlobalConormalPointLocalSectionAction g (j ≫ U.ι) U _ z

end PfaffianDescent
