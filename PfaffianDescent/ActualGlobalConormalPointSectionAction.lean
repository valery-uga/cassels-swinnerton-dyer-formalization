import PfaffianDescent.ActualGlobalPointAdjunctionSectionEvaluation
import PfaffianDescent.ActualGlobalClosedConormalDifferentialMap
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernelSectionHom

/- SOURCE ONLY / UNVERIFIED. The GENUINE GLOBAL conormal map on an
actual ideal section is the true point pullback of the universal D of
its actual included coefficient. No affine/chart comparison premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule BundleSectionZeroLocus
universe u

lemma actualGlobalConormalPointSectionAction
    {k L : Type u} [CommRing k] [Field L] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) (q : Spec (.of L) ⟶ X) [IsClosedImmersion q]
    (v : schemeModuleUnit X ⟶ closedImmersionModule q) :
    (moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap g q)
      (actualModulePointSectionClass q (closedImmersionModule q) v) =
    actualModulePointSectionClass q (schemeRelativeDifferentials g)
      (cubicClosedPointSerreSurfaceJetCotangent_sectionHomOfTop
        (schemeRelativeDifferentials g)
        (actualRelativeDifferentialSection g ⊤
          ((closedImmersionModuleToUnit q).val.app (op ⊤)
            (v.val.app (op ⊤) (1 : Γ(X, ⊤)))))) := by
  rw [actualGlobalPointAdjunctionSectionEvaluation,
    actualGlobalClosedConormalDifferentialMap_adjunct_section]
  let O := schemeRelativeDifferentials g
  let t := cubicClosedPointSerreSurfaceJetCotangent_sectionHomOfTop O
    (actualRelativeDifferentialSection g ⊤
      ((closedImmersionModuleToUnit q).val.app (op ⊤)
        (v.val.app (op ⊤) (1 : Γ(X, ⊤)))))
  have h := actualGlobalPointAdjunctionSectionEvaluation q O
    ((Scheme.Modules.pullback q).obj O) t (𝟙 _)
  rw [Functor.map_id, ModuleCat.id_apply,
    Adjunction.homEquiv_id,
    cubicClosedPointSerreSurfaceJetCotangent_sectionHomOfTop_one] at h
  exact h.symm

end PfaffianDescent
