import PfaffianDescent.ActualGlobalConormalPointLocalSectionAction
import PfaffianDescent.ActualGlobalConormalAdjunctOpenSectionAction

/- SOURCE ONLY / UNVERIFIED. GLOBAL conormal D on LOCAL original ideal
sections is computed by the SAME chart universal derivative, using actual
point adjunction and the genuine open differential sheaf Iso. No source
or target comparison square is assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
universe u

lemma actualGlobalConormalPointLocalChartDerivative
    {k L : Type u} [CommRing k] [Field L] {X Y : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsOpenImmersion f]
    (j : Spec (.of L) ⟶ Y) (q : Spec (.of L) ⟶ X) [IsClosedImmersion q]
    (hfac : j ≫ f = q)
    (z : (closedImmersionModule q).val.obj (op (f ''ᵁ (⊤ : Y.Opens)))) :
    (moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap g q)
      (actualPointLocalSectionClass q (closedImmersionModule q) (f ''ᵁ ⊤)
        (actualFieldPointFactor_preimage_image_top f j q hfac) z) =
    actualPointLocalSectionClass q (schemeRelativeDifferentials g) (f ''ᵁ ⊤)
      (actualFieldPointFactor_preimage_image_top f j q hfac)
      ((actualOpenImmersionDifferentialSheafRestrictionIso f g).hom.val.app (op ⊤)
        (actualRelativeDifferentialSection (f ≫ g) ⊤
          ((f.appIso ⊤).hom
            ((closedImmersionModuleToUnit q).val.app (op (f ''ᵁ ⊤)) z)))) := by
  have h := actualGlobalConormalPointLocalSectionAction_of_factor g f j q hfac z
  exact h.trans (congrArg
    (actualPointLocalSectionClass q (schemeRelativeDifferentials g) (f ''ᵁ ⊤)
      (actualFieldPointFactor_preimage_image_top f j q hfac))
    (actualOpenDifferentialSheafIso_section_D_image f g ⊤
      ((closedImmersionModuleToUnit q).val.app (op (f ''ᵁ ⊤)) z)).symm)

end PfaffianDescent
