import PfaffianDescent.ActualGlobalClosedConormalDifferentialMap
import PfaffianDescent.ActualOpenDifferentialSheafDerivationAction

/- SOURCE ONLY / UNVERIFIED. The genuine GLOBAL conormal adjoint's
section action is the SAME universal derivative under the internally
constructed actual open differential-sheaf Iso. This is a section theorem;
point-pullback/tensor coherence is not asserted by definition. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
universe u
variable {k : Type u} [CommRing k] {X Y Z : Scheme.{u}}

lemma actualOpenDifferentialSheafIso_section_D_image
    (f : Y ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (.of k))
    (U : Y.Opens) (r : Γ(X, f ''ᵁ U)) :
    (actualOpenImmersionDifferentialSheafRestrictionIso f g).hom.val.app (op U)
      (actualRelativeDifferentialSection (f ≫ g) U ((f.appIso U).hom r)) =
        actualRelativeDifferentialSection g (f ''ᵁ U) r := by
  rw [actualOpenImmersionDifferentialSheafIso_section_D, Iso.hom_inv_id_apply]

lemma actualGlobalConormalDifferentialMap_adjunct_openSection
    (f : Y ⟶ X) [IsOpenImmersion f] (g : X ⟶ Spec (.of k))
    (q : Z ⟶ X) [IsClosedImmersion q]
    (U : Y.Opens) (z : (closedImmersionModule q).val.obj (op (f ''ᵁ U))) :
    (((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _)
      (actualGlobalClosedConormalDifferentialMap g q)).val.app (op (f ''ᵁ U)) z =
    ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
      (schemeRelativeDifferentials g)).val.app (op (f ''ᵁ U))
      ((actualOpenImmersionDifferentialSheafRestrictionIso f g).hom.val.app (op U)
        (actualRelativeDifferentialSection (f ≫ g) U
          ((f.appIso U).hom
            ((closedImmersionModuleToUnit q).val.app (op (f ''ᵁ U)) z)))) := by
  have h := actualGlobalClosedConormalDifferentialMap_adjunct_section
    g q (f ''ᵁ U) z
  exact h.trans (congrArg
    (fun t => ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
      (schemeRelativeDifferentials g)).val.app (op (f ''ᵁ U)) t)
    (actualOpenDifferentialSheafIso_section_D_image f g U
      ((closedImmersionModuleToUnit q).val.app (op (f ''ᵁ U)) z)).symm)

end PfaffianDescent
