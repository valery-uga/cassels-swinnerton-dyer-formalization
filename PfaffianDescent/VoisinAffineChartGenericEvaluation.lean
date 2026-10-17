import PfaffianDescent.VoisinAffineChartCoordinateSections
import AllCharacteristics.SpecGlobalSectionEvaluation

/-! An affine chart coordinate evaluated through a field-valued point
equals the value of its pulled global section. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

theorem specPreimage_apply_eq_appTop_evaluation
    {A F : Type u} [CommRing A] [Field F]
    (f : Spec (.of F) ⟶ Spec (.of A)) (r : A) :
    (Spec.preimage f).hom r =
      (Scheme.ΓSpecIso (.of F)).hom.hom
        (f.appTop.hom ((StructureSheaf.globalSectionsIso A).hom r)) := by
  have h := specMap_appTop_structureSheafSection_apply
    (Spec.preimage f).hom r
  have he : f.appTop.hom
      ((StructureSheaf.globalSectionsIso A).hom r) =
      (StructureSheaf.globalSectionsIso F).hom
        ((Spec.preimage f).hom r) := by
    simpa only [CommRingCat.ofHom_hom, Spec.map_preimage] using h
  rw [he]
  exact ((Scheme.ΓSpecIso (.of F)).inv_hom_id_apply _).symm

theorem specPreimage_comp_apply_eq_appTop_evaluation
    {A F : Type u} [CommRing A] [Field F]
    (U : Scheme.{u})
    (s : Spec (.of F) ⟶ U)
    (t : U ⟶ Spec (.of A)) (r : A) :
    (Spec.preimage (s ≫ t)).hom r =
      (Scheme.ΓSpecIso (.of F)).hom.hom
        (s.appTop.hom
          (t.appTop.hom ((StructureSheaf.globalSectionsIso A).hom r))) := by
  rw [specPreimage_apply_eq_appTop_evaluation]
  rw [Scheme.Hom.comp_appTop]
  rfl

end PfaffianDescent
