import PfaffianDescent.IncidenceTotalSpaceLocalNaturality
import PfaffianDescent.SchemeOpenMorphismGluing
import PfaffianDescent.SchemeModuleSectionGluing

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u v
section
variable (K : Type u) [CommRing K]

lemma incidenceSchemeSectionsRestrict_trans
    (U V W : (grassmannianScheme K 3 3).Opens) (hV : V ≤ U) (hW : W ≤ V)
    (s : IncidenceSchemeSections K U) :
    incidenceSchemeSectionsRestrict K V W hW (incidenceSchemeSectionsRestrict K U V hV s) =
      incidenceSchemeSectionsRestrict K U W (hW.trans hV) s := by
  apply Subtype.ext
  change _ ≫ (_ ≫ s.val) = _ ≫ s.val
  rw [← Category.assoc, Scheme.homOfLE_homOfLE]

lemma incidenceKernelSectionRestrict_trans
    (U V W : (grassmannianScheme K 3 3).Opens) (hV : V ≤ U) (hW : W ≤ V)
    (s : Γ(incidenceKernelSheaf K, U)) :
    incidenceKernelSectionRestrict K V W hW (incidenceKernelSectionRestrict K U V hV s) =
      incidenceKernelSectionRestrict K U W (hW.trans hV) s :=
  (PresheafOfModules.map_comp_apply (incidenceKernelSheaf K).val
    (homOfLE hV).op (homOfLE hW).op s).symm

variable {ι : Type v} (U : (grassmannianScheme K 3 3).Opens)
    (V : ι → (grassmannianScheme K 3 3).Opens) (hV : ∀ i, V i ≤ U)
    (hcover : U ≤ ⨆ i, V i)
include hcover

/-- Actual sections of the incidence projection glue uniquely over any open cover. -/
theorem incidenceSchemeSections_glue (s : ∀ i, IncidenceSchemeSections K (V i))
    (h : ∀ i j, incidenceSchemeSectionsRestrict K (V i) (V i ⊓ V j) inf_le_left (s i) =
      incidenceSchemeSectionsRestrict K (V j) (V i ⊓ V j) inf_le_right (s j)) :
    ∃! x : IncidenceSchemeSections K U, ∀ i, incidenceSchemeSectionsRestrict K U (V i) (hV i) x = s i := by
  obtain ⟨f, hf, hu⟩ := schemeOpenMorphisms_glue U V hV hcover (fun i => (s i).val)
    (fun i j => congrArg Subtype.val (h i j))
  have hp : f ≫ incidenceToGrassmannian K = U.ι := by
    apply schemeOpenMorphisms_ext U V hV hcover
    intro i
    rw [← Category.assoc, hf i, (s i).property, Scheme.homOfLE_ι]
  refine ⟨⟨f, hp⟩, fun i => Subtype.ext (hf i), ?_⟩
  intro y hy
  apply Subtype.ext
  exact hu y.val (fun i => congrArg Subtype.val (hy i))

lemma incidenceSchemeSections_ext (x y : IncidenceSchemeSections K U)
    (h : ∀ i, incidenceSchemeSectionsRestrict K U (V i) (hV i) x =
      incidenceSchemeSectionsRestrict K U (V i) (hV i) y) : x = y := by
  apply Subtype.ext
  exact schemeOpenMorphisms_ext U V hV hcover x.val y.val (fun i => congrArg Subtype.val (h i))

end
end PfaffianDescent
