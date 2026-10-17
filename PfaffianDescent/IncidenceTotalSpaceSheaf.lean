import PfaffianDescent.IncidenceTotalSpaceGlobalEquiv

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
section
variable (K : Type u) [CommRing K]

/-- The presheaf of actual scheme sections of the incidence projection. -/
noncomputable def incidenceSchemeSectionPresheaf :
    (TopologicalSpace.Opens (grassmannianScheme K 3 3))ᵒᵖ ⥤ Type u where
  obj U := IncidenceSchemeSections K U.unop
  map h := TypeCat.ofHom (incidenceSchemeSectionsRestrict K _ _ (leOfHom h.unop))
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (grassmannianScheme K 3 3).homOfLE _ ≫ s.val = s.val
    rw [Scheme.homOfLE_rfl, Category.id_comp]
  map_comp h g := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (incidenceSchemeSectionsRestrict_trans K _ _ _ (leOfHom h.unop) (leOfHom g.unop) s).symm

/-- The global incidence section functor is naturally isomorphic to the actual kernel sheaf. -/
noncomputable def incidenceTotalSpaceSectionIso :
    incidenceSchemeSectionPresheaf K ≅
      (incidenceKernelSheaf K).presheaf ⋙ forget AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun U => (incidenceSchemeKernelSectionsEquiv K U.unop).toIso)
    (by
      intro U V h
      apply ConcreteCategory.hom_ext
      intro s
      exact incidenceSchemeKernelSectionsEquiv_restrict K U.unop V.unop (leOfHom h.unop) s)

end
end PfaffianDescent
