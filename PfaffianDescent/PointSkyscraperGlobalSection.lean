import PfaffianDescent.FieldPointSectionRepresenterKoszul

/-!
# Extending a point Koszul generator to a global section

Restriction from the top open to an open containing the skyscraper's center
is surjective. Transporting this fact to the actual point quotient supplies
a global section whose restriction is the already checked Koszul generator.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace PfaffianDescent

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Every section of a skyscraper on a neighborhood of its center extends
to the top open. -/
theorem schemeModuleSkyscraper_restriction_from_top_surjective
    {X : Scheme.{u}} (x : X) (A : ModuleCat.{u} (X.presheaf.stalk x))
    (U : X.Opens) (hx : x ∈ U) :
    Function.Surjective ((schemeModuleSkyscraper x A).val.map
      (homOfLE (le_top : U ≤ ⊤)).op) := by
  intro m
  let eU := schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx
  let eT := schemeModuleSkyscraperAbPresheafAddEquivOfMem x A ⊤ (show x ∈ ⊤ from trivial)
  refine ⟨eT.symm (eU m), ?_⟩
  apply eU.injective
  change schemeModuleSkyscraperAbPresheafAddEquivOfMem x A U hx
    ((schemeModuleSkyscraperAbPresheaf x A).map
      (homOfLE (le_top : U ≤ ⊤)).op (eT.symm (eU m))) = eU m
  rw [schemeModuleSkyscraperAbPresheafAddEquivOfMem_map]
  exact eT.apply_symm_apply (eU m)

set_option backward.isDefEq.respectTransparency false in
/-- The section extension property transports along an actual skyscraper
isomorphism. -/
theorem schemeModule_restriction_from_top_surjective_of_skyscraperIso
    {X : Scheme.{u}} (x : X) (A : ModuleCat.{u} (X.presheaf.stalk x))
    (M : X.Modules) (e : M ≅ schemeModuleSkyscraper x A)
    (U : X.Opens) (hx : x ∈ U) :
    Function.Surjective (M.val.map (homOfLE (le_top : U ≤ ⊤)).op) := by
  intro m
  obtain ⟨t, ht⟩ := schemeModuleSkyscraper_restriction_from_top_surjective x A U hx
    (e.hom.val.app (op U) m)
  refine ⟨e.inv.val.app (op (⊤ : X.Opens)) t, ?_⟩
  rw [← PresheafOfModules.naturality_apply, ht]
  change (e.hom ≫ e.inv).val.app (op U) m = m
  rw [e.hom_inv_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual point quotient's normalized local Koszul section extends
globally; the equality of local and global generators is proved. -/
theorem exists_fieldPointKoszul_global_section
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (U : X.Opens) (hx : i default ∈ U) (q f : Γ(X, U))
    (qM : (schemeModuleStalkModuleFunctor X (i default)).obj
        (closedImmersionIdealTwistSequence i T).X₃ ≅
      ModuleCat.of (X.presheaf.stalk (i default))
        (sectionRepresenterPointKoszulQuotient X U (i default) hx q f)) :
    ∃ s : (closedImmersionIdealTwistSequence i T).X₃.val.obj (op (⊤ : X.Opens)),
      (closedImmersionIdealTwistSequence i T).X₃.val.map
        (homOfLE (le_top : U ≤ ⊤)).op s =
      fieldPointSectionRepresenterKoszulSection i T V hV eV U hx q f qM := by
  exact schemeModule_restriction_from_top_surjective_of_skyscraperIso
    (i default) _ (closedImmersionIdealTwistSequence i T).X₃
    (fieldPointPushforwardTwist_skyscraperIso_of_coversTop_iso_unit i T V hV eV) U hx _

end PfaffianDescent
