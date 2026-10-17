import PfaffianDescent.SchemeModuleActualLocalHomGluing
import PfaffianDescent.FiniteProjectiveProjectionFormula

/-! SOURCE ONLY. Genuine Iso descent for actual native local Hom maps.
The final geometric caller must derive the displayed local Isos and their
whole compatibility; this module is the ordinary sheaf descent mechanism. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open SchemeModuleInternalHom
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

/-- The actual glued morphism restricts to the SAME entire local morphism. -/
theorem schemeModuleHomGlueOfActualCompatibleOverMorphisms_over
    {ι : Type u} (U : ι → X.Opens) (hcover : ⨆ i, U i = ⊤)
    (f : ∀ i, M.over (U i) ⟶ N.over (U i))
    (hcompat : ∀ i j,
      (SchemeModuleInternalHom.sheaf M N).val.map
          (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op
          ((sectionsEquivOver M N (U i)).symm (f i)) =
        (SchemeModuleInternalHom.sheaf M N).val.map
          (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op
          ((sectionsEquivOver M N (U j)).symm (f j))) (i : ι) :
    (schemeModuleHomGlueOfActualCompatibleOverMorphisms M N U hcover f hcompat).over
      (U i) = f i := by
  apply (sectionsEquivOver M N (U i)).symm.injective
  exact schemeModuleHomGlueOfActualCompatibleOverMorphisms_homSection
    M N U hcover f hcompat i

/-- Isomorphism on the actual over-site implies isomorphism after actual
scheme restriction, by the installed native over-site equivalence. -/
theorem restrictFunctorMap_isIso_of_actualOverMap_isIso
    (U : X.Opens) (f : M ⟶ N) [IsIso (f.over U)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) := by
  let E := Scheme.Modules.overEquiv U
  let H := SheafOfModules.overFunctor X.ringCatSheaf U
  let n := Scheme.Modules.overFunctorEquiv U
  letI : IsIso (H.map f) := by change IsIso (f.over U); infer_instance
  haveI : IsIso (E.functor.map (H.map f)) := Functor.map_isIso E.functor _
  have hOver : IsIso ((H ⋙ E.functor).map f) := by
    change IsIso (E.functor.map (H.map f))
    infer_instance
  exact (NatIso.isIso_map_iff n f).mp hOver

/-- The actual compatible local Iso maps produce a GLOBAL native module
Iso, internally proving its invertibility on original stalks. -/
def schemeModuleIsoGlueOfActualCompatibleOverIsos
    {ι : Type u} (U : ι → X.Opens) (hcover : ⨆ i, U i = ⊤)
    (e : ∀ i, M.over (U i) ≅ N.over (U i))
    (hcompat : ∀ i j,
      (SchemeModuleInternalHom.sheaf M N).val.map
          (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op
          ((sectionsEquivOver M N (U i)).symm (e i).hom) =
        (SchemeModuleInternalHom.sheaf M N).val.map
          (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op
          ((sectionsEquivOver M N (U j)).symm (e j).hom)) : M ≅ N := by
  let a := schemeModuleHomGlueOfActualCompatibleOverMorphisms M N U hcover
    (fun i => (e i).hom) hcompat
  haveI : IsIso a := by
    apply schemeModuleMap_isIso_of_stalk a
    intro x
    have hx : x ∈ ⨆ i, U i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    haveI : IsIso (a.over (U i)) := by
      rw [show a.over (U i) = (e i).hom from
        schemeModuleHomGlueOfActualCompatibleOverMorphisms_over
          M N U hcover (fun i => (e i).hom) hcompat i]
      infer_instance
    haveI : IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map a) :=
      restrictFunctorMap_isIso_of_actualOverMap_isIso M N (U i) a
    exact schemeModuleStalkMap_isIso_of_restrict (U i) ⟨x, hi⟩ a
  exact asIso a

end PfaffianDescent
