import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealUnitEndomorphism

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism_id
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism i (𝟙 _) = 𝟙 _ := by
  letI : Mono (closedImmersionModuleToUnit i) := by
    change Mono (idealModuleToUnit _)
    infer_instance
  apply (cancel_mono (closedImmersionModuleToUnit i)).mp
  rw [cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism_toUnit]
  simp

theorem cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism_comp
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism i (a ≫ b) =
      cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism i a ≫
        cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism i b := by
  letI : Mono (closedImmersionModuleToUnit i) := by
    change Mono (idealModuleToUnit _)
    infer_instance
  apply (cancel_mono (closedImmersionModuleToUnit i)).mp
  calc
    cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism i (a ≫ b) ≫
        closedImmersionModuleToUnit i = closedImmersionModuleToUnit i ≫ a ≫ b :=
      cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism_toUnit i (a ≫ b)
    _ = (closedImmersionModuleToUnit i ≫ a) ≫ b := (Category.assoc _ _ _).symm
    _ = (cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism i a ≫
        closedImmersionModuleToUnit i) ≫ b := congrArg (fun t => t ≫ b)
      (cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism_toUnit i a).symm
    _ = (cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism i a ≫
        cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism i b) ≫
        closedImmersionModuleToUnit i := by
      rw [Category.assoc, Category.assoc,
        cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism_toUnit]

/-- An actual change of unit coordinates acts invertibly on the SAME actual
closed ideal, retaining the literal inclusion square. -/
def cubicClosedPointSerreSurfaceJetCotangent_idealUnitAutomorphismIso
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (a : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf) :
    closedImmersionModule i ≅ closedImmersionModule i where
  hom := cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism i a.hom
  inv := cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism i a.inv
  hom_inv_id := by
    rw [← cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism_comp,
      a.hom_inv_id, cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism_id]
  inv_hom_id := by
    rw [← cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism_comp,
      a.inv_hom_id, cubicClosedPointSerreSurfaceJetCotangent_idealUnitEndomorphism_id]

end PfaffianDescent
