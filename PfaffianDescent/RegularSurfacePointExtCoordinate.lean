import PfaffianDescent.FieldPointAffineKoszulCoordinate
import PfaffianDescent.SmoothPointKoszulParameters

/-!
# Ext coordinates from a regular closed surface point

A twist-trivializing cover and a regular dimension-two closed point suffice:
the affine equations, support isolation, and restricted trivialization are
constructed here rather than supplied as additional premises.
-/

noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false in
/-- Restrict a unit trivialization on an over-site to a smaller open. -/
noncomputable def overFunctorUnitIso_restrict
    {X : Scheme.{u}} (T : X.Modules) {U V : X.Opens} (hUV : U ≤ V)
    (eV : (SheafOfModules.overFunctor X.ringCatSheaf V).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf V))) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)) :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE hUV)).app T).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE hUV)).mapIso eV ≪≫
    SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) (homOfLE hUV)
set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The global degree-two point Ext group has a field coordinate, constructed
from regular surface geometry and a locally trivial twist. -/
noncomputable def fieldPointExtTwoCoordinateAddEquivOfRegularSurfacePoint
    {L : Type u} [Field L] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    [IsRegularLocalRing (X.presheaf.stalk (i default))]
    (hdim : ringKrullDim (X.presheaf.stalk (i default)) = 2)
    (T : X.Modules) {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i default)))] :
    Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2 ≃+ L := by
  classical
  have hclosed : IsClosed ({i default} : Set X) := by
    have hrange : Set.range i = {i default} := by
      ext x
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨y, rfl⟩
        congr 1
        exact Subsingleton.elim _ _
      · rintro rfl
        exact ⟨default, rfl⟩
    rw [← hrange]
    exact i.isClosedEmbedding.isClosed_range
  have hcover : TopologicalSpace.IsOpenCover V := (Opens.coversTop_iff X V).mp hV
  have hxCover : i default ∈ ⨆ j, V j := by
    rw [hcover.iSup_eq_top]
    trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hxCover
  let j := Classical.choose hxCover
  have hj := Classical.choose_spec hxCover
  choose U hU hx q f hUV hqreg hfreg hmax hspan using
    exists_affine_point_koszul_parameters (i default) hdim hclosed (V j) hj
  letI : IsNoetherianRing Γ((U : Scheme), ⊤) := by
    exact IsLocallyNoetherian.component_noetherian ⟨⊤, by
      letI : IsAffine (U : Scheme) := hU
      exact isAffineOpen_top _⟩
  exact fieldPointExtTwoCoordinateAddEquivOfAffineKoszulResolution
    i T V hV eV U hU hx q f hspan hqreg hfreg
    (overFunctorUnitIso_restrict T hUV (eV j)) hmax
end PfaffianDescent
