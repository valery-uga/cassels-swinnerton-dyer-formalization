import PfaffianDescent.FieldPointLocalTargetResiduePresentation
import PfaffianDescent.RegularSurfacePointExtCoordinate

/-! # Actual coefficient-target Ext coordinates from regular surface geometry -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
namespace PfaffianDescent
universe u

/-- Shrinking an actual unit trivialization preserves the specified coefficient module. -/
def schemeModuleLocalUnitTrivialization_restrict {X : Scheme.{u}}
    (Y : X.Modules) {U V : X.Opens} (hUV : U ≤ V)
    (eV : Y.restrict V.ι ≅ SheafOfModules.unit (V : Scheme).ringCatSheaf) :
    Y.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf :=
  (Scheme.Modules.restrictFunctorCongr (Scheme.homOfLE_ι X hUV).symm).app Y ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE hUV) V.ι).app Y ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE hUV)).mapIso eV ≪≫
    Scheme.Modules.restrictUnitIso (X.homOfLE hUV)

set_option backward.isDefEq.respectTransparency false in
/-- The affine equations, local quotient and coefficient coordinates are constructed
from a regular closed surface point and actual local trivializations. -/
noncomputable def regularSurfacePointExtCoordinateWithResiduePresentation
    {L : Type u} [Field L] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    [IsRegularLocalRing (X.presheaf.stalk (i default))]
    (hdim : ringKrullDim (X.presheaf.stalk (i default)) = 2)
    (T : X.Modules) {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (Y : X.Modules)
    (eYV : ∀ j, Y.restrict (V j).ι ≅ SheafOfModules.unit (V j : Scheme).ringCatSheaf)
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i default)))] :
    Σ e : Ext.{u} (closedImmersionIdealTwistSequence i T).X₃ Y 2 ≃+ L,
      FieldPointExtResiduePresentation i default
        (closedImmersionIdealTwistSequence i T).X₃ Y e := by
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
  let eT := overFunctorUnitIso_restrict T hUV (eV j)
  let qM := fieldPointPushforwardTwistStalkQuotientIsoOfLocalTrivialization
    i default T U hx eT
    (X.presheaf.germ U (i default) hx q)
    (X.presheaf.germ U (i default) hx f) hmax
  let eY := schemeModuleLocalUnitTrivialization_restrict Y hUV (eYV j)
  let e := fieldPointExtTwoCoordinateAddEquivOfLocalTargetKoszulResolution
    i T V hV eV U hU hx q f qM hspan hqreg hfreg eT Y eY hmax
  have hd := fieldPointExtTwoCoordinateAddEquivOfLocalTargetKoszulResolution_residuePresentation
    i T V hV eV U hU hx q f qM hspan hqreg hfreg eT Y eY hmax
  exact ⟨e, Classical.choice hd⟩

set_option backward.isDefEq.respectTransparency false in
/-- The affine geometry constructs the actual point Ext equivalence. The
residue presentation is retained by the underlying certified construction. -/
noncomputable def fieldPointExtTwoCoordinateAddEquivOfRegularSurfacePointLocalTarget
    {L : Type u} [Field L] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    [IsRegularLocalRing (X.presheaf.stalk (i default))]
    (hdim : ringKrullDim (X.presheaf.stalk (i default)) = 2)
    (T : X.Modules) {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (Y : X.Modules)
    (eYV : ∀ j, Y.restrict (V j).ι ≅ SheafOfModules.unit (V j : Scheme).ringCatSheaf)
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i default)))] :
    Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      Y 2 ≃+ L :=
  (regularSurfacePointExtCoordinateWithResiduePresentation i hdim T V hV eV Y eYV).1

end PfaffianDescent
