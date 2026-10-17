import PfaffianDescent.FieldPointLocalTargetCoordinate

/-! # A residue-field coordinate on actual Ext with locally trivial target -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open scoped nonZeroDivisors
namespace PfaffianDescent
universe u

set_option backward.isDefEq.respectTransparency false in
/-- The actual point resolution supplies the local nonzero class and injective
localization needed for a residue-field coordinate, for any target locally
trivialized on the chart. This is independent of global Serre trace nonvanishing. -/
def fieldPointExtTwoCoordinateAddEquivOfLocalTargetKoszulResolution
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    (T : X.Modules) {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (U : X.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ((U : Scheme), ⊤)] (hx : i default ∈ U) (q f : Γ(X, U))
    (qM : (schemeModuleStalkModuleFunctor X (i default)).obj
        (closedImmersionIdealTwistSequence i T).X₃ ≅
      ModuleCat.of (X.presheaf.stalk (i default))
        (sectionRepresenterPointKoszulQuotient
          X U (i default) hx q f))
    (hspan : ∀ (z : X) (hz : z ∈ U), z ≠ i default →
      Ideal.span
        ({X.presheaf.germ U z hz q, X.presheaf.germ U z hz f} :
          Set (X.presheaf.stalk z)) = ⊤)
    (hqreg : X.presheaf.germ U (i default) hx q ∈
      (X.presheaf.stalk (i default))⁰)
    (hfreg : Ideal.Quotient.mk
        (Ideal.span {X.presheaf.germ U (i default) hx q})
        (X.presheaf.germ U (i default) hx f) ∈
      ((X.presheaf.stalk (i default)) ⧸
        Ideal.span {X.presheaf.germ U (i default) hx q})⁰)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    (Y : X.Modules)
    (eY : Y.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    [hExt : HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i default)))] :
    let hmax := Ideal.span
      ({X.presheaf.germ U (i default) hx q,
        X.presheaf.germ U (i default) hx f} : Set _) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i default))
    hmax → Ext.{u} (closedImmersionIdealTwistSequence i T).X₃ Y 2 ≃+ L := by
  dsimp only
  intro hmax
  let x : U := ⟨i default, hx⟩
  let qY := schemeModuleLocalUnitStalkIso U x Y eY
  let coord := schemeModuleLocalUnitSectionAddEquiv U Y eY
  let y := coord.symm (1 : Γ(X, U))
  have hqmax : X.presheaf.germ U (i default) hx q ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i default)) := by
    rw [← hmax]
    exact Ideal.subset_span (by simp)
  have hfmax : X.presheaf.germ U (i default) hx f ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i default)) := by
    rw [← hmax]
    exact Ideal.subset_span (by simp)
  have hy : schemeModuleSectionStalkCoordinateAddHom U (i default) hx Y qY y ∉
      Ideal.span ({X.presheaf.germ U (i default) hx q,
        X.presheaf.germ U (i default) hx f} : Set _) := by
    apply schemeModuleSectionStalkCoordinateAddHom_not_mem_span_of_eq_one
      U (i default) hx Y qY q f y hqmax hfmax
    have hgerm : schemeModuleSectionStalkCoordinateAddHom U (i default) hx Y qY y =
        X.presheaf.germ U (i default) hx (coord y) :=
      schemeModuleLocalUnitStalkCoordinate_germ U x Y eY y
    rw [hgerm]
    change X.presheaf.germ U (i default) hx (coord (coord.symm 1)) = 1
    rw [AddEquiv.apply_symm_apply, map_one]
  let z := fieldPointSectionRepresenterKoszulDegreeTwoClass
    i T V hV eV U hx q f qM hspan hqreg hfreg Y y
  have hn := fieldPointSectionRepresenterKoszulDegreeTwoClass_stalk_ne_zero
    i T V hV eV U hx q f qM hspan hqreg hfreg Y y qY hy
  have hz : z ≠ 0 := by
    intro hz0
    apply hn
    change schemeModuleStalkModuleExtMap X (i default)
      (closedImmersionIdealTwistSequence i T).X₃ Y 2 z = 0
    rw [hz0, map_zero]
  let hstalk := fieldPointKoszul_stalkExtTwo_injective_of_localTargetTrivialization
    i T V hV eV U hU hx q f qM hspan hqreg hfreg Y eY
  exact fieldPointExtTwoCoordinateAddEquivOfLocalTrivialization
    i default T U hx eT Y
    (X.presheaf.germ U (i default) hx q)
    (X.presheaf.germ U (i default) hx f) hqreg hfreg hqmax hfmax
    qM qY hmax hstalk z hz

end PfaffianDescent
