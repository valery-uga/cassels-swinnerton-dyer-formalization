import PfaffianDescent.FieldPointExtResiduePresentation
import PfaffianDescent.FieldPointLocalTargetExtEquiv

/-! # Residue data for the actual locally trivial target coordinate -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open scoped nonZeroDivisors
namespace PfaffianDescent
universe u

set_option backward.isDefEq.respectTransparency false in
/-- The constructed local-target coordinate carries its actual residue presentation. -/
theorem fieldPointExtTwoCoordinateAddEquivOfLocalTargetKoszulResolution_residuePresentation
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
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i default)))]
    (hmax : Ideal.span
      ({X.presheaf.germ U (i default) hx q,
        X.presheaf.germ U (i default) hx f} : Set _) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i default))) :
    Nonempty (FieldPointExtResiduePresentation i default
      (closedImmersionIdealTwistSequence i T).X₃ Y
      (fieldPointExtTwoCoordinateAddEquivOfLocalTargetKoszulResolution
        i T V hV eV U hU hx q f qM hspan hqreg hfreg eT Y eY hmax)) := by
  have hqmax : X.presheaf.germ U (i default) hx q ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i default)) := by
    rw [← hmax]
    exact Ideal.subset_span (by simp)
  have hfmax : X.presheaf.germ U (i default) hx f ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i default)) := by
    rw [← hmax]
    exact Ideal.subset_span (by simp)
  refine ⟨{
    f := X.presheaf.germ U (i default) hx q
    g := X.presheaf.germ U (i default) hx f
    hf := hqreg
    hg := hfreg
    hfm := hqmax
    hgm := hfmax
    qM := qM
    qN := schemeModuleLocalUnitStalkIso U ⟨i default, hx⟩ Y eY
    coordinate_eq := ?_ }⟩
  intro z
  rfl

end PfaffianDescent
