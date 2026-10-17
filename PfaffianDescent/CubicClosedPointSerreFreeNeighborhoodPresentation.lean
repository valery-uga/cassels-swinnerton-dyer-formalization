import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodBiprod
import PfaffianDescent.SerreExtensionFoundation

/-! # An actual finite quotient presentation proves rank-two freeness -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual lifted generators of a finite quotient presentation form a
free rank-two sheaf whenever their relation has an invertible actual unit
coefficient.  The short five lemma proves the displayed map itself is an
isomorphism, with no finiteness hypothesis on the unknown middle sheaf. -/
theorem cubicClosedPointSerreFreeNeighborhoodPresentation_lift_isIso
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionSequenceData X M)
    (d : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)))
    (q : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) ⟶ M)
    (hdq : d ≫ q = 0) (hS : (ShortComplex.mk d q hdq).ShortExact)
    (v : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) ⟶ e.E)
    (hv : v ≫ e.projection = q)
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso c] (hc : d ≫ v = c ≫ e.inclusion) : IsIso v := by
  let S := ShortComplex.mk d q hdq
  let a : S ⟶ e.complex := ShortComplex.homMk c v (𝟙 M) hc.symm
    (by simpa [S] using hv)
  have h₁ : IsIso a.τ₁ := by change IsIso c; infer_instance
  have h₃ : IsIso a.τ₃ := by change IsIso (𝟙 M); infer_instance
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' a hS e.shortExact h₁ h₃

/-- The corresponding explicit free sheaf identification. -/
def cubicClosedPointSerreFreeNeighborhoodPresentationIso
    {X : Scheme.{u}} {M : X.Modules} (e : SerreExtensionSequenceData X M)
    (d : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)))
    (q : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) ⟶ M)
    (hdq : d ≫ q = 0) (hS : (ShortComplex.mk d q hdq).ShortExact)
    (v : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) ⟶ e.E)
    (hv : v ≫ e.projection = q)
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso c] (hc : d ≫ v = c ≫ e.inclusion) :
    SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) ≅ e.E := by
  letI := cubicClosedPointSerreFreeNeighborhoodPresentation_lift_isIso e d q hdq hS v hv c hc
  exact asIso v

end PfaffianDescent
