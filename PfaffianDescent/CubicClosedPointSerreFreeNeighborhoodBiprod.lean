import PfaffianDescent.SheafFreeCover
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Actual rank-two free coordinates for a split unit extension -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Two copies of the actual unit module form the actual free rank-two
module sheaf, with its prescribed lifted `Fin 2` index type. -/
def cubicClosedPointSerreFreeNeighborhoodUnitBiprodIso (X : Scheme.{u}) :
    SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) ≅
      (SheafOfModules.unit X.ringCatSheaf ⊞ SheafOfModules.unit X.ringCatSheaf) := by
  classical
  let h : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) ⟶
      (SheafOfModules.unit X.ringCatSheaf ⊞ SheafOfModules.unit X.ringCatSheaf) :=
    Sigma.desc (fun i => if i.down = 0 then biprod.inl else biprod.inr)
  let v : (SheafOfModules.unit X.ringCatSheaf ⊞ SheafOfModules.unit X.ringCatSheaf) ⟶
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) :=
    biprod.desc (SheafOfModules.ιFree (ULift.up 0)) (SheafOfModules.ιFree (ULift.up 1))
  refine ⟨h, v, ?_, ?_⟩
  · apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (ULift.{u} (Fin 2)))
    intro i
    obtain ⟨i⟩ := i
    fin_cases i <;> simp [h, v, SheafOfModules.freeCofan, SheafOfModules.ιFree]
  · apply biprod.hom_ext'
    · simp [h, v, SheafOfModules.ιFree]
    · simp [h, v, SheafOfModules.ιFree]

/-- A section of an actual short exact unit-by-unit sequence gives an
explicit actual free rank-two sheaf isomorphism. -/
def cubicClosedPointSerreFreeNeighborhoodSplitIso
    {X : Scheme.{u}} (E : X.Modules)
    (i : SheafOfModules.unit X.ringCatSheaf ⟶ E)
    (p : E ⟶ SheafOfModules.unit X.ringCatSheaf) (hip : i ≫ p = 0)
    (hS : (ShortComplex.mk i p hip).ShortExact)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ E) (hs : s ≫ p = 𝟙 _) :
    SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)) ≅ E := by
  let S := ShortComplex.mk i p hip
  let b := ShortComplex.Splitting.ofExactOfSection S hS.exact s hs hS.mono_f
  exact cubicClosedPointSerreFreeNeighborhoodUnitBiprodIso X ≪≫ b.isoBinaryBiproduct.symm

end PfaffianDescent
