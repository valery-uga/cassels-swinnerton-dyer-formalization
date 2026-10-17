import PfaffianDescent.ActualFieldPointModuleCounitIso
import Mathlib.Topology.Sheaves.LocallySurjective

/- SOURCE ONLY / UNVERIFIED. Literal pushforward sections retain their
actual point/preimage, including actual empty-value vanishing. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u

lemma actualAffineModule_empty_sections_subsingleton
    {R : CommRingCat.{u}} (M : (Spec R).Modules) : Subsingleton Γ(M, ⊥) := by
  change Subsingleton ((modulesSpecToSheaf.obj M).obj.obj (op ⊥))
  have hTerminal := (modulesSpecToSheaf.obj M).isTerminalOfEmpty
  have hZero : IsZero ((modulesSpecToSheaf.obj M).obj.obj (op ⊥)) :=
    IsZero.of_iso (isZero_zero (ModuleCat R))
      ((isZero_zero (ModuleCat R)).isoIsTerminal hTerminal).symm
  exact ModuleCat.subsingleton_of_isZero hZero

lemma actualFieldPoint_preimage_open_eq_top
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (P : X) (hconst : ∀ z, q z = P)
    (U : X.Opens) (hPU : P ∈ U) : q ⁻¹ᵁ U = ⊤ := by
  ext z
  change q z ∈ U ↔ True
  simp only [hconst z, hPU, true_iff]

def actualFieldPointPushforwardUnit_sectionIso
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (P : X) (hconst : ∀ z, q z = P)
    (U : X.Opens) (hPU : P ∈ U) :
    Γ(SheafOfModules.unit (Spec (.of L)).ringCatSheaf, ⊤) ≅
      Γ((Scheme.Modules.pushforward q).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf), U) :=
  (SheafOfModules.unit (Spec (.of L)).ringCatSheaf).presheaf.mapIso
    ((eqToIso (actualFieldPoint_preimage_open_eq_top q P hconst U hPU)).symm.op)

lemma actualFieldPointPushforwardUnit_sectionIso_restrict
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (P : X) (hconst : ∀ z, q z = P)
    {U V : X.Opens} (hVU : V ≤ U) (hPU : P ∈ U) (hPV : P ∈ V) :
    (actualFieldPointPushforwardUnit_sectionIso q P hconst U hPU).hom ≫
      ((Scheme.Modules.pushforward q).obj
        (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)).presheaf.map (homOfLE hVU).op =
      (actualFieldPointPushforwardUnit_sectionIso q P hconst V hPV).hom := by
  let O := SheafOfModules.unit (Spec (.of L)).ringCatSheaf
  change O.presheaf.map ((eqToHom
      (actualFieldPoint_preimage_open_eq_top q P hconst U hPU)).op) ≫
    O.presheaf.map (((Opens.map q.base).map (homOfLE hVU)).op) =
      O.presheaf.map ((eqToHom
        (actualFieldPoint_preimage_open_eq_top q P hconst V hPV)).op)
  rw [← Functor.map_comp, ← op_comp]
  congr 1
  exact congrArg Quiver.Hom.op (Subsingleton.elim _ _)

end PfaffianDescent
