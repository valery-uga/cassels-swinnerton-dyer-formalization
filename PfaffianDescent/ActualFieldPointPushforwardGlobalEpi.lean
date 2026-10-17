import PfaffianDescent.ActualFieldPointPushforwardSectionTransport
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Functor.EpiMono

/- SOURCE ONLY / UNVERIFIED. Chart containing P plus its closed-point
complement proves actual GLOBAL sheaf Epi. This is an auxiliary local test;
actual cubic caller must derive chart surjectivity, not assume global Epi. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u

theorem actualFieldPointPushforward_map_isLocallySurjective_of_chart
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (P : X) (hconst : ∀ z, q z = P)
    (hClosed : IsClosed ({P} : Set X)) (M : X.Modules)
    (t : M ⟶ (Scheme.Modules.pushforward q).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (V : X.Opens) (hPV : P ∈ V) (hsurj : Function.Surjective (t.app V)) :
    TopCat.Presheaf.IsLocallySurjective
      (((SheafOfModules.toSheaf X.ringCatSheaf).map t).hom) := by
  let O := SheafOfModules.unit (Spec (.of L)).ringCatSheaf
  let N := (Scheme.Modules.pushforward q).obj O
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U s x hxU
  by_cases hxP : x = P
  · subst x
    let W := V ⊓ U
    have hPW : P ∈ W := ⟨hPV, hxU⟩
    let eU := actualFieldPointPushforwardUnit_sectionIso q P hconst U hxU
    let eV := actualFieldPointPushforwardUnit_sectionIso q P hconst V hPV
    let eW := actualFieldPointPushforwardUnit_sectionIso q P hconst W hPW
    obtain ⟨mV, hmV⟩ := hsurj (eV.hom (eU.inv s))
    refine ⟨W, inf_le_right, ⟨M.presheaf.map (homOfLE inf_le_left).op mV, ?_⟩, hPW⟩
    have hn := ConcreteCategory.congr_hom
      (t.mapPresheaf.naturality (homOfLE (show W ≤ V from inf_le_left)).op) mV
    change t.app W (M.presheaf.map (homOfLE inf_le_left).op mV) =
      N.presheaf.map (homOfLE inf_le_right).op s
    calc
      _ = N.presheaf.map (homOfLE inf_le_left).op (t.app V mV) := hn
      _ = N.presheaf.map (homOfLE inf_le_left).op (eV.hom (eU.inv s)) := by rw [hmV]
      _ = eW.hom (eU.inv s) := ConcreteCategory.congr_hom
        (actualFieldPointPushforwardUnit_sectionIso_restrict q P hconst
          (show W ≤ V from inf_le_left) hPV hPW) (eU.inv s)
      _ = N.presheaf.map (homOfLE inf_le_right).op s := by
        have h := ConcreteCategory.congr_hom
          (actualFieldPointPushforwardUnit_sectionIso_restrict q P hconst
            (show W ≤ U from inf_le_right) hxU hPW) (eU.inv s)
        simpa only [Iso.inv_hom_id_apply] using h.symm
  · let C : X.Opens := ⟨({P} : Set X)ᶜ, hClosed.isOpen_compl⟩
    let W := U ⊓ C
    have hxW : x ∈ W := ⟨hxU, hxP⟩
    have hEmpty : q ⁻¹ᵁ W = ⊥ := by
      ext z
      change (q z ∈ U ∧ q z ≠ P) ↔ False
      simp only [hconst z, ne_eq, eq_self_iff_true, not_true_eq_false, and_false]
    letI : Subsingleton Γ(N, W) := by
      change Subsingleton Γ(O, q ⁻¹ᵁ W)
      rw [hEmpty]
      exact actualAffineModule_empty_sections_subsingleton O
    exact ⟨W, inf_le_left, ⟨0, Subsingleton.elim _ _⟩, hxW⟩

theorem actualFieldPointPushforward_map_epi_of_chart
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (P : X) (hconst : ∀ z, q z = P)
    (hClosed : IsClosed ({P} : Set X)) (M : X.Modules)
    (t : M ⟶ (Scheme.Modules.pushforward q).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (V : X.Opens) (hPV : P ∈ V) (hsurj : Function.Surjective (t.app V)) : Epi t := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  letI : Sheaf.IsLocallySurjective (F.map t) :=
    actualFieldPointPushforward_map_isLocallySurjective_of_chart q P hconst hClosed M t V hPV hsurj
  have h : Epi (F.map t) := inferInstance
  exact F.epi_of_epi_map h

end PfaffianDescent
