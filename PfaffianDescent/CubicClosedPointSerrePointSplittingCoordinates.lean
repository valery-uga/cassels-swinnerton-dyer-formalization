import PfaffianDescent.VoisinGenericPullbackCoordinates
import PfaffianDescent.AffineFreeModuleBaseChange

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual pulled section coordinates at a split field component are obtained
by the SAME coordinate-ring map, normalized by the native GammaSpec maps. -/
theorem pointSplitting_section_coordinate
    {A E : Type u} [CommRing A] [Field E]
    (α : A →+* E) (I : Type u) [Fintype I] [DecidableEq I]
    (M : (Spec (.of A)).Modules)
    (e : SheafOfModules.free (R := (Spec (.of A)).ringCatSheaf) I ≅ M)
    (s : M.sections) (i : I) :
    (Scheme.ΓSpecIso (.of E)).hom.hom
      (moduleOpenTopLinearEquivOfFreeIso I
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom α))).obj M)
        (pullbackFreeIso (Spec.map (CommRingCat.ofHom α)) I e)
        ((pullbackSection (Spec.map (CommRingCat.ofHom α)) M
          (isIso_pullbackUnitComparison _) s).val (op ⊤)) i) =
    α ((Scheme.ΓSpecIso (.of A)).hom.hom
      (moduleOpenTopLinearEquivOfFreeIso I M e (s.val (op ⊤)) i)) := by
  let f := Spec.map (CommRingCat.ofHom α)
  have h := moduleOpenTopLinearEquivOfPullbackFreeIso_general f I M e
    (s.val (op ⊤)) i
  have hs : (schemeModuleSectionsEquivTop M).symm (s.val (op ⊤)) = s :=
    (schemeModuleSectionsEquivTop M).symm_apply_apply s
  dsimp only at h
  rw [hs] at h
  change (Scheme.ΓSpecIso (.of E)).hom.hom
      (moduleOpenTopLinearEquivOfFreeIso I ((Scheme.Modules.pullback f).obj M)
        (pullbackFreeIso f I e)
        (schemeModuleSectionsEquivTop _ (pullbackSection f M
          (isIso_pullbackUnitComparison _) s)) i) = _
  rw [h]
  exact congrArg (fun m : Γ(Spec (.of A), ⊤) ⟶ CommRingCat.of E =>
    m.hom (moduleOpenTopLinearEquivOfFreeIso I M e (s.val (op ⊤)) i))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom α))

end PfaffianDescent
