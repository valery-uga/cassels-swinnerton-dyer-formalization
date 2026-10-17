import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNativeKernelSections
import PfaffianDescent.SchemeModuleGlobalSectionsTop

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
open IdealSheafDataModule BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual global sections at top correspond to actual morphisms from the unit. -/
def cubicClosedPointSerreSurfaceJetCotangent_sectionHomOfTop
    {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  M.unitHomEquiv.symm ((schemeModuleSectionsEquivTop M).symm s)

theorem cubicClosedPointSerreSurfaceJetCotangent_sectionHomOfTop_one
    {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) :
    (cubicClosedPointSerreSurfaceJetCotangent_sectionHomOfTop M s).val.app (op ⊤)
      (1 : Γ(X, ⊤)) = s := by
  let a := cubicClosedPointSerreSurfaceJetCotangent_sectionHomOfTop M s
  calc
    a.val.app (op ⊤) (1 : Γ(X, ⊤)) = (M.unitHomEquiv a).val (op ⊤) :=
      (SheafOfModules.unitHomEquiv_apply_coe M a (op ⊤)).symm
    _ = ((schemeModuleSectionsEquivTop M).symm s).val (op ⊤) :=
      congrArg (fun t => t.val (op ⊤)) (M.unitHomEquiv.apply_symm_apply _)
    _ = s := (schemeModuleSectionsEquivTop M).apply_symm_apply s

/-- The SAME native H global section, now as a literal actual module morphism. -/
def cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    (a : RingHom.ker g) :
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf ⟶
      closedImmersionModule (Spec.map (CommRingCat.ofHom g)) :=
  cubicClosedPointSerreSurfaceJetCotangent_sectionHomOfTop _
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealGlobalSectionsEquiv g a)

/-- Its actual inclusion is multiplication by the literal affine function a. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom_toUnit
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    (a : RingHom.ker g) :
    cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom g a ≫
      closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom g)) =
    unitEndomorphismOfRegularFunction (X := Spec (CommRingCat.of A))
      ((affineGlobalSectionsUnitLinearEquiv (A := A)).symm a.1) := by
  rw [← unitEndomorphismOfRegularFunction_value
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom g a ≫
      closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom g)))]
  congr 1
  unfold unitEndomorphismValue unitSectionAtTop
  change (closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom g))).val.app (op ⊤)
    ((cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom g a).val.app (op ⊤)
      (1 : Γ(Spec (CommRingCat.of A), ⊤))) = _
  have ht := cubicClosedPointSerreSurfaceJetCotangent_sectionHomOfTop_one
    (closedImmersionModule (Spec.map (CommRingCat.ofHom g)))
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealGlobalSectionsEquiv g a)
  exact (congrArg (fun x =>
    (closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom g))).val.app (op ⊤) x) ht).trans
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealGlobalSectionsEquiv_toUnit g a)

end PfaffianDescent
