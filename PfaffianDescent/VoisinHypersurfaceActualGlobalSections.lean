import PfaffianDescent.VoisinHypersurfaceGlobalSections
import PfaffianDescent.VoisinHypersurfaceCokernel
import PfaffianDescent.VoisinCubicSurfaceVanishing
import PfaffianDescent.SchemePushforwardUnitSections

/-!
# Global sections of the actual cubic hypersurface

The canonical cokernel of multiplication by a cubic is already identified with
the pushforward of the cubic hypersurface's structure sheaf. This file applies
the projective-space negative-twist vanishings directly to the resulting
geometric restriction sequence.
-/

noncomputable section

namespace PfaffianDescent.ProjectiveNegativeTwist

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective

universe u

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

private theorem unitToPushforward_sections_top
    {X Z : Scheme.{u}} (i : Z ⟶ X)
    (s : (SheafOfModules.unit X.ringCatSheaf).sections) :
    pushforwardUnitSectionsEquiv i
      (SheafOfModules.sectionsMap
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) s) =
      i.appTop.hom
        (moduleSectionsEquivTop X
          (SheafOfModules.unit X.ringCatSheaf) s) := by
  let M := SheafOfModules.unit Z.ringCatSheaf
  let N := (Scheme.Modules.pushforward i).obj M
  let eX := moduleSectionsEquivTop X N
  let eZ := moduleSectionsEquivTop Z M
  have hpush (t : N.sections) :
      pushforwardUnitSectionsEquiv i t = eX t := by
    change eZ (eZ.symm (eX t)) = eX t
    exact eZ.apply_symm_apply (eX t)
  rw [hpush]
  change (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i).val.app
      (.op ⊤) (s.val (.op ⊤)) = i.appTop.hom (s.val (.op ⊤))
  exact SheafOfModules.unitToPushforwardObjUnit_val_app_apply
    i.toRingCatSheafHom (X := .op ⊤) (s.val (.op ⊤))

/-- For an integral cubic hypersurface in projective three-space, ambient
global functions restrict bijectively to sections of its actual
pushed-forward structure sheaf. -/
theorem p3_cubicPushforward_sectionsMap_bijective
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))] :
    Function.Bijective (SheafOfModules.sectionsMap
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (hypersurfaceToAmbient p hp))) := by
  letI : Subsingleton (sheafOfModules PS 3).sections :=
    p3_negativeTwist_sections_subsingleton_of_pos K 3 (by decide)
  letI : Subsingleton (schemeModuleCohomology (Proj PS)
      (sheafOfModules PS 3) 1) :=
    (p3_negativeTwist_cohomology_one_and_two_subsingleton K 3).1
  letI : Subsingleton (hypersurfaceRestrictionSequence p hp).X₁.sections := by
    change Subsingleton (sheafOfModules PS (0 + 3)).sections
    simpa only [zero_add] using
      (inferInstance : Subsingleton (sheafOfModules PS 3).sections)
  letI : Subsingleton (Ext.{u}
      (SheafOfModules.unit (Proj PS).ringCatSheaf)
      (hypersurfaceRestrictionSequence p hp).X₁ 1) := by
    change Subsingleton (schemeModuleCohomology (Proj PS)
      (sheafOfModules PS (0 + 3)) 1)
    simpa only [zero_add] using
      (inferInstance : Subsingleton (schemeModuleCohomology (Proj PS)
        (sheafOfModules PS 3) 1))
  exact sectionsMap_bijective_of_shortExact_of_left_h0_h1_vanish
    (hypersurfaceRestrictionSequence p hp)
    (hypersurfaceRestrictionSequence_shortExact p hp hp0)

/-- Smoothness supplies the coordinate-domain hypothesis of the geometric
cubic restriction theorem. -/
theorem p3_smoothCubicPushforward_sectionsMap_bijective
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    Function.Bijective (SheafOfModules.sectionsMap
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (hypersurfaceToAmbient p hp))) := by
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) :=
    smoothCubic_coordinateRing_isDomain K p hp hp0
  exact p3_cubicPushforward_sectionsMap_bijective K p hp hp0

/-- Restriction of ordinary global functions from projective three-space
to an integral cubic hypersurface is a bijection. -/
theorem p3_cubicGlobalFunctions_restriction_bijective
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))] :
    Function.Bijective (hypersurfaceToAmbient p hp).appTop.hom := by
  let i := hypersurfaceToAmbient p hp
  let A := SheafOfModules.unit (Proj PS).ringCatSheaf
  let eA := moduleSectionsEquivTop (Proj PS) A
  let eS := pushforwardUnitSectionsEquiv i
  let f := SheafOfModules.sectionsMap
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)
  have hf : Function.Bijective f :=
    p3_cubicPushforward_sectionsMap_bijective K p hp hp0
  have hcompat (s : A.sections) :
      eS (f s) = i.appTop.hom (eA s) :=
    unitToPushforward_sections_top i s
  constructor
  · intro a b hab
    obtain ⟨s, rfl⟩ := eA.surjective a
    obtain ⟨t, rfl⟩ := eA.surjective b
    apply congrArg eA
    apply hf.1
    apply eS.injective
    rw [hcompat s, hcompat t]
    exact hab
  · intro z
    obtain ⟨y, rfl⟩ := eS.surjective z
    obtain ⟨s, hs⟩ := hf.2 y
    refine ⟨eA s, ?_⟩
    rw [← hcompat s, hs]

/-- The same ordinary-global-function statement for a smooth cubic. -/
theorem p3_smoothCubicGlobalFunctions_restriction_bijective
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf)]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    Function.Bijective (hypersurfaceToAmbient p hp).appTop.hom := by
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) :=
    smoothCubic_coordinateRing_isDomain K p hp hp0
  exact p3_cubicGlobalFunctions_restriction_bijective K p hp hp0

end PfaffianDescent.ProjectiveNegativeTwist
