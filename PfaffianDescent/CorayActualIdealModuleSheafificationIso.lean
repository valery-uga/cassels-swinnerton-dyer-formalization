import PfaffianDescent.CorayNativeIdealSheafificationMono
import PfaffianDescent.IdealSheafModule

noncomputable section
namespace PfaffianDescent.Coray
open CategoryTheory CategoryTheory.Limits
universe u
open AlgebraicGeometry IdealSheafDataModule
/-- The actual sheafification of the affine-local ideal subpresheaf embeds
into the original unit sheaf. No replacement for the original map is used. -/
theorem actualIdealModuleSheafToUnit_mono
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    Mono (moduleSheafToUnit I) := by
  exact nativeAssociatedSubpresheafToSheaf_mono X.ringCatSheaf
    (SheafOfModules.unit X.ringCatSheaf) (presheafSubmodule I)

/-- The existing factor through its actual image is an Iso. -/
theorem actualIdealModuleSheafToImage_isIso
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsIso (moduleSheafToIdealModule I) := by
  letI : Mono (moduleSheafToUnit I) := actualIdealModuleSheafToUnit_mono I
  change IsIso (Abelian.factorThruImage (moduleSheafToUnit I))
  letI : Mono (Abelian.factorThruImage (moduleSheafToUnit I)) := inferInstance
  letI : Epi (Abelian.factorThruImage (moduleSheafToUnit I)) := inferInstance
  exact isIso_of_mono_of_epi _

/-- Canonical elimination of the literal Abelian-image presentation,
using the SAME existing ideal module and original sheafification. -/
def actualIdealModuleSheafificationIso
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    idealModule I ≅ moduleSheaf I := by
  letI : IsIso (moduleSheafToIdealModule I) := actualIdealModuleSheafToImage_isIso I
  exact (asIso (moduleSheafToIdealModule I)).symm

/-- The canonical Iso retains the actual ideal inclusion into O_X. -/
theorem actualIdealModuleSheafificationIso_hom_toUnit
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    (actualIdealModuleSheafificationIso I).hom ≫ moduleSheafToUnit I =
      idealModuleToUnit I := by
  letI : IsIso (moduleSheafToIdealModule I) := actualIdealModuleSheafToImage_isIso I
  let e := asIso (moduleSheafToIdealModule I)
  change e.inv ≫ moduleSheafToUnit I = idealModuleToUnit I
  rw [← moduleSheafToIdealModule_comp]
  exact e.inv_hom_id_assoc _

end PfaffianDescent.Coray
