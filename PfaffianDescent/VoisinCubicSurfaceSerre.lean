import PfaffianDescent.VoisinCubicSurfaceVanishing
import PfaffianDescent.SerreExtensionFoundation

/-! # The cubic-surface cohomology input for Voisin's Serre pencil -/

noncomputable section

namespace PfaffianDescent.ProjectiveNegativeTwist

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective

universe u

variable (K : Type u) [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The proved cubic-surface structure-sheaf vanishing is exactly the
`Ext¹(O_S,O_S)` input needed to lift quotient sections in Voisin's Serre
construction. -/
theorem cubicSurface_structure_ext_one_subsingleton
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (hypersurface p hp).Modules] :
    Subsingleton (Ext.{u}
      (show (hypersurface p hp).Modules from
        SheafOfModules.unit (hypersurface p hp).ringCatSheaf)
      (show (hypersurface p hp).Modules from
        SheafOfModules.unit (hypersurface p hp).ringCatSheaf) 1) := by
  exact cubicSurface_structure_cohomology_one K p hp hp0

/-- Any nonzero quotient section in a Serre extension on the cubic surface
therefore yields the two-section seed used for Voisin's moving pencil. -/
theorem nonempty_serreExtensionPencilSeed_of_cubicSurface
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (hypersurface p hp).Modules]
    {M : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) M)
    (t : M.sections) (ht : t ≠ SerreExtensionData.zeroSection M) :
    Nonempty (SerreExtensionData.SerreExtensionPencilSeed e) := by
  exact @SerreExtensionData.nonempty_serreExtensionPencilSeed_of_ext_one_subsingleton
    (hypersurface p hp) M e
    (show HasExt.{u} (SheafOfModules.{u} (hypersurface p hp).ringCatSheaf)
      from ‹HasExt.{u} (hypersurface p hp).Modules›)
    (cubicSurface_structure_cohomology_one K p hp hp0) t ht

/-- On a smooth cubic surface, the Ext¹ vanishing required to lift quotient
sections follows with no separate coordinate-ring domain hypothesis. -/
theorem cubicSurface_structure_ext_one_subsingleton_of_smooth
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (hypersurface p hp).Modules] :
    Subsingleton (Ext.{u}
      (show (hypersurface p hp).Modules from
        SheafOfModules.unit (hypersurface p hp).ringCatSheaf)
      (show (hypersurface p hp).Modules from
        SheafOfModules.unit (hypersurface p hp).ringCatSheaf) 1) := by
  exact cubicSurface_structure_cohomology_one_of_smooth K p hp hp0

/-- A nonzero quotient section in a Serre extension on a smooth cubic yields
the two-section pencil seed used by Voisin, with all surface cohomology
conditions discharged internally. -/
theorem nonempty_serreExtensionPencilSeed_of_smooth_cubicSurface
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (hypersurface p hp).Modules]
    {M : (hypersurface p hp).Modules}
    (e : SerreExtensionData (hypersurface p hp) M)
    (t : M.sections) (ht : t ≠ SerreExtensionData.zeroSection M) :
    Nonempty (SerreExtensionData.SerreExtensionPencilSeed e) := by
  exact @SerreExtensionData.nonempty_serreExtensionPencilSeed_of_ext_one_subsingleton
    (hypersurface p hp) M e
    (show HasExt.{u} (SheafOfModules.{u} (hypersurface p hp).ringCatSheaf)
      from ‹HasExt.{u} (hypersurface p hp).Modules›)
    (cubicSurface_structure_cohomology_one_of_smooth K p hp hp0) t ht

end PfaffianDescent.ProjectiveNegativeTwist
