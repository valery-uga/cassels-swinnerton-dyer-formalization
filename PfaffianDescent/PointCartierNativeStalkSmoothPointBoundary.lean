import PfaffianDescent.PointCartierNativeStalkBoundaryNonzero
import PfaffianDescent.PointCartierNativeStalkResidueNonzero
import PfaffianDescent.CubicPointCompatibleNegativeTwistCoordinate

/-! # The actual Cartier boundary detects every nonzero smooth cubic point class

The regular pair, endpoint coordinates, and chart are all constructed by the
existing actual residue coordinate. No sequence or trace square is an input.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent.ProjectiveNegativeTwist

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective MvPolynomial

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

theorem pointCartierNativeStalkSmoothPoint_boundary_ne_zero
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExtSurface : HasExt.{u} (hypersurface p hp).Modules]
    [hExtLocalAmbient : HasExt.{u + 1}
      (ModuleCat.{u} ((Proj PS).presheaf.stalk (hypersurfaceAmbientPoint p hp (i default))))]
    [hExtLocalSurface : HasExt.{u + 1}
      (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default)))]
    (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2) (hz : z ≠ 0) :
    (z.mapExactFunctor (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp))).comp
      (hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 1).extClass rfl ≠ 0 := by
  let e := cubicPointCompatibleNegativeTwistCoordinate K 1 p hp hp0 i
  let d := Classical.choice
    (cubicPointCompatibleNegativeTwistCoordinate_residuePresentation K 1 p hp hp0 i)
  have hez : e z ≠ 0 := by
    intro hzero
    apply hz
    apply e.injective
    simpa only [map_zero] using hzero
  have hlocal := pointCartierNativeStalkResidue_local_ne_zero i default _ _ e d z hez
  have hcover : hypersurfaceAmbientPoint p hp (i default) ∈
      ⨆ j : Fin 4, p3StandardOpen (K := K) j := by
    rw [p3StandardOpen_iSup]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hcover
  have hx : X j ∉ (hypersurfaceAmbientPoint p hp (i default)).asHomogeneousIdeal.toIdeal :=
    (ProjectiveSpectrum.mem_basicOpen PS (X j) _).mp hj
  letI : EnoughInjectives (hypersurface p hp).Modules :=
    sheafOfModules_enoughInjectives (hypersurface p hp).ringCatSheaf
  exact pointCartierNativeStalkHypersurface_boundary_ne_zero_of_local p hp hp0
    (i default) j hx _ d.f d.g d.hf d.hg d.qM d.qN z hlocal

end PfaffianDescent.ProjectiveNegativeTwist
