import PfaffianDescent.RegularSurfacePointExtCoordinate
import AllCharacteristics.ProjectiveHypersurfaceClosedDimension
import AllCharacteristics.SmoothSchemeRegularity

/-!
# Field-point Ext coordinates on an actual smooth cubic surface

Smoothness supplies regular local rings and local noetherianity, and the
projective chart calculation supplies dimension two. The affine Koszul
parameters and quotient-stalk coordinate are constructed internally.
-/

noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-two Ext group of a twisted closed field point on a smooth
cubic surface has a field-valued coordinate with its geometric inputs proved. -/
noncomputable def fieldPointExtTwoCoordinateAddEquivOfSmoothCubicSurface
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [IsClosedImmersion i]
    (T : (hypersurface p hp).Modules) {J : Type u}
    (V : J → (hypersurface p hp).Opens)
    (hV : (Opens.grothendieckTopology (hypersurface p hp)).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor (hypersurface p hp).ringCatSheaf (V j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver (hypersurface p hp).sheaf (V j))))
    [HasExt.{u} (hypersurface p hp).Modules]
    [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))] :
    Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      (show (hypersurface p hp).Modules from
        SheafOfModules.unit (hypersurface p hp).ringCatSheaf) 2 ≃+ L := by
  let S := hypersurface p hp
  let f := hypersurfaceToBase p hp
  letI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian f
  letI : IsRegularRing Γ(Spec (.of K), ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  letI : IsRegularLocalRing (S.presheaf.stalk (i default)) :=
    AllCharacteristics.isRegularLocalRing_stalk_of_smooth_over_affine f (i default)
  have hclosed : IsClosed ({i default} : Set S) := by
    have hrange : Set.range i = {i default} := by
      ext x
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨y, rfl⟩
        congr 1
        exact Subsingleton.elim _ _
      · rintro rfl
        exact ⟨default, rfl⟩
    rw [← hrange]
    exact i.isClosedEmbedding.isClosed_range
  exact fieldPointExtTwoCoordinateAddEquivOfRegularSurfacePoint i
    (ringKrullDim_stalk_projective_hypersurface_eq_two p hp hp0 (i default) hclosed)
    T V hV eV
end PfaffianDescent
