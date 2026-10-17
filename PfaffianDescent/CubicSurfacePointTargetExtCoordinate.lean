import PfaffianDescent.RegularSurfacePointTargetExtCoordinate
import PfaffianDescent.CubicSurfacePointExtCoordinate

/-! # Actual locally trivial target Ext coordinates on smooth cubic surfaces -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
/-- Smooth cubic geometry supplies the regularity and dimension needed for the
actual point Ext coordinate with a locally trivial coefficient target. -/
noncomputable def fieldPointExtTwoCoordinateAddEquivOfSmoothCubicSurfaceLocalTarget
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
    (Y : (hypersurface p hp).Modules)
    (eYV : ∀ j, Y.restrict (V j).ι ≅ SheafOfModules.unit (V j : Scheme).ringCatSheaf)
    [HasExt.{u} (hypersurface p hp).Modules]
    [HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))] :
    Ext.{u} (closedImmersionIdealTwistSequence i T).X₃
      Y 2 ≃+ L := by
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
  exact fieldPointExtTwoCoordinateAddEquivOfRegularSurfacePointLocalTarget i
    (ringKrullDim_stalk_projective_hypersurface_eq_two p hp hp0 (i default) hclosed)
    T V hV eV Y eYV

end PfaffianDescent
