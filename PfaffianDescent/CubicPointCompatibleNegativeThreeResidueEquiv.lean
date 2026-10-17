import PfaffianDescent.CubicPointCompatibleQuadraticResidue
import PfaffianDescent.CubicPointCompatibleNegativeTwistCoordinate
import PfaffianDescent.FieldPointResidueStalkEquiv

/-! # The compatible negative-three point residue is an equivalence

An independently constructed smooth-point residue coordinate proves that the
actual global-to-stalk Ext map is bijective. The equivalence below then uses
the original canonical source parameters and the original negative-three
coefficient coordinate, so its forward map is exactly the existing raw residue.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The actual point Ext comparison to the stalk is bijective for every
negative twist on a smooth cubic. -/
theorem cubicPointCompatibleNegativeTwist_stalkMap_bijective
    (m : ℕ) (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [hClosed : IsClosedImmersion i]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))] :
    Function.Bijective (schemeModuleStalkModuleExtMap (hypersurface p hp) (i default)
      (closedImmersionIdealTwistSequence i
        (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) m) 2) := by
  let e := cubicPointCompatibleNegativeTwistCoordinate K m p hp hp0 i
  let d := Classical.choice
    (cubicPointCompatibleNegativeTwistCoordinate_residuePresentation K m p hp hp0 i)
  exact fieldPointStalkExtMap_bijective_of_residuePresentation i default _ e d

set_option backward.isDefEq.respectTransparency false in
/-- The original raw negative-three residue, upgraded to an additive
equivalence using its unchanged canonical source presentation. -/
def cubicPointCompatibleNegativeThreeResidueEquiv
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [hClosed : IsClosedImmersion i]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))] :
    Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 3) 2 ≃+ L := by
  let d := cubicPointCompatibleResiduePresentation K p hp hp0 i
  exact fieldPointExtTwoCoordinateAddEquiv i default _ _ d.f d.g d.hf d.hg d.hfm d.hgm
    d.qM (cubicPointCompatibleNegativeTwistStalkIso K p hp i 3)
    (d.span_eq_maximalIdeal_of_unit_source i default _ _)
    (cubicPointCompatibleNegativeTwist_stalkMap_bijective K 3 p hp hp0 i)

/-- The upgraded equivalence has exactly the original raw residue as its
forward map, with no parameter or coefficient-coordinate change. -/
@[simp] theorem cubicPointCompatibleNegativeThreeResidueEquiv_apply
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [hClosed : IsClosedImmersion i]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))]
    (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 3) 2) :
    cubicPointCompatibleNegativeThreeResidueEquiv K p hp hp0 i z =
      cubicPointCompatibleNegativeThreeResidue K p hp hp0 i z := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Bijectivity of the original raw negative-three residue follows without
any assumption on the geometric trace coefficient. -/
theorem cubicPointCompatibleNegativeThreeResidue_bijective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [hClosed : IsClosedImmersion i]
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))] :
    Function.Bijective (cubicPointCompatibleNegativeThreeResidue K p hp hp0 i) :=
  (@cubicPointCompatibleNegativeThreeResidueEquiv K _ p hp hp0 hSmooth L _ i
    hClosed hExt hExtStalk).bijective

end PfaffianDescent.ProjectiveNegativeTwist
