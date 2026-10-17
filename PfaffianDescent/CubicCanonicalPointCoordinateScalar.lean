import PfaffianDescent.CubicCanonicalPointResiduePresentation
import PfaffianDescent.CubicCanonicalCoefficientScalar

/-! # Ground-field scalar compatibility of the constructed canonical coordinate -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The internally constructed smooth cubic point coordinate respects the actual
ground-field coefficient action. No coordinate-compatibility premise is assumed. -/
theorem cubicCanonicalPointExtTwoCoordinate_postcomp_scalar
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hSmooth : Smooth (hypersurfaceToBase p hp)]
    {L : Type u} [Field L] [Algebra K L]
    (i : Spec (.of L) ⟶ hypersurface p hp) [hClosed : IsClosedImmersion i]
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    [hExt : HasExt.{u} (hypersurface p hp).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((hypersurface p hp).presheaf.stalk (i default)))]
    (c : K)
    (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2) :
    cubicCanonicalPointExtTwoCoordinate K p hp hp0 i
        (z.comp (Ext.mk₀ (C := (hypersurface p hp).Modules)
          (mulHomogeneous (grading (equationIdeal p hp))
            (cubicScalarHomogeneous K p hp c) 1)) (add_zero 2)) =
      algebraMap K L c * cubicCanonicalPointExtTwoCoordinate K p hp hp0 i z := by
  obtain ⟨d⟩ := cubicCanonicalPointExtTwoCoordinate_residuePresentation K p hp hp0 i
  have hs := @cubicCanonicalPointExtResidueCoordinate_scalar
    K _ p hp L _ _ i hClosed hi default hExt hExtStalk
    (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).X₃
    d.f d.g d.hf d.hg d.hfm d.hgm d.qM d.qN c z
  exact (d.coordinate_eq _).trans (hs.trans
    (congrArg (fun a : L => algebraMap K L c * a) (d.coordinate_eq z).symm))

end PfaffianDescent.ProjectiveNegativeTwist
