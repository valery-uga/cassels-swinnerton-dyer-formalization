import PfaffianDescent.ActualCubicGlobalChartPointDifferentialFiber
import PfaffianDescent.SmoothCubicActualKaehlerChartFiberDimension
import AllCharacteristics.ProjectivePointCoordinates

/- SOURCE ONLY / UNVERIFIED. The genuinely constructed global relative
Ω of the SAME smooth cubic has dimension-two fiber at EVERY original
field-valued point. Its chart is selected and compared internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- Original q is retained exactly. No degree, perfectness, chosen chart,
nonzero-gradient, rank or comparison certificate is an extra premise. -/
theorem smoothCubic_originalPointDifferentialFiber_finrank_two
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (q : Spec (CommRingCat.of L) ⟶ hypersurface p hp)
    (hq : q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    Module.finrank L ((moduleSpecΓFunctor (R := CommRingCat.of L)).obj
      ((Scheme.Modules.pullback q).obj
        (schemeRelativeDifferentials (hypersurfaceToBase p hp)))) = 2 := by
  let I := equationIdeal p hp
  obtain ⟨j, ρ, hρ, hfac⟩ :=
    exists_chart_hom_eq_of_point I (algebraMap K L) q hq
  rw [← hfac]
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : Algebra (ChartRing I j) L := ρ.toAlgebra
  rw [(actualCubicGlobalChartPointDifferentialFiberEquiv p hp j ρ).finrank_eq]
  exact smoothCubic_actualKaehlerChartFiber_finrank_two p hp hp0 j ρ

end PfaffianDescent
