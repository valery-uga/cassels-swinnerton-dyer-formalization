import AllCharacteristics.PowerSeriesPencilSpecifiedPoint
import AllCharacteristics.ProjectiveUnitCoefficientFlatness

/-! SOURCE ONLY / UNVERIFIED. The actual pencil is flat from the nonzero
original equation. This removes flatness as a proposed certificate in the
remaining pointwise special-fiber smoothness transfer. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry HomogeneousProjective
universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem prescribedPowerSeriesPencil_flat
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3)
    (hp0 : p ≠ 0) :
    Flat (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
      (prescribedPowerSeriesPencil_homogeneous hp hg)) := by
  obtain ⟨m, hm⟩ := MvPolynomial.exists_coeff_ne_zero hp0
  apply flat_hypersurfaceToBase_of_isUnit_coeff _ _ m
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  have hcoeff : PowerSeries.constantCoeff
      ((prescribedPowerSeriesPencil p g).coeff m) = p.coeff m := by
    have h := congrArg (MvPolynomial.coeff m)
      (prescribedPowerSeriesPencil_constantCoeff p g)
    simpa only [MvPolynomial.coeff_map] using h
  rw [hcoeff]
  exact isUnit_iff_ne_zero.mpr hm

end AllCharacteristics
