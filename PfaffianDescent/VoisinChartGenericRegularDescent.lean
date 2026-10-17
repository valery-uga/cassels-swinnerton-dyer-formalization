import PfaffianDescent.RegularDescentFromGenericFibre
import PfaffianDescent.VoisinChartDirectSystem
import AllCharacteristics.ProjectiveChartBaseChange
import PfaffianDescent.VoisinCubicSurfaceChartRegular

/-!
# Regularity descent on actual projective coordinate charts

For a flat homogeneous coordinate algebra, coefficient extension along an
injective map embeds every actual affine projective chart. Consequently a
regular equation on the changed chart was regular before base change.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type u} [CommRing R] [CommRing S]
variable (f : R →+* S) (hf : Function.Injective f)
variable (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
variable (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
variable (hmap : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal)
variable [Module.Flat R (CoordinateRing I)]

include hf hmap in

/-- A flat projective chart embeds into its coefficient-changed chart when
the coefficient map is injective. -/
theorem chartCoefficientMap_injective_of_coordinateRing_flat (j : Fin 4) :
    Function.Injective (chartCoefficientMap f I J hmap j) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : Module.Flat R (ChartRing I j) :=
    chartRing_flat_of_coordinateRing_flat I j
  exact injective_of_flat_pushout
    (chartCoefficientMap f I J hmap j) (chartBaseMap J j)
    (isPushout_chartCoefficientMap f I J hmap j) hf

include hf hmap in
/-- A regular section on a changed projective chart was regular on the
original chart if the homogeneous coordinate algebra is flat. -/
theorem chartSection_regular_of_baseChange_regular
    (j : Fin 4) (x : ChartRing I j)
    (hx : IsRegular (chartCoefficientMap f I J hmap j x)) :
    IsRegular x :=
  isRegular_of_injective_ringHom _
    (chartCoefficientMap_injective_of_coordinateRing_flat f hf I J hmap j) x hx

include hf in
/-- Generic-fibre regularity of a moving cubic descends to its normalized
evaluation on every actual projective chart of a flat fixed-cubic family. -/
theorem cubicChartEvaluation_regular_of_baseChange_regular
    (a p : MvPolynomial (Fin 4) R)
    (ha : a.IsHomogeneous 3) (hp : p.IsHomogeneous 3)
    [Module.Flat R (CoordinateRing (equationIdeal a ha))]
    (j : Fin 4)
    (hreg : IsRegular
      ((p.map f).eval₂
        (chartBaseMap (equationIdeal (a.map f) (ha.map f)) j)
        (chartCoordinate (equationIdeal (a.map f) (ha.map f)) j))) :
    IsRegular (p.eval₂
      (chartBaseMap (equationIdeal a ha) j)
      (chartCoordinate (equationIdeal a ha) j)) := by
  apply chartSection_regular_of_baseChange_regular f hf
    (equationIdeal a ha) (equationIdeal (a.map f) (ha.map f))
    (equationIdeal_map f a ha) j
  simpa only [chartCoefficientMap_eval] using hreg

/-- The field-point chart regularity statement supplies the regularity
input for descent from the generic field to a total-space chart. -/
theorem cubicChartEvaluation_regular_of_genericField_regular
    {F : Type u} [Field F]
    (g : R →+* F) (hg : Function.Injective g)
    (a p : MvPolynomial (Fin 4) R)
    (ha : a.IsHomogeneous 3) (hp : p.IsHomogeneous 3)
    [Module.Flat R (CoordinateRing (equationIdeal a ha))]
    (j : Fin 4)
    (hreg : IsRegular
      (normalizedCubicSection (a.map g) (ha.map g) (p.map g) (hp.map g) j)) :
    IsRegular (p.eval₂
      (chartBaseMap (equationIdeal a ha) j)
      (chartCoordinate (equationIdeal a ha) j)) := by
  apply cubicChartEvaluation_regular_of_baseChange_regular g hg a p ha hp j
  rw [eval₂_chartCoordinate_eq_fraction
    (equationIdeal (a.map g) (ha.map g)) j (p.map g) (hp.map g)]
  exact hreg

end PfaffianDescent
