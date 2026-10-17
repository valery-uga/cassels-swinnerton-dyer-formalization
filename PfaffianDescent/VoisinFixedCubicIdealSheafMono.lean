import PfaffianDescent.ProjectiveChartRelativeIdealSheafMono
import PfaffianDescent.VoisinFixedCubicCoordinateFlat

/-!
# Actual fixed-cubic moving-divisor chart ideals under parameter change

At a local parameter point where the residual moving cubic is regular,
the actual affine ideal sheaf of the moving divisor remains embedded under
every further change of parameters.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem fixedCubicIntersectionChart_idealPullback_mono_of_residue_regular
    {K T S : Type u} [Field K] [CommRing T] [Algebra K T]
    [IsLocalRing T] [CommRing S]
    (f : T →+* S)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) T) (hp : p.IsHomogeneous 3)
    (hreg : IsRegular (Ideal.Quotient.mk
      (equationIdeal (a.map (algebraMap K (IsLocalRing.ResidueField T)))
        (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal
      (p.map (algebraMap T (IsLocalRing.ResidueField T)))))
    (j : Fin 4) :
    let J := equationIdeal (a.map (algebraMap K T))
      (ha.map (algebraMap K T))
    let hIJ : J.toIdeal ≤ (J ⊔ equationIdeal p hp).toIdeal := by
      rw [HomogeneousIdeal.toIdeal_sup]
      exact le_sup_left
    let C := coefficientChangedHomogeneousIdeal f J
    let g := chartCoefficientMap f J C
      (coefficientChangedHomogeneousIdeal_toIdeal f J) j
    let Q := RingHom.ker (chartQuotientMap J
      (J ⊔ equationIdeal p hp) hIJ j)
    Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q))))) := by
  let J := equationIdeal (a.map (algebraMap K T))
    (ha.map (algebraMap K T))
  let hIJ : J.toIdeal ≤ (J ⊔ equationIdeal p hp).toIdeal := by
    rw [HomogeneousIdeal.toIdeal_sup]
    exact le_sup_left
  exact chartQuotientMap_idealPullback_mono_of_flat f J
    (J ⊔ equationIdeal p hp) hIJ j
    (fixedCubicIntersectionChart_flat_of_residue_regular a ha p hp hreg j)

end PfaffianDescent
