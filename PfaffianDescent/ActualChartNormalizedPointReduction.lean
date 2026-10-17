import PfaffianDescent.LinearNormalizedProjectivePoint
import AllCharacteristics.ProjectivePointCoordinates

/-! Normalized coordinates and residue reduction recover the original chart
point itself. This comparison keeps a constructed tangent jet attached to
its original closed point. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[irreducible]
def actualChart_normalizedPoint_reduction
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (i : Spec (.of L) ⟶ scheme I)
    (j : Fin 4) (g : ChartRing I j →+* L)
    (hbase : g.comp (chartBaseMap I j) = algebraMap K L)
    (hpoint : Spec.map (CommRingCat.ofHom g) ≫ chartι I j = i)
    (y : Fin 4 → A)
    (he : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K A) y = 0)
    (hy : y j = 1)
    (φ : A →ₐ[K] L)
    (hred : ∀ a, φ (y a) = g (chartCoordinate I j a)) :
    let hzA : (Ideal.Quotient.lift I.toIdeal
        (eval₂Hom (algebraMap K A) y) he) (coordinate I j) = 1 := by
      simpa only [coordinate, Ideal.Quotient.lift_mk, eval₂Hom_X'] using hy
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      linearNormalizedPointAt I y he (coordinate I j) (coordinate_mem I j) hzA = i :=
  let b : Fin 4 → L := fun a => g (chartCoordinate I j a)
  let heL : ∀ p ∈ I.toIdeal, p.eval₂ (algebraMap K L) b = 0 := by
    intro p hp
    have h := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j p hp)
    rw [hom_eval₂, hbase, map_zero] at h
    exact h
  let hzA : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K A) y) he) (coordinate I j) = 1 := by
    simpa only [coordinate, Ideal.Quotient.lift_mk, eval₂Hom_X'] using hy
  let hzL : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K L) b) heL) (coordinate I j) = 1 := by
    simpa only [coordinate, Ideal.Quotient.lift_mk, eval₂Hom_X'] using
      (congrArg g (chartCoordinate_self I j)).trans (map_one g)
  let hg : g = linearNormalizedPointChartMapAt I b heL
      (coordinate I j) (coordinate_mem I j) hzL :=
    linearNormalizedPointChartMapAt_eq_of_base_and_coordinates
      I b heL (coordinate I j) (coordinate_mem I j) hzL g hbase
      (by intro a; simp only [b, linearChartCoordinate, chartCoordinate])
  let hn := linearNormalizedPointAt_naturality I y he φ b
    (fun a => (hred a).symm) heL (coordinate I j) (coordinate_mem I j) hzA hzL
  let hp : linearNormalizedPointAt I b heL
      (coordinate I j) (coordinate_mem I j) hzL = i := by
    change Spec.map (CommRingCat.ofHom (linearNormalizedPointChartMapAt
      I b heL (coordinate I j) (coordinate_mem I j) hzL)) ≫ chartι I j = i
    rw [← hg]
    exact hpoint
  hn.symm.trans hp

end PfaffianDescent
