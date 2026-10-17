import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridAffineCoordinates
import PfaffianDescent.VoisinPulledChartEquationVanishing

/-! # Native normalized coordinates and equation on the selected grid chart -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient map of every actual ordered chart coordinate is the
coefficient map of the ordered configuration itself. -/
theorem voisinDegreeTenSelectedAvoidance_orderedChartLift_baseMap
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (n : ℕ) (U : Scheme.{u})
    (i : U ⟶ (orderedFamilyConfigurationOver (toBase I) n).left)
    (t : Fin n → (U ⟶ Spec (.of (Away (grading I) (coordinate I 0)))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading I) (coordinate I 0)
        (coordinate_mem I 0) (by decide : 0 < 1) =
      (i ≫ Over.Hom.left (orderedFamilyConfigurationι (toBase I) n)) ≫
        (orderedFamilyCoordinate (toBase I) n k).left)
    (k : Fin n) :
    t k ≫ Spec.map (CommRingCat.ofHom
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := coordinate I 0))) =
      i ≫ (orderedFamilyConfigurationOver (toBase I) n).hom := by
  let q := Proj.awayι (grading I) (coordinate I 0) (coordinate_mem I 0)
    (by decide : 0 < 1)
  let cfg := orderedFamilyConfigurationι (toBase I) n
  let pr := orderedFamilyCoordinate (toBase I) n k
  have hq := homogeneousChart_toBase I (coordinate I 0) (coordinate_mem I 0)
    (by decide : 0 < 1)
  have hpr := orderedFamilyCoordinate_toBase (toBase I) n k
  calc
    t k ≫ Spec.map (CommRingCat.ofHom
      (AllCharacteristics.GradedChart.baseMap (grading I) (z := coordinate I 0))) =
        (t k ≫ q) ≫ toBase I := by
          rw [← hq]
          exact (Category.assoc _ _ _).symm
    _ = ((i ≫ cfg.left) ≫ pr.left) ≫ toBase I := by
      exact congrArg (fun v : U ⟶ Proj (grading I) => v ≫ toBase I) (ht k)
    _ = i ≫ (orderedFamilyConfigurationOver (toBase I) n).hom := by
      rw [Category.assoc (i ≫ cfg.left) pr.left (toBase I), hpr]
      simpa only [Category.assoc] using (congrArg (fun v => i ≫ v) cfg.w)

set_option backward.isDefEq.respectTransparency false in
/-- The native pulled coordinate at the chart denominator is literally one. -/
theorem voisinDegreeTenSelectedAvoidance_pulled_coordinate_zero_one
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (U : Scheme.{u})
    (t : U ⟶ Spec (.of (Away (grading I) (coordinate I 0)))) :
    pulledLinearChartCoordinate I (coordinate I 0) (coordinate_mem I 0) U t 0 = 1 := by
  change affineFunctionHom t (linearChartCoordinate I (coordinate I 0) (coordinate_mem I 0) 0) = 1
  unfold linearChartCoordinate
  rw [AllCharacteristics.GradedChart.normalized_self, map_one]

set_option backward.isDefEq.respectTransparency false in
/-- The original defining cubic vanishes on all actual pulled vectors,
using the actual configuration coefficient map. -/
theorem voisinDegreeTenSelectedAvoidance_pulled_cubic_equation_zero
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (U : Scheme.{u})
    (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
    (t : Fin n → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
      (coordinate (equationIdeal p hp) 0)))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
        (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0)
        (by decide : 0 < 1) =
      (i ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) n k).left)
    (k : Fin n) :
    (p.map (voisinDegreeTenSelectedAvoidance_affineBaseRingMap U
      (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom))).eval
      (fun z => pulledLinearChartCoordinate (equationIdeal p hp)
        (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0) U (t k) z) = 0 := by
  change (p.map (affineFunctionHom
    (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom))).eval _ = 0
  apply pulledLinearChartCoordinate_equation_zero (equationIdeal p hp)
    (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0) U (t k)
    (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom)
    (voisinDegreeTenSelectedAvoidance_orderedChartLift_baseMap (equationIdeal p hp) n U i t ht k) p hp
  exact Ideal.mem_span_singleton_self p

end PfaffianDescent
