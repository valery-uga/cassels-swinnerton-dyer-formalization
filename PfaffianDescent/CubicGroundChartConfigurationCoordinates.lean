import PfaffianDescent.CubicGroundChartConfigurationAffine
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridAffineCoordinates
import PfaffianDescent.VoisinPulledChartEquationVanishing

/-! Literal coefficients, equations and field values of actual ground-chart coordinates. -/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicGroundChart_orderedChartLift_baseMap
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (n : ℕ) (U : Scheme.{u})
    (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
    (t : Fin n → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
      (cubicGroundChartClass p hp c)))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
        (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c)
        (by decide : 0 < 1) =
      (i ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) n k).left)
    (k : Fin n) :
    t k ≫ Spec.map (CommRingCat.ofHom
      (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal p hp))
        (z := cubicGroundChartClass p hp c))) =
      i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom := by
  let I := equationIdeal p hp
  let z := cubicGroundChartClass p hp c
  let hz := cubicGroundChartClass_mem p hp c
  let chart := Proj.awayι (grading I) z hz (by decide : 0 < 1)
  let cfg := orderedFamilyConfigurationι (toBase I) n
  let pr := orderedFamilyCoordinate (toBase I) n k
  have hc := homogeneousChart_toBase I z hz (by decide : 0 < 1)
  have hpr := orderedFamilyCoordinate_toBase (toBase I) n k
  calc
    t k ≫ Spec.map (CommRingCat.ofHom
        (AllCharacteristics.GradedChart.baseMap (grading I) (z := z))) =
        (t k ≫ chart) ≫ toBase I := by
      rw [← hc]
      exact (Category.assoc _ _ _).symm
    _ = ((i ≫ cfg.left) ≫ pr.left) ≫ toBase I := by
      exact congrArg (fun q => q ≫ toBase I) (ht k)
    _ = i ≫ (orderedFamilyConfigurationOver (toBase I) n).hom := by
      rw [Category.assoc (i ≫ cfg.left) pr.left (toBase I), hpr]
      simpa only [Category.assoc] using congrArg (fun q => i ≫ q) cfg.w

theorem cubicGroundChart_pulled_equations
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (n : ℕ) (U : Scheme.{u})
    (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left)
    (t : Fin n → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
      (cubicGroundChartClass p hp c)))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
        (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c)
        (by decide : 0 < 1) =
      (i ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) n k).left)
    (k : Fin n) :
    let b := voisinDegreeTenSelectedAvoidance_affineBaseRingMap U
      (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom)
    let x := fun z => pulledLinearChartCoordinate (equationIdeal p hp)
      (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c) U (t k) z
    (p.map b).eval x = 0 ∧ ((homogeneousLinearForm c).map b).eval x = 1 := by
  constructor
  · change (p.map (affineFunctionHom
      (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom))).eval _ = 0
    apply pulledLinearChartCoordinate_equation_zero (equationIdeal p hp)
      (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c) U (t k)
      (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom)
      (cubicGroundChart_orderedChartLift_baseMap p hp c n U i t ht k) p hp
    exact Ideal.mem_span_singleton_self p
  · exact pulledLinearChartCoordinate_denominator_one (equationIdeal p hp) c U (t k)
      (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom)
      (cubicGroundChart_orderedChartLift_baseMap p hp c n U i t ht k)

theorem cubicGroundChart_fieldPointSpecialization_coordinate
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (v : Fin 4 → L)
    (hv : p.eval₂ (algebraMap K L) v = 0)
    (hc : (homogeneousLinearForm c).eval₂ (algebraMap K L) v ≠ 0)
    (U : Scheme.{u}) (a : Spec (.of L) ⟶ U)
    (t : U ⟶ Spec (.of (Away (grading (equationIdeal p hp)) (cubicGroundChartClass p hp c))))
    (hpoint : (a ≫ t) ≫ Proj.awayι (grading (equationIdeal p hp))
        (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c)
        (by decide : 0 < 1) = cubicExtensionVectorPointInGroundChart p hp c v hv hc)
    (j : Fin 4) :
    voisinDegreeTenSelectedAvoidance_fieldPointSpecialization a
      (pulledLinearChartCoordinate (equationIdeal p hp) (cubicGroundChartClass p hp c)
        (cubicGroundChartClass_mem p hp c) U t j) = cubicGroundChartNormalizedVector c v j := by
  change (Scheme.ΓSpecIso (.of L)).hom.hom (a.appTop.hom _) = _
  rw [pulledLinearChartCoordinate_value_of_normalizedPointAt (equationIdeal p hp)
    (cubicGroundChartClass p hp c) (cubicGroundChartClass_mem p hp c)
    (cubicGroundChartNormalizedVector c v) _ _ U a t hpoint j]
  exact (Scheme.ΓSpecIso (.of L)).inv_hom_id_apply _

end PfaffianDescent
