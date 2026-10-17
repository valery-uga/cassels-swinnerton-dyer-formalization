import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridIntegralBase

/-! # The actual affine coefficient witness for cubic interpolation -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- Actual affine global functions, coefficient and specialization maps,
and sixteen universal normalized vectors. Their specialized cubic
restriction is surjective and the two original grid cubics give a finite
native specialization. All data are constructed from the smooth cubic
and absence of a ground-field point. -/
theorem voisinDegreeTenSelectedAvoidance_exists_sixteen_grid_affine_witness
    {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ (U : Scheme.{u}) (_ : IsAffine U) (_ : IsIntegral U)
      (i : U ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left)
      (a : Spec (.of L) ⟶ U)
      (t : Fin 16 → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
        (coordinate (equationIdeal p hp) 0)))))
      (b : K →+* Γ(U, ⊤)) (f : Γ(U, ⊤) →+* L)
      (x : Fin 16 → Fin 4 → Γ(U, ⊤)),
      IsOpenImmersion i ∧ _root_.IsDomain Γ(U, ⊤) ∧
      b = voisinDegreeTenSelectedAvoidance_affineBaseRingMap U
        (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).hom) ∧
      f = voisinDegreeTenSelectedAvoidance_fieldPointSpecialization a ∧
      x = (fun k z => pulledLinearChartCoordinate (equationIdeal p hp)
        (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0) U (t k) z) ∧
      f.comp b = algebraMap K L ∧
      (∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
          (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0)
          (by decide : 0 < 1) =
        (i ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 16)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 16 k).left) ∧
      (∀ k, x k 0 = 1) ∧
      (∀ k, (p.map b).eval (x k) = 0) ∧
      Function.Surjective
        (homogeneousSectionRestriction (K := L) (fun z k => f (x k z)) 3) ∧
      (∀ k, (((voisinDegreeTenSelectedAvoidance_gridCubic K 1).map b).map f).eval
          (fun z => f (x k z)) = 0) ∧
      (∀ k, (((voisinDegreeTenSelectedAvoidance_gridCubic K 2).map b).map f).eval
          (fun z => f (x k z)) = 0) ∧
      IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
        ((p.map b).map f)
        (((voisinDegreeTenSelectedAvoidance_gridCubic K 1).map b).map f)
        (((voisinDegreeTenSelectedAvoidance_gridCubic K 2).map b).map f)
        ((hp.map b).map f)
        (((voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 1).map b).map f)
        (((voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 2).map b).map f))) := by
  classical
  obtain ⟨v, hv0, hpv, A, _, hAbase, hAcoord, _, hcubic, hqzero, hrzero⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_sixteen_grid_original_configuration (L := L) p hp hno
  have hp0 := voisinDegreeTenSelectedAvoidance_cubic_ne_zero_of_no_section p hp hno
  obtain ⟨hOint, hBint⟩ :=
    voisinDegreeTenSelectedAvoidance_configuration_integral_of_fieldPoint p hp hp0 16 A
  letI : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).left := hOint
  letI : IsIntegral (cubicConfigurationBase p hp 16) := hBint
  obtain ⟨U, Q, hUa, _, i, _, _, a, t, hi, _, _, _, hUint, _, ha, _, _, _, ht, _⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_integral_affine_charts p hp 16 v hpv hv0 A hAcoord
  letI : IsIntegral U := hUint
  let b := voisinDegreeTenSelectedAvoidance_affineBaseRingMap U
    (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).hom)
  let f := voisinDegreeTenSelectedAvoidance_fieldPointSpecialization a
  let x : Fin 16 → Fin 4 → Γ(U, ⊤) := fun k z =>
    pulledLinearChartCoordinate (equationIdeal p hp)
      (coordinate (equationIdeal p hp) 0) (coordinate_mem (equationIdeal p hp) 0) U (t k) z
  have habase : a ≫ (i ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 16).hom) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    rw [← Category.assoc, ha]
    exact hAbase
  have hfb : f.comp b = algebraMap K L :=
    voisinDegreeTenSelectedAvoidance_fieldPointSpecialization_base U _ a habase
  have hfx (k : Fin 16) (z : Fin 4) : f (x k z) = v k z := by
    apply voisinDegreeTenSelectedAvoidance_fieldPointSpecialization_coordinate
      p hp (v k) (hpv k) (hv0 k) U a (t k)
    rw [Category.assoc, ht k]
    change ((a ≫ i) ≫ Over.Hom.left
      (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 16)) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 16 k).left = _
    rw [ha]
    exact hAcoord k
  have hqmap : (((voisinDegreeTenSelectedAvoidance_gridCubic K 1).map b).map f) =
      voisinDegreeTenSelectedAvoidance_gridCubic L 1 := by
    rw [MvPolynomial.map_map, hfb, voisinDegreeTenSelectedAvoidance_gridCubic_map]
  have hrmap : (((voisinDegreeTenSelectedAvoidance_gridCubic K 2).map b).map f) =
      voisinDegreeTenSelectedAvoidance_gridCubic L 2 := by
    rw [MvPolynomial.map_map, hfb, voisinDegreeTenSelectedAvoidance_gridCubic_map]
  have hideal : tripleCompleteIntersectionHomogeneousIdeal
      ((p.map b).map f)
      (((voisinDegreeTenSelectedAvoidance_gridCubic K 1).map b).map f)
      (((voisinDegreeTenSelectedAvoidance_gridCubic K 2).map b).map f)
      ((hp.map b).map f)
      (((voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 1).map b).map f)
      (((voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 2).map b).map f) =
      voisinDegreeTenSelectedAvoidance_gridIdeal (p.map (algebraMap K L)) (hp.map (algebraMap K L)) := by
    apply HomogeneousIdeal.ext
    change Ideal.span {((p.map b).map f),
      (((voisinDegreeTenSelectedAvoidance_gridCubic K 1).map b).map f),
      (((voisinDegreeTenSelectedAvoidance_gridCubic K 2).map b).map f)} = _
    rw [MvPolynomial.map_map, hfb, hqmap, hrmap]
    rfl
  refine ⟨U, hUa, hUint, i, a, t, b, f, x, hi, inferInstance, rfl, rfl, rfl,
    hfb, ht, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact voisinDegreeTenSelectedAvoidance_pulled_coordinate_zero_one (equationIdeal p hp) U (t k)
  · intro k
    exact voisinDegreeTenSelectedAvoidance_pulled_cubic_equation_zero p hp 16 U i t ht k
  · simpa only [hfx] using hcubic
  · intro k
    rw [hqmap]
    simp only [hfx]
    have hk := congrFun hqzero k
    rw [finite_product_evaluation_apply] at hk
    exact hk
  · intro k
    rw [hrmap]
    simp only [hfx]
    have hk := congrFun hrzero k
    rw [finite_product_evaluation_apply] at hk
    exact hk
  · rw [hideal]
    exact voisinDegreeTenSelectedAvoidance_grid_geometric_finite p hp hno

end PfaffianDescent
