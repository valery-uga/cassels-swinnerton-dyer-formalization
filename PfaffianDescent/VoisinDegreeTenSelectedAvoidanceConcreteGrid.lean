import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridLineFinite
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceRankThreeEtale

/-! # Concrete cubic grid in the branch without a rational point

The two grid cubics are products of the three planes with coordinate ratios
-1, 0, 1. Their nine common lines pass through the rational infinity point
[0,0,0,1], which is excluded from the cubic by the absence of rational points.
Thus their actual triple intersection is finite and the last cubic is regular.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

def voisinDegreeTenSelectedAvoidance_gridSlope
    (K : Type u) [Field K] (a : Fin 3) : K := (a.val : K) - 1

def voisinDegreeTenSelectedAvoidance_gridPlane
    (K : Type u) [Field K] (j : Fin 4) (a : Fin 3) : MvPolynomial (Fin 4) K :=
  X j - C (voisinDegreeTenSelectedAvoidance_gridSlope K a) * X 0

def voisinDegreeTenSelectedAvoidance_gridCubic
    (K : Type u) [Field K] (j : Fin 4) : MvPolynomial (Fin 4) K :=
  ∏ a : Fin 3, voisinDegreeTenSelectedAvoidance_gridPlane K j a

def voisinDegreeTenSelectedAvoidance_gridInfinity
    (K : Type u) [Field K] : Fin 4 → K := ![0, 0, 0, 1]

def voisinDegreeTenSelectedAvoidance_gridBase
    (K : Type u) [Field K] (a b : Fin 3) : Fin 4 → K :=
  ![1, voisinDegreeTenSelectedAvoidance_gridSlope K a,
    voisinDegreeTenSelectedAvoidance_gridSlope K b, 0]

theorem voisinDegreeTenSelectedAvoidance_gridPlane_homogeneous
    (K : Type u) [Field K] (j : Fin 4) (a : Fin 3) :
    (voisinDegreeTenSelectedAvoidance_gridPlane K j a).IsHomogeneous 1 :=
  (isHomogeneous_X K j).sub ((isHomogeneous_X K 0).C_mul _)

theorem voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous
    (K : Type u) [Field K] (j : Fin 4) :
    (voisinDegreeTenSelectedAvoidance_gridCubic K j).IsHomogeneous 3 := by
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin 3))
    (voisinDegreeTenSelectedAvoidance_gridPlane K j) (fun _ => 1)
    (fun a _ => voisinDegreeTenSelectedAvoidance_gridPlane_homogeneous K j a)
  simpa only [voisinDegreeTenSelectedAvoidance_gridCubic, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using h

theorem voisinDegreeTenSelectedAvoidance_gridCubic_map
    {K L : Type u} [Field K] [Field L] (φ : K →+* L) (j : Fin 4) :
    (voisinDegreeTenSelectedAvoidance_gridCubic K j).map φ =
      voisinDegreeTenSelectedAvoidance_gridCubic L j := by
  simp [voisinDegreeTenSelectedAvoidance_gridCubic,
    voisinDegreeTenSelectedAvoidance_gridPlane, voisinDegreeTenSelectedAvoidance_gridSlope,
    map_prod]

theorem voisinDegreeTenSelectedAvoidance_gridInfinity_map_eval
    {K L : Type u} [Field K] [Field L] (φ : K →+* L)
    (p : MvPolynomial (Fin 4) K) :
    (p.map φ).eval (voisinDegreeTenSelectedAvoidance_gridInfinity L) =
      φ (p.eval (voisinDegreeTenSelectedAvoidance_gridInfinity K)) := by
  rw [eval_map, eval₂_comp]
  congr 1
  funext j
  fin_cases j <;> simp [voisinDegreeTenSelectedAvoidance_gridInfinity]

/-- Every nonzero ground-field vector is outside the defining cubic when
the actual surface has no rational point. -/
theorem voisinDegreeTenSelectedAvoidance_eval_ne_zero_of_no_section
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (v : Fin 4 → K) (hv : v ≠ 0) : p.eval v ≠ 0 := by
  intro he
  apply hno
  obtain ⟨s, hs⟩ := hypersurface_point_of_coordinates (RingHom.id K) p hp v hv he
  exact ⟨s, by simpa only [CommRingCat.ofHom_id, Spec.map_id] using hs⟩

theorem voisinDegreeTenSelectedAvoidance_grid_line_parameters
    {L : Type u} [Field L] (a b : Fin 3) (y : Fin 4 → L)
    (ha : (voisinDegreeTenSelectedAvoidance_gridPlane L 1 a).eval y = 0)
    (hb : (voisinDegreeTenSelectedAvoidance_gridPlane L 2 b).eval y = 0) :
    ∃ s t : L, y = s • voisinDegreeTenSelectedAvoidance_gridInfinity L +
      t • voisinDegreeTenSelectedAvoidance_gridBase L a b := by
  have ha' : y 1 = voisinDegreeTenSelectedAvoidance_gridSlope L a * y 0 :=
    sub_eq_zero.mp (by simpa [voisinDegreeTenSelectedAvoidance_gridPlane] using ha)
  have hb' : y 2 = voisinDegreeTenSelectedAvoidance_gridSlope L b * y 0 :=
    sub_eq_zero.mp (by simpa [voisinDegreeTenSelectedAvoidance_gridPlane] using hb)
  refine ⟨y 3, y 0, ?_⟩
  ext j
  fin_cases j <;>
    simp [voisinDegreeTenSelectedAvoidance_gridInfinity,
      voisinDegreeTenSelectedAvoidance_gridBase, ha', hb', mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- The actual last cubic in the explicit nine-line grid is regular modulo
the surface cubic and the first grid cubic. This is an unconditional native
proper-intersection witness in the branch without a rational point. -/
theorem voisinDegreeTenSelectedAvoidance_concrete_grid_third_regular
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∀ F : MvPolynomial (Fin 4) K,
      voisinDegreeTenSelectedAvoidance_gridCubic K 2 * F ∈ Ideal.span
        ({p, voisinDegreeTenSelectedAvoidance_gridCubic K 1} : Set _) →
      F ∈ Ideal.span ({p, voisinDegreeTenSelectedAvoidance_gridCubic K 1} : Set _) := by
  let L := AlgebraicClosure K
  let φ := algebraMap K L
  obtain ⟨c, hc⟩ := homogeneous_cubic_has_tensor_any_characteristic
    (p.map φ) (hp.map φ)
  apply voisinDegreeTenSelectedAvoidance_regular_of_nineLine_grid
    p (voisinDegreeTenSelectedAvoidance_gridCubic K 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic K 2) hp
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic_homogeneous K 2) c hc
    (voisinDegreeTenSelectedAvoidance_gridPlane L 1)
    (voisinDegreeTenSelectedAvoidance_gridPlane L 2)
    (voisinDegreeTenSelectedAvoidance_gridPlane_homogeneous L 1)
    (voisinDegreeTenSelectedAvoidance_gridPlane_homogeneous L 2)
    (voisinDegreeTenSelectedAvoidance_gridCubic_map φ 1)
    (voisinDegreeTenSelectedAvoidance_gridCubic_map φ 2)
    (fun _ _ => voisinDegreeTenSelectedAvoidance_gridInfinity L)
    (voisinDegreeTenSelectedAvoidance_gridBase L)
  · intro a b
    have hne := voisinDegreeTenSelectedAvoidance_eval_ne_zero_of_no_section p hp hno
      (voisinDegreeTenSelectedAvoidance_gridInfinity K) (by
        intro h
        have h3 := congrFun h 3
        simpa [voisinDegreeTenSelectedAvoidance_gridInfinity] using h3)
    have he : c.eval (voisinDegreeTenSelectedAvoidance_gridInfinity L) =
        φ (p.eval (voisinDegreeTenSelectedAvoidance_gridInfinity K)) := by
      have hec : c.toMvPolynomial.eval (voisinDegreeTenSelectedAvoidance_gridInfinity L) =
          c.eval (voisinDegreeTenSelectedAvoidance_gridInfinity L) := by
        change MvPolynomial.eval₂ (RingHom.id L)
          (voisinDegreeTenSelectedAvoidance_gridInfinity L) c.toMvPolynomial = _
        rw [Cubic.eval_toMvPolynomial]
        rfl
      rw [← hec, hc]
      exact voisinDegreeTenSelectedAvoidance_gridInfinity_map_eval φ p
    rw [he]
    exact (map_ne_zero φ).mpr hne
  · intro a b t h
    have h0 := congrFun h 0
    simpa [voisinDegreeTenSelectedAvoidance_gridInfinity,
      voisinDegreeTenSelectedAvoidance_gridBase] using h0
  · intro a b
    simp [voisinDegreeTenSelectedAvoidance_gridPlane,
      voisinDegreeTenSelectedAvoidance_gridInfinity,
      voisinDegreeTenSelectedAvoidance_gridBase]
  · intro a b
    simp [voisinDegreeTenSelectedAvoidance_gridPlane,
      voisinDegreeTenSelectedAvoidance_gridInfinity,
      voisinDegreeTenSelectedAvoidance_gridBase]
  · exact voisinDegreeTenSelectedAvoidance_grid_line_parameters

end PfaffianDescent
