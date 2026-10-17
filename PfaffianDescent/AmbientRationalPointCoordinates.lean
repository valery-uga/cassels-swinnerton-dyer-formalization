import AllCharacteristics.AmbientChartPresentation
import PfaffianDescent.VoisinProjectiveSpaceCech

/-! # Coordinates of an actual field-valued point of native projective space

Every actual scheme point factors through an actual coordinate chart. Its
chart-ring homomorphism preserves the specified coefficient map, and is
determined by its normalized coordinate values.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The actual native coordinate-chart inclusion preserves coefficients. -/
theorem ambientRationalPoint_chartι_toBase (j : Fin 4) :
    Proj.awayι PS (X j) (isHomogeneous_X K j) (of_decide_eq_true rfl : 0 < 1) ≫
      ambientToBase =
    Spec.map (CommRingCat.ofHom
      (AllCharacteristics.GradedChart.baseMap PS (z := X j))) := by
  change Proj.awayι PS (X j) (isHomogeneous_X K j) (of_decide_eq_true rfl : 0 < 1) ≫
    (Proj.toSpecZero PS ≫ Spec.map (CommRingCat.ofHom (algebraMap K (PS 0)))) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- Every actual field-valued native projective point is reconstructed by
one actual affine chart homomorphism over its specified coefficient map. -/
theorem ambientRationalPoint_exists_chart_hom
    {L : Type u} [Field L] (b : K →+* L)
    (i : Spec (.of L) ⟶ Proj PS)
    (hi : i ≫ ambientToBase = Spec.map (CommRingCat.ofHom b)) :
    ∃ j : Fin 4, ∃ g : Away PS (X j) →+* L,
      g.comp (AllCharacteristics.GradedChart.baseMap PS (z := X j)) = b ∧
      Spec.map (CommRingCat.ofHom g) ≫
        Proj.awayι PS (X j) (isHomogeneous_X K j) (of_decide_eq_true rfl : 0 < 1) = i := by
  have hx : i default ∈ ⨆ j : Fin 4, ProjectiveNegativeTwist.p3StandardOpen (K := K) j := by
    rw [ProjectiveNegativeTwist.p3StandardOpen_iSup]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let a := Proj.awayι PS (X j) (isHomogeneous_X K j) (of_decide_eq_true rfl : 0 < 1)
  have hrange : Set.range i ⊆ Set.range a := by
    rintro _ ⟨k, rfl⟩
    have hk : k = (default : Spec (.of L)) := Subsingleton.elim _ _
    rw [hk]
    change i default ∈ Proj.basicOpen PS (X j) at hj
    rw [← Proj.opensRange_awayι PS (X j) (isHomogeneous_X K j)
      (of_decide_eq_true rfl : 0 < 1)] at hj
    exact hj
  let iU := IsOpenImmersion.lift a i hrange
  let g := Spec.preimage iU
  have hg : Spec.map g = iU := Spec.map_preimage iU
  have hU : iU ≫ Spec.map (CommRingCat.ofHom
      (AllCharacteristics.GradedChart.baseMap PS (z := X j))) =
        Spec.map (CommRingCat.ofHom b) := by
    rw [← ambientRationalPoint_chartι_toBase K j, ← Category.assoc]
    exact (congrArg (fun q => q ≫ ambientToBase) (IsOpenImmersion.lift_fac a i hrange)).trans hi
  refine ⟨j, g.hom, ?_, ?_⟩
  · have he : CommRingCat.ofHom (AllCharacteristics.GradedChart.baseMap PS (z := X j)) ≫ g =
        CommRingCat.ofHom b := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg]
      exact hU
    exact congrArg CommRingCat.Hom.hom he
  · change Spec.map g ≫ a = i
    rw [hg]
    exact IsOpenImmersion.lift_fac a i hrange

/-- Native ambient chart homomorphisms are determined by coefficients and
normalized coordinates. -/
theorem ambientRationalPoint_chart_hom_ext
    {L : Type u} [CommRing L] (j : Fin 4)
    (g h : Away PS (X j) →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap PS (z := X j)) =
      h.comp (AllCharacteristics.GradedChart.baseMap PS (z := X j)))
    (hcoords : ∀ k : Fin 4, g (ambientChartCoordinate (R := K) j k) =
      h (ambientChartCoordinate (R := K) j k)) : g = h := by
  apply RingHom.ext
  intro z
  obtain ⟨p, hp⟩ := ambientChartEvaluation_surjective j z
  rw [← hp]
  change g (p.eval₂ (AllCharacteristics.GradedChart.baseMap PS (z := X j))
      (ambientChartCoordinate (R := K) j)) =
    h (p.eval₂ (AllCharacteristics.GradedChart.baseMap PS (z := X j))
      (ambientChartCoordinate (R := K) j))
  rw [MvPolynomial.hom_eval₂, MvPolynomial.hom_eval₂, hbase]
  congr 1
  exact funext hcoords

/-- Actual evaluation on a native coordinate chart at a normalized vector. -/
noncomputable def ambientRationalPoint_chartEvaluation
    {L : Type u} [CommRing L] (b : K →+* L)
    (v : Fin 4 → L) (j : Fin 4) (hv : v j = 1) : Away PS (X j) →+* L :=
  AllCharacteristics.GradedChart.liftCoordinateOne PS (X j)
    (eval₂Hom b v) (by simpa using hv)

theorem ambientRationalPoint_chartEvaluation_base
    {L : Type u} [CommRing L] (b : K →+* L)
    (v : Fin 4 → L) (j : Fin 4) (hv : v j = 1) :
    (ambientRationalPoint_chartEvaluation K b v j hv).comp
      (AllCharacteristics.GradedChart.baseMap PS (z := X j)) = b := by
  apply RingHom.ext
  intro a
  change AllCharacteristics.GradedChart.liftCoordinateOne PS (X j)
    (eval₂Hom b v) (by simpa using hv)
      (AllCharacteristics.GradedChart.baseMap PS a) = b a
  exact (AllCharacteristics.GradedChart.liftCoordinateOne_baseMap PS (X j)
    (eval₂Hom b v) (by simpa using hv) a).trans (eval₂Hom_C b v a)

theorem ambientRationalPoint_chartEvaluation_coordinate
    {L : Type u} [CommRing L] (b : K →+* L)
    (v : Fin 4 → L) (j : Fin 4) (hv : v j = 1) (k : Fin 4) :
    ambientRationalPoint_chartEvaluation K b v j hv
      (ambientChartCoordinate (R := K) j k) = v k := by
  exact (AllCharacteristics.GradedChart.liftCoordinateOne_normalized PS (X j)
    (eval₂Hom b v) (by simpa using hv) (isHomogeneous_X K j) (X k)
      (isHomogeneous_X K k)).trans (eval₂Hom_X' b v k)

/-- Recover every actual field-valued projective morphism from a nonzero
normalized coordinate vector using its original coefficient map. -/
theorem ambientRationalPoint_exists_normalized_evaluation
    {L : Type u} [Field L] (b : K →+* L)
    (i : Spec (.of L) ⟶ Proj PS)
    (hi : i ≫ ambientToBase = Spec.map (CommRingCat.ofHom b)) :
    ∃ (j : Fin 4) (v : Fin 4 → L) (hv : v j = 1), v ≠ 0 ∧
      Spec.map (CommRingCat.ofHom (ambientRationalPoint_chartEvaluation K b v j hv)) ≫
        Proj.awayι PS (X j) (isHomogeneous_X K j) (of_decide_eq_true rfl : 0 < 1) = i := by
  obtain ⟨j, g, hb, hg⟩ := ambientRationalPoint_exists_chart_hom K b i hi
  let v : Fin 4 → L := fun k => g (ambientChartCoordinate (R := K) j k)
  have hv : v j = 1 := by simp [v, ambientChartCoordinate_self]
  have hne : v ≠ 0 := by
    intro h
    have hj := congrFun h j
    rw [hv] at hj
    exact one_ne_zero hj
  have he : ambientRationalPoint_chartEvaluation K b v j hv = g := by
    apply ambientRationalPoint_chart_hom_ext K j
    · exact (ambientRationalPoint_chartEvaluation_base K b v j hv).trans hb.symm
    · intro k
      exact ambientRationalPoint_chartEvaluation_coordinate K b v j hv k
  refine ⟨j, v, hv, hne, ?_⟩
  rw [he]
  exact hg

end PfaffianDescent
