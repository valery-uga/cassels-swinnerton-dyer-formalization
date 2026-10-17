import PfaffianDescent.ActualNormalizedFrameColumns
import PfaffianDescent.NormalizedFiniteEquationPoint
import PfaffianDescent.AmbientNormalizedPointUnitChartComparison

/-! SOURCE ONLY, UNVERIFIED. A common-chart normalizer is DERIVED from the
actual field-valued support point. The proof factors a zero coordinate
through its actual hyperplane, not through reduced or set-only equations. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K A : Type u} [Field K] [Field A] [Algebra K A]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem actual_normalized_field_point_coordinate_ne_zero_of_basicOpen
    (x : Fin 4 → A) (r : Fin 4) (hx : x r = 1) (j : Fin 4)
    (hOpen : ambientNormalizedCoordinateChartPoint (F := K) x r hx
        (IsLocalRing.closedPoint A) ∈
      Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X j)) : x j ≠ 0 := by
  intro hzero
  let J := equationIdeal (X j : MvPolynomial (Fin 4) K) (isHomogeneous_X K j)
  have hker : J.toIdeal ≤ RingHom.ker (eval₂Hom (algebraMap K A) x) := by
    apply Ideal.span_le.mpr
    intro p hp
    have hp' : p = X j := Set.mem_singleton_iff.mp hp
    subst p
    change eval₂Hom (algebraMap K A) x (X j) = 0
    simpa only [eval₂Hom_X'] using hzero
  have heJ : ∀ p ∈ J.toIdeal, p.eval₂ (algebraMap K A) x = 0 := by
    intro p hp
    exact hker hp
  have hxX : (X r : MvPolynomial (Fin 4) K).eval₂ (algebraMap K A) x = 1 := by
    simpa only [eval₂_X] using hx
  let q := normalizedFiniteEquationPoint J x (X r) (isHomogeneous_X K r) hxX heJ
  have hFactor : q ≫ quotientProjMap J =
      ambientNormalizedCoordinateChartPoint (F := K) x r hx := by
    calc
      q ≫ quotientProjMap J = normalizedFiniteEquationPoint ⊥ x (X r)
          (isHomogeneous_X K r) hxX
          (fun p hp => by simp [show p = 0 from Ideal.mem_bot.mp hp]) ≫ quotientProjMap ⊥ :=
        normalizedFiniteEquationPoint_toAmbient J x (X r) (isHomogeneous_X K r) hxX heJ
      _ = ambientNormalizedCoordinateChartPoint x r hx := by
        change linearNormalizedPoint ⊥ x (X r) (isHomogeneous_X K r) hxX _ ≫
          quotientProjMap ⊥ = _
        exact linearNormalizedPoint_toAmbient_eq_coordinateChartPoint ⊥ x r hx _
  have hRange : ambientNormalizedCoordinateChartPoint (F := K) x r hx
      (IsLocalRing.closedPoint A) ∈ Set.range (quotientProjMap J) := by
    refine ⟨q (IsLocalRing.closedPoint A), ?_⟩
    exact congrArg (fun f : Spec (.of A) ⟶ Proj (homogeneousSubmodule (Fin 4) K) =>
      f (IsLocalRing.closedPoint A)) hFactor
  have hLe := (quotientProjMap_mem_range_iff J _).mp hRange
  have hMem : (X j : MvPolynomial (Fin 4) K) ∈ J.toIdeal :=
    Ideal.subset_span (Set.mem_singleton _)
  change (X j : MvPolynomial (Fin 4) K) ∉
    (ambientNormalizedCoordinateChartPoint (F := K) x r hx
      (IsLocalRing.closedPoint A)).asHomogeneousIdeal.toIdeal at hOpen
  exact hOpen (hLe hMem)

theorem actual_normalized_point_equal_cross_chart_coordinates
    (x y : Fin 4 → A) (r j : Fin 4) (hx : x r = 1) (hy : y j = 1)
    (hPoint : ambientNormalizedCoordinateChartPoint (F := K) x r hx =
      ambientNormalizedCoordinateChartPoint (F := K) y j hy) :
    x j ≠ 0 ∧ ∀ s, x s = x j * y s := by
  have hOpen : ambientNormalizedCoordinateChartPoint (F := K) x r hx
      (IsLocalRing.closedPoint A) ∈
        Proj.basicOpen (homogeneousSubmodule (Fin 4) K) (X j) := by
    rw [hPoint, ← Proj.opensRange_awayι (homogeneousSubmodule (Fin 4) K) (X j)
      (isHomogeneous_X K j) (by decide : 0 < 1)]
    exact ⟨Spec.map (CommRingCat.ofHom (ambientNormalizedCoordinateChartMap y j hy))
      (IsLocalRing.closedPoint A), rfl⟩
  have hne := actual_normalized_field_point_coordinate_ne_zero_of_basicOpen x r hx j hOpen
  let u : Aˣ := Units.mk0 (x j) hne
  have he : ∀ p ∈ (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)).toIdeal,
      p.eval₂ (algebraMap K A) x = 0 := by
    intro p hp
    have hp0 : p = 0 := Ideal.mem_bot.mp hp
    simp [hp0]
  have hxX : (X r : MvPolynomial (Fin 4) K).eval₂ (algebraMap K A) x = 1 := by
    simpa only [eval₂_X] using hx
  have hOld := linearNormalizedPoint_toAmbient_eq_coordinateChartPoint ⊥ x r hx he
  have hNew := linearNormalizedPoint_toAmbient_eq_unit_coordinateChartPoint ⊥ x (X r)
    (isHomogeneous_X K r) hxX he j u rfl
  have hNormalized : ambientNormalizedCoordinateChartPoint (F := K)
      (fun s => (x j)⁻¹ * x s) j (by simp [hne]) =
        ambientNormalizedCoordinateChartPoint (F := K) y j hy := by
    simpa only [u, Units.val_inv_eq_inv_val, Units.val_mk0] using
      hNew.symm.trans (hOld.trans hPoint)
  have hCoords := actual_normalized_ambient_point_coordinates_injective
    (fun s => (x j)⁻¹ * x s) y j (by simp [hne]) hy hNormalized
  refine ⟨hne, ?_⟩
  intro s
  calc
    x s = x j * ((x j)⁻¹ * x s) := by rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ = x j * y s := congrArg (fun a => x j * a) (congrFun hCoords s)

end PfaffianDescent
