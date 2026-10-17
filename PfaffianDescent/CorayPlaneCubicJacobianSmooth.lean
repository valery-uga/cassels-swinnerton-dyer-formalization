import AllCharacteristics.AffineChartPresentation
import AllCharacteristics.JacobianLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Data.Fin.VecNotation

/-! SOURCE ONLY / UNVERIFIED149. Literal native Fin3/cubic plane-chart
presentation, with THREE variables and TWO equations, hence relative dimension
ONE. This constructs the real localized submersive presentation and native
smoothness from actual partial covers. The actual generic caller in this
packet derives those covers internally; no smooth-cut conclusion is assumed.
No source148 duplication, compiler launch, or heartbeat-option change. -/

open AlgebraicGeometry CategoryTheory MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective

universe u
variable {k : Type u} [CommRing k]
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance plane_hypersurfaceChartAlgebra
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3) (j : Fin 3) :
    Algebra k (ChartRing (equationIdeal p hp) j) :=
  (chartBaseMap (equationIdeal p hp) j).toAlgebra

noncomputable def plane_hypersurfaceChartRelations
    (p : MvPolynomial (Fin 3) k) (j : Fin 3) : Fin 2 → MvPolynomial (Fin 3) k :=
  ![p, X j - 1]

@[simp] theorem plane_hypersurfaceChartRelations_zero
    (p : MvPolynomial (Fin 3) k) (j : Fin 3) :
    plane_hypersurfaceChartRelations p j 0 = p := by
  simp [plane_hypersurfaceChartRelations]

@[simp] theorem plane_hypersurfaceChartRelations_one
    (p : MvPolynomial (Fin 3) k) (j : Fin 3) :
    plane_hypersurfaceChartRelations p j 1 = X j - 1 := by
  simp [plane_hypersurfaceChartRelations]

def plane_hypersurfaceChartRelationVariables (i j : Fin 3) : Fin 2 → Fin 3 :=
  ![i, j]

@[simp] theorem plane_hypersurfaceChartRelationVariables_zero (i j : Fin 3) :
    plane_hypersurfaceChartRelationVariables i j 0 = i := by
  simp [plane_hypersurfaceChartRelationVariables]

@[simp] theorem plane_hypersurfaceChartRelationVariables_one (i j : Fin 3) :
    plane_hypersurfaceChartRelationVariables i j 1 = j := by
  simp [plane_hypersurfaceChartRelationVariables]

theorem plane_hypersurfaceChartRelationVariables_injective {i j : Fin 3} (hij : i ≠ j) :
    Function.Injective (plane_hypersurfaceChartRelationVariables i j) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [plane_hypersurfaceChartRelationVariables]

theorem plane_range_hypersurfaceChartRelations
    (p : MvPolynomial (Fin 3) k) (j : Fin 3) :
    Set.range (plane_hypersurfaceChartRelations p j) = {p, X j - 1} := by
  ext q
  constructor
  · rintro ⟨a, rfl⟩
    fin_cases a <;> simp [plane_hypersurfaceChartRelations]
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact ⟨0, by simp [plane_hypersurfaceChartRelations]⟩
    · exact ⟨1, by simp [plane_hypersurfaceChartRelations]⟩

theorem plane_span_range_hypersurfaceChartRelations
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3) (j : Fin 3) :
    Ideal.span (Set.range (plane_hypersurfaceChartRelations p j)) =
      chartPresentationIdeal (equationIdeal p hp) j := by
  rw [plane_range_hypersurfaceChartRelations]
  change Ideal.span {p, X j - 1} = Ideal.span {p} ⊔ Ideal.span {X j - 1}
  rw [← Ideal.span_union]
  congr

/-- The naive two-equation quotient is the actual normalized projective
chart, as a `k`-algebra. -/
noncomputable def plane_hypersurfaceChartRelationsEquiv
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3) (j : Fin 3) :
    (MvPolynomial (Fin 3) k ⧸
      Ideal.span (Set.range (plane_hypersurfaceChartRelations p j))) ≃ₐ[k]
        ChartRing (equationIdeal p hp) j := by
  let e : (MvPolynomial (Fin 3) k ⧸
      Ideal.span (Set.range (plane_hypersurfaceChartRelations p j))) ≃+*
        ChartRing (equationIdeal p hp) j :=
    (Ideal.quotEquivOfEq (plane_span_range_hypersurfaceChartRelations p hp j)).trans
      (chartPresentationEquiv (equationIdeal p hp) j)
  exact
    { e with
      commutes' := by
        intro r
        change e (Ideal.Quotient.mk _ (C r)) = chartBaseMap (equationIdeal p hp) j r
        simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
          chartPresentationEquiv_mk, eval₂_C] }

@[simp] theorem plane_hypersurfaceChartRelationsEquiv_mk
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3) (j : Fin 3)
    (r : MvPolynomial (Fin 3) k) :
    plane_hypersurfaceChartRelationsEquiv p hp j (Ideal.Quotient.mk _ r) =
      r.eval₂ (chartBaseMap (equationIdeal p hp) j)
        (chartCoordinate (equationIdeal p hp) j) := by
  change chartPresentationEquiv (equationIdeal p hp) j
      (Ideal.quotEquivOfEq (plane_span_range_hypersurfaceChartRelations p hp j)
        (Ideal.Quotient.mk _ r)) = _
  rw [Ideal.quotEquivOfEq_mk, chartPresentationEquiv_mk]

/-- The two-equation pre-submersive presentation of a normalized chart,
using `p` in variable `i` and `X j - 1` in variable `j`. -/
noncomputable def plane_hypersurfaceChartPrePresentation
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3)
    (i j : Fin 3) (hij : i ≠ j) :
    Algebra.PreSubmersivePresentation k (ChartRing (equationIdeal p hp) j)
      (Fin 3) (Fin 2) :=
  (Algebra.PreSubmersivePresentation.naive
      (v := plane_hypersurfaceChartRelations p j)
      (plane_hypersurfaceChartRelationVariables i j)
      (plane_hypersurfaceChartRelationVariables_injective hij)).ofAlgEquiv
    (plane_hypersurfaceChartRelationsEquiv p hp j)

/-- A normalized projective hypersurface chart has relative dimension one:
the presentation uses three coordinates and the hypersurface equation together
with the chart normalization give two relations. -/
theorem plane_hypersurfaceChartPrePresentation_dimension
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3)
    (i j : Fin 3) (hij : i ≠ j) :
    (plane_hypersurfaceChartPrePresentation p hp i j hij).dimension = 1 := by
  change ((Algebra.PreSubmersivePresentation.naive
      (v := plane_hypersurfaceChartRelations p j)
      (plane_hypersurfaceChartRelationVariables i j)
      (plane_hypersurfaceChartRelationVariables_injective hij)).ofAlgEquiv
        (plane_hypersurfaceChartRelationsEquiv p hp j)).dimension = 1
  simp [Algebra.Presentation.dimension]

/-- The Jacobian of this chart presentation is the normalized value of the
chosen partial derivative. -/
theorem plane_hypersurfaceChartPrePresentation_jacobian
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3)
    (i j : Fin 3) (hij : i ≠ j) :
    (plane_hypersurfaceChartPrePresentation p hp i j hij).jacobian =
      (pderiv i p).eval₂ (chartBaseMap (equationIdeal p hp) j)
        (chartCoordinate (equationIdeal p hp) j) := by
  classical
  let P₀ := Algebra.PreSubmersivePresentation.naive
    (v := plane_hypersurfaceChartRelations p j)
    (plane_hypersurfaceChartRelationVariables i j)
    (plane_hypersurfaceChartRelationVariables_injective hij)
  have hP₀ : P₀.jacobian =
      Ideal.Quotient.mk _ (pderiv i p) := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    change Ideal.Quotient.mk _ P₀.jacobiMatrix.det = _
    congr 1
    rw [Matrix.det_fin_two]
    simp only [P₀, Algebra.PreSubmersivePresentation.jacobiMatrix_naive,
      plane_hypersurfaceChartRelationVariables_zero, plane_hypersurfaceChartRelationVariables_one,
      plane_hypersurfaceChartRelations_zero, plane_hypersurfaceChartRelations_one]
    simp [hij]
  change (P₀.ofAlgEquiv (plane_hypersurfaceChartRelationsEquiv p hp j)).jacobian = _
  calc
    _ = plane_hypersurfaceChartRelationsEquiv p hp j P₀.jacobian :=
      Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv P₀
        (plane_hypersurfaceChartRelationsEquiv p hp j)
    _ = plane_hypersurfaceChartRelationsEquiv p hp j
        (Ideal.Quotient.mk _ (pderiv i p)) := congrArg _ hP₀
    _ = _ := plane_hypersurfaceChartRelationsEquiv_mk p hp j (pderiv i p)

/-- The normalized class of a partial derivative on a projective chart. -/
noncomputable def plane_chartPDeriv
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3) (j : Fin 3)
    (i : {i : Fin 3 // i ≠ j}) : ChartRing (equationIdeal p hp) j :=
  (pderiv i.1 p).eval₂ (chartBaseMap (equationIdeal p hp) j)
    (chartCoordinate (equationIdeal p hp) j)

/-- On the open where one non-distinguished partial derivative is invertible,
the normalized projective hypersurface chart is standard smooth of relative
dimension one.  This is the chart-level input for the curve-dimension
calculation in the pencil construction. -/
theorem plane_standardSmoothOfRelativeDimension_one_chartBaseMap_away_pderiv
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3)
    (j : Fin 3) (i : {i : Fin 3 // i ≠ j}) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 k
      (Localization.Away (plane_chartPDeriv p hp j i)) := by
  let P := plane_hypersurfaceChartPrePresentation p hp i.1 j i.2
  have hjac : P.jacobian = plane_chartPDeriv p hp j i := by
    exact plane_hypersurfaceChartPrePresentation_jacobian p hp i.1 j i.2
  rw [← hjac]
  apply (jacobianLocalizedPresentation P).isStandardSmoothOfRelativeDimension
  rw [jacobianLocalizedPresentation_dimension]
  exact plane_hypersurfaceChartPrePresentation_dimension p hp i.1 j i.2

/-- If the partial-derivative basic opens cover a normalized chart, its
coefficient homomorphism is locally standard smooth of relative dimension
one. -/
theorem plane_locally_standardSmoothOfRelativeDimension_one_chartBaseMap_of_span_pderiv
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3) (j : Fin 3)
    (hspan : Ideal.span (Set.range (plane_chartPDeriv p hp j)) = ⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (chartBaseMap (equationIdeal p hp) j) := by
  refine ⟨Set.range (plane_chartPDeriv p hp j), hspan, ?_⟩
  rintro d ⟨i, rfl⟩
  rw [← RingHom.algebraMap_toAlgebra
    (chartBaseMap (equationIdeal p hp) j)]
  rw [← IsScalarTower.algebraMap_eq k
    (ChartRing (equationIdeal p hp) j)
    (Localization.Away (plane_chartPDeriv p hp j i)),
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact plane_standardSmoothOfRelativeDimension_one_chartBaseMap_away_pderiv p hp j i

/-- If the non-distinguished partial derivatives cover a normalized chart,
its coefficient homomorphism is smooth. -/
theorem plane_smooth_chartBaseMap_of_span_pderiv
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3) (j : Fin 3)
    (hspan : Ideal.span (Set.range (plane_chartPDeriv p hp j)) = ⊤) :
    (chartBaseMap (equationIdeal p hp) j).Smooth := by
  rw [RingHom.smooth_iff_locally_isStandardSmooth]
  refine ⟨Set.range (plane_chartPDeriv p hp j), hspan, ?_⟩
  rintro d ⟨i, rfl⟩
  let P := plane_hypersurfaceChartPrePresentation p hp i.1 j i.2
  have hjac : P.jacobian = plane_chartPDeriv p hp j i := by
    exact plane_hypersurfaceChartPrePresentation_jacobian p hp i.1 j i.2
  rw [← RingHom.algebraMap_toAlgebra
    (chartBaseMap (equationIdeal p hp) j)]
  rw [← IsScalarTower.algebraMap_eq k
    (ChartRing (equationIdeal p hp) j)
    (Localization.Away (plane_chartPDeriv p hp j i)),
    RingHom.isStandardSmooth_algebraMap]
  rw [← hjac]
  exact (jacobianLocalizedPresentation P).isStandardSmooth

/-- Chartwise Jacobian covers prove smoothness of the projective
hypersurface. -/
theorem plane_smooth_hypersurface_of_chart_pderiv_span
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3)
    (hspan : ∀ j : Fin 3, Ideal.span (Set.range (plane_chartPDeriv p hp j)) = ⊤) :
    Smooth (hypersurfaceToBase p hp) := by
  have : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth.{u})
    (coordinateOpenCover (equationIdeal p hp)).openCover).mpr
  intro j
  change Fin 3 at j
  dsimp only [hypersurfaceToBase, hypersurface]
  change Smooth (chartι (equationIdeal p hp) j ≫ toBase (equationIdeal p hp))
  rw [chartι_toBase]
  exact (HasRingHomProperty.Spec_iff (P := @Smooth.{u})).mpr
    (plane_smooth_chartBaseMap_of_span_pderiv p hp j (hspan j))

/-- A projective hypersurface whose Jacobian basic opens cover every
normalized chart is smooth of relative dimension one. -/
theorem plane_smoothOfRelativeDimension_one_hypersurface_of_chart_pderiv_span
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous 3)
    (hspan : ∀ j : Fin 3, Ideal.span (Set.range (plane_chartPDeriv p hp j)) = ⊤) :
    SmoothOfRelativeDimension 1 (hypersurfaceToBase p hp) := by
  letI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 1)
    (coordinateOpenCover (equationIdeal p hp)).openCover
  intro j
  change Fin 3 at j
  dsimp only [hypersurfaceToBase, hypersurface]
  change SmoothOfRelativeDimension 1
    (chartι (equationIdeal p hp) j ≫ toBase (equationIdeal p hp))
  rw [chartι_toBase]
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
  change RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
    (chartBaseMap (equationIdeal p hp) j)
  exact plane_locally_standardSmoothOfRelativeDimension_one_chartBaseMap_of_span_pderiv
    p hp j (hspan j)

end HomogeneousProjective
end AllCharacteristics
