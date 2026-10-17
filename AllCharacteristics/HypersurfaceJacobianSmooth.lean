import AllCharacteristics.AffineChartPresentation
import AllCharacteristics.JacobianLocalization
import AllCharacteristics.RegularPairDimension
import AllCharacteristics.SmoothRegularity
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# A chartwise Jacobian criterion for projective hypersurfaces

The normalized `j`-th chart has the two-relation presentation
`p = 0`, `X j - 1 = 0`.  Inverting a partial derivative in a distinct
coordinate makes this presentation standard smooth.  If those derivative
classes generate the unit ideal on every chart, the projective hypersurface
is smooth.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective

universe u
variable {k : Type u} [CommRing k]
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance hypersurfaceChartAlgebra
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (j : Fin 4) :
    Algebra k (ChartRing (equationIdeal p hp) j) :=
  (chartBaseMap (equationIdeal p hp) j).toAlgebra

noncomputable def hypersurfaceChartRelations
    (p : MvPolynomial (Fin 4) k) (j : Fin 4) : Fin 2 → MvPolynomial (Fin 4) k :=
  ![p, X j - 1]

@[simp] theorem hypersurfaceChartRelations_zero
    (p : MvPolynomial (Fin 4) k) (j : Fin 4) :
    hypersurfaceChartRelations p j 0 = p := by
  simp [hypersurfaceChartRelations]

@[simp] theorem hypersurfaceChartRelations_one
    (p : MvPolynomial (Fin 4) k) (j : Fin 4) :
    hypersurfaceChartRelations p j 1 = X j - 1 := by
  simp [hypersurfaceChartRelations]

def hypersurfaceChartRelationVariables (i j : Fin 4) : Fin 2 → Fin 4 :=
  ![i, j]

@[simp] theorem hypersurfaceChartRelationVariables_zero (i j : Fin 4) :
    hypersurfaceChartRelationVariables i j 0 = i := by
  simp [hypersurfaceChartRelationVariables]

@[simp] theorem hypersurfaceChartRelationVariables_one (i j : Fin 4) :
    hypersurfaceChartRelationVariables i j 1 = j := by
  simp [hypersurfaceChartRelationVariables]

theorem hypersurfaceChartRelationVariables_injective {i j : Fin 4} (hij : i ≠ j) :
    Function.Injective (hypersurfaceChartRelationVariables i j) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [hypersurfaceChartRelationVariables]

theorem range_hypersurfaceChartRelations
    (p : MvPolynomial (Fin 4) k) (j : Fin 4) :
    Set.range (hypersurfaceChartRelations p j) = {p, X j - 1} := by
  ext q
  constructor
  · rintro ⟨a, rfl⟩
    fin_cases a <;> simp [hypersurfaceChartRelations]
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact ⟨0, by simp [hypersurfaceChartRelations]⟩
    · exact ⟨1, by simp [hypersurfaceChartRelations]⟩

theorem span_range_hypersurfaceChartRelations
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (j : Fin 4) :
    Ideal.span (Set.range (hypersurfaceChartRelations p j)) =
      chartPresentationIdeal (equationIdeal p hp) j := by
  rw [range_hypersurfaceChartRelations]
  change Ideal.span {p, X j - 1} = Ideal.span {p} ⊔ Ideal.span {X j - 1}
  rw [← Ideal.span_union]
  congr

/-- The naive two-equation quotient is the actual normalized projective
chart, as a `k`-algebra. -/
noncomputable def hypersurfaceChartRelationsEquiv
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (j : Fin 4) :
    (MvPolynomial (Fin 4) k ⧸
      Ideal.span (Set.range (hypersurfaceChartRelations p j))) ≃ₐ[k]
        ChartRing (equationIdeal p hp) j := by
  let e : (MvPolynomial (Fin 4) k ⧸
      Ideal.span (Set.range (hypersurfaceChartRelations p j))) ≃+*
        ChartRing (equationIdeal p hp) j :=
    (Ideal.quotEquivOfEq (span_range_hypersurfaceChartRelations p hp j)).trans
      (chartPresentationEquiv (equationIdeal p hp) j)
  exact
    { e with
      commutes' := by
        intro r
        change e (Ideal.Quotient.mk _ (C r)) = chartBaseMap (equationIdeal p hp) j r
        simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
          chartPresentationEquiv_mk, eval₂_C] }

@[simp] theorem hypersurfaceChartRelationsEquiv_mk
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (r : MvPolynomial (Fin 4) k) :
    hypersurfaceChartRelationsEquiv p hp j (Ideal.Quotient.mk _ r) =
      r.eval₂ (chartBaseMap (equationIdeal p hp) j)
        (chartCoordinate (equationIdeal p hp) j) := by
  change chartPresentationEquiv (equationIdeal p hp) j
      (Ideal.quotEquivOfEq (span_range_hypersurfaceChartRelations p hp j)
        (Ideal.Quotient.mk _ r)) = _
  rw [Ideal.quotEquivOfEq_mk, chartPresentationEquiv_mk]

/-- The two-equation pre-submersive presentation of a normalized chart,
using `p` in variable `i` and `X j - 1` in variable `j`. -/
noncomputable def hypersurfaceChartPrePresentation
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (i j : Fin 4) (hij : i ≠ j) :
    Algebra.PreSubmersivePresentation k (ChartRing (equationIdeal p hp) j)
      (Fin 4) (Fin 2) :=
  (Algebra.PreSubmersivePresentation.naive
      (v := hypersurfaceChartRelations p j)
      (hypersurfaceChartRelationVariables i j)
      (hypersurfaceChartRelationVariables_injective hij)).ofAlgEquiv
    (hypersurfaceChartRelationsEquiv p hp j)

/-- A normalized projective hypersurface chart has relative dimension two:
the presentation uses four coordinates and the hypersurface equation together
with the chart normalization give two relations. -/
theorem hypersurfaceChartPrePresentation_dimension
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (i j : Fin 4) (hij : i ≠ j) :
    (hypersurfaceChartPrePresentation p hp i j hij).dimension = 2 := by
  change ((Algebra.PreSubmersivePresentation.naive
      (v := hypersurfaceChartRelations p j)
      (hypersurfaceChartRelationVariables i j)
      (hypersurfaceChartRelationVariables_injective hij)).ofAlgEquiv
        (hypersurfaceChartRelationsEquiv p hp j)).dimension = 2
  simp [Algebra.Presentation.dimension]

/-- The Jacobian of this chart presentation is the normalized value of the
chosen partial derivative. -/
theorem hypersurfaceChartPrePresentation_jacobian
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (i j : Fin 4) (hij : i ≠ j) :
    (hypersurfaceChartPrePresentation p hp i j hij).jacobian =
      (pderiv i p).eval₂ (chartBaseMap (equationIdeal p hp) j)
        (chartCoordinate (equationIdeal p hp) j) := by
  classical
  let P₀ := Algebra.PreSubmersivePresentation.naive
    (v := hypersurfaceChartRelations p j)
    (hypersurfaceChartRelationVariables i j)
    (hypersurfaceChartRelationVariables_injective hij)
  have hP₀ : P₀.jacobian =
      Ideal.Quotient.mk _ (pderiv i p) := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    change Ideal.Quotient.mk _ P₀.jacobiMatrix.det = _
    congr 1
    rw [Matrix.det_fin_two]
    simp only [P₀, Algebra.PreSubmersivePresentation.jacobiMatrix_naive,
      hypersurfaceChartRelationVariables_zero, hypersurfaceChartRelationVariables_one,
      hypersurfaceChartRelations_zero, hypersurfaceChartRelations_one]
    simp [hij]
  change (P₀.ofAlgEquiv (hypersurfaceChartRelationsEquiv p hp j)).jacobian = _
  calc
    _ = hypersurfaceChartRelationsEquiv p hp j P₀.jacobian :=
      Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv P₀
        (hypersurfaceChartRelationsEquiv p hp j)
    _ = hypersurfaceChartRelationsEquiv p hp j
        (Ideal.Quotient.mk _ (pderiv i p)) := congrArg _ hP₀
    _ = _ := hypersurfaceChartRelationsEquiv_mk p hp j (pderiv i p)

/-- The normalized class of a partial derivative on a projective chart. -/
noncomputable def chartPDeriv
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (i : {i : Fin 4 // i ≠ j}) : ChartRing (equationIdeal p hp) j :=
  (pderiv i.1 p).eval₂ (chartBaseMap (equationIdeal p hp) j)
    (chartCoordinate (equationIdeal p hp) j)

/-- On the open where one non-distinguished partial derivative is invertible,
the normalized projective hypersurface chart is standard smooth of relative
dimension two.  This is the chart-level input for the surface-dimension
calculation in the pencil construction. -/
theorem standardSmoothOfRelativeDimension_two_chartBaseMap_away_pderiv
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (j : Fin 4) (i : {i : Fin 4 // i ≠ j}) :
    Algebra.IsStandardSmoothOfRelativeDimension 2 k
      (Localization.Away (chartPDeriv p hp j i)) := by
  let P := hypersurfaceChartPrePresentation p hp i.1 j i.2
  have hjac : P.jacobian = chartPDeriv p hp j i := by
    exact hypersurfaceChartPrePresentation_jacobian p hp i.1 j i.2
  rw [← hjac]
  apply (jacobianLocalizedPresentation P).isStandardSmoothOfRelativeDimension
  rw [jacobianLocalizedPresentation_dimension]
  exact hypersurfaceChartPrePresentation_dimension p hp i.1 j i.2

/-- If the partial-derivative basic opens cover a normalized chart, its
coefficient homomorphism is locally standard smooth of relative dimension
two. -/
theorem locally_standardSmoothOfRelativeDimension_two_chartBaseMap_of_span_pderiv
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (hspan : Ideal.span (Set.range (chartPDeriv p hp j)) = ⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 2)
      (chartBaseMap (equationIdeal p hp) j) := by
  refine ⟨Set.range (chartPDeriv p hp j), hspan, ?_⟩
  rintro d ⟨i, rfl⟩
  rw [← RingHom.algebraMap_toAlgebra
    (chartBaseMap (equationIdeal p hp) j)]
  rw [← IsScalarTower.algebraMap_eq k
    (ChartRing (equationIdeal p hp) j)
    (Localization.Away (chartPDeriv p hp j i)),
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact standardSmoothOfRelativeDimension_two_chartBaseMap_away_pderiv p hp j i

/-- A smooth projective-hypersurface chart over a field has local dimension at most two at every
prime, provided its non-distinguished partial derivatives generate the unit ideal. -/
theorem ringKrullDim_localizationAtPrime_chartBaseMap_le_two_of_span_pderiv
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (hspan : Ideal.span (Set.range (chartPDeriv p hp j)) = ⊤)
    (q : Ideal (ChartRing (equationIdeal p hp) j)) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime q) ≤ 2 := by
  have hlocal := locally_standardSmoothOfRelativeDimension_two_chartBaseMap_of_span_pderiv
    p hp j hspan
  rw [← RingHom.algebraMap_toAlgebra
    (chartBaseMap (equationIdeal p hp) j)] at hlocal
  exact ringKrullDim_localizationAtPrime_le_of_locally_standardSmoothOfRelativeDimension_of_field
    (K := k) (A := ChartRing (equationIdeal p hp) j) 2 hlocal q

/-- If the non-distinguished partial derivatives cover a normalized chart,
its coefficient homomorphism is smooth. -/
theorem smooth_chartBaseMap_of_span_pderiv
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (hspan : Ideal.span (Set.range (chartPDeriv p hp j)) = ⊤) :
    (chartBaseMap (equationIdeal p hp) j).Smooth := by
  rw [RingHom.smooth_iff_locally_isStandardSmooth]
  refine ⟨Set.range (chartPDeriv p hp j), hspan, ?_⟩
  rintro d ⟨i, rfl⟩
  let P := hypersurfaceChartPrePresentation p hp i.1 j i.2
  have hjac : P.jacobian = chartPDeriv p hp j i := by
    exact hypersurfaceChartPrePresentation_jacobian p hp i.1 j i.2
  rw [← RingHom.algebraMap_toAlgebra
    (chartBaseMap (equationIdeal p hp) j)]
  rw [← IsScalarTower.algebraMap_eq k
    (ChartRing (equationIdeal p hp) j)
    (Localization.Away (chartPDeriv p hp j i)),
    RingHom.isStandardSmooth_algebraMap]
  rw [← hjac]
  exact (jacobianLocalizedPresentation P).isStandardSmooth

/-- Two fibrewise regular functions on a smooth cubic chart have an Artinian common zero scheme.
The dimension hypothesis is supplied by the chartwise Jacobian criterion. -/
theorem isArtinianRing_quotient_pair_chartRing_of_fibrewiseRegularPair_of_span_pderiv
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (hspan : Ideal.span (Set.range (chartPDeriv p hp j)) = ⊤)
    (a b : ChartRing (equationIdeal p hp) j)
    (hregular : IsFibrewiseRegularPair (chartBaseMap (equationIdeal p hp) j) a b) :
    IsArtinianRing
      (ChartRing (equationIdeal p hp) j ⧸ (Ideal.span {a} ⊔ Ideal.span {b})) := by
  have hsmooth := smooth_chartBaseMap_of_span_pderiv p hp j hspan
  rw [← RingHom.algebraMap_toAlgebra
    (chartBaseMap (equationIdeal p hp) j)] at hsmooth hregular
  letI : Algebra.Smooth k (ChartRing (equationIdeal p hp) j) := hsmooth
  letI : Algebra.FiniteType k (ChartRing (equationIdeal p hp) j) := inferInstance
  letI : IsNoetherianRing (ChartRing (equationIdeal p hp) j) :=
    Algebra.FiniteType.isNoetherianRing k (ChartRing (equationIdeal p hp) j)
  exact isArtinianRing_quotient_pair_of_fibrewiseRegularPair_of_all_maximal_localizations_dim_le_two
    (algebraMap k (ChartRing (equationIdeal p hp) j)) a b hregular
    (fun Q _ => ringKrullDim_localizationAtPrime_chartBaseMap_le_two_of_span_pderiv
      p hp j hspan Q)

/- A Jacobian calculation at the common zeros can be used directly, without
 first packaging the result as a fibrewise-regular pair.  This is the chart
 interface needed when Voisin's transversality argument is stated in terms of
 cotangent-space independence. -/
theorem isArtinianRing_quotient_pair_chartRing_of_cotangentParameters_of_span_pderiv
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (hspan : Ideal.span (Set.range (chartPDeriv p hp j)) = ⊤)
    (a b : ChartRing (equationIdeal p hp) j)
    (hparameters : ∀ (Q : Ideal (ChartRing (equationIdeal p hp) j)) [Q.IsMaximal],
      a ∈ Q → b ∈ Q →
      IsRegularLocalRing (Localization.AtPrime Q) ∧
      algebraMap (ChartRing (equationIdeal p hp) j) (Localization.AtPrime Q) a ∉
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) ^ 2 ∧
      algebraMap (ChartRing (equationIdeal p hp) j) (Localization.AtPrime Q) b ∉
        Ideal.span {algebraMap (ChartRing (equationIdeal p hp) j)
          (Localization.AtPrime Q) a} ⊔
          IsLocalRing.maximalIdeal (Localization.AtPrime Q) ^ 2) :
    IsArtinianRing
      (ChartRing (equationIdeal p hp) j ⧸ (Ideal.span {a} ⊔ Ideal.span {b})) := by
  have hsmooth := smooth_chartBaseMap_of_span_pderiv p hp j hspan
  rw [← RingHom.algebraMap_toAlgebra
    (chartBaseMap (equationIdeal p hp) j)] at hsmooth
  letI : Algebra.Smooth k (ChartRing (equationIdeal p hp) j) := hsmooth
  letI : Algebra.FiniteType k (ChartRing (equationIdeal p hp) j) := inferInstance
  letI : IsNoetherianRing (ChartRing (equationIdeal p hp) j) :=
    Algebra.FiniteType.isNoetherianRing k (ChartRing (equationIdeal p hp) j)
  exact
    isArtinianRing_quotient_pair_of_cotangentIndependentParameters_at_all_common_maximal_localizations_dim_le_two
      a b hparameters
      (fun Q _ => ringKrullDim_localizationAtPrime_chartBaseMap_le_two_of_span_pderiv
        p hp j hspan Q)

/-- Homogeneous coordinates with a nonzero partial derivative define an
actual point in the relative smooth locus of a projective cubic
hypersurface.  The coefficient ring is arbitrary; only the target of the
point is required to be a field. -/
theorem exists_hypersurface_point_mem_smoothLocus_of_pderiv
    [IsNoetherianRing k] {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (f : k →+* K) (x : Fin 4 → K) (hx : x ≠ 0)
    (he : p.eval₂ f x = 0)
    (hderiv : ∃ i : Fin 4, (pderiv i p).eval₂ f x ≠ 0) :
    ∃ q : Spec (.of K) ⟶ hypersurface p hp,
      q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom f) ∧
      q (IsLocalRing.closedPoint K) ∈ (hypersurfaceToBase p hp).smoothLocus := by
  classical
  change ∃ q : Spec (.of K) ⟶ scheme (equationIdeal p hp),
    q ≫ toBase (equationIdeal p hp) = Spec.map (CommRingCat.ofHom f) ∧
    q (IsLocalRing.closedPoint K) ∈ (toBase (equationIdeal p hp)).smoothLocus
  obtain ⟨i, hi⟩ := hderiv
  obtain ⟨j, hji, hxj⟩ : ∃ j : Fin 4, j ≠ i ∧ x j ≠ 0 := by
    by_contra h
    push Not at h
    have hxi : x i ≠ 0 := by
      intro hxi
      apply hx
      funext a
      by_cases hai : a = i
      · simpa [hai] using hxi
      · exact h a hai
    have hsum :
        (∑ a : Fin 4, x a * (pderiv a p).eval₂ f x) =
          x i * (pderiv i p).eval₂ f x := by
      apply Finset.sum_eq_single i
      · intro a _ hai
        rw [h a hai, zero_mul]
      · simp
    have heuler : (∑ a : Fin 4, x a * (pderiv a p).eval₂ f x) = 0 := by
      calc
        (∑ a : Fin 4, x a * (pderiv a p).eval₂ f x) =
            (∑ a : Fin 4, X a * pderiv a p).eval₂ f x := by simp
        _ = (3 • p).eval₂ f x := by rw [hp.sum_X_mul_pderiv]
        _ = 0 := by simp [he]
    exact (mul_ne_zero hxi hi) (hsum ▸ heuler)
  have hij : i ≠ j := Ne.symm hji
  let y : Fin 4 → K := (x j)⁻¹ • x
  have hyj : y j = 1 := by simp [y, hxj]
  have hy : y ≠ 0 := by
    intro hy
    have := congrFun hy j
    simpa [hyj] using this
  have hey : p.eval₂ f y = 0 := by
    change p.eval₂ f ((x j)⁻¹ • x) = 0
    rw [eval₂_homogeneous_smul p hp, he, mul_zero]
  have hdy : (pderiv i p).eval₂ f y ≠ 0 := by
    change (pderiv i p).eval₂ f ((x j)⁻¹ • x) ≠ 0
    rw [eval₂_homogeneous_smul (pderiv i p) hp.pderiv]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hxj)) hi
  let Q := MvPolynomial (Fin 4) k ⧸
    Ideal.span (Set.range (hypersurfaceChartRelations p j))
  let e₀ : MvPolynomial (Fin 4) k →+* K := MvPolynomial.eval₂Hom f y
  have hspan : Ideal.span (Set.range (hypersurfaceChartRelations p j)) ≤
      RingHom.ker e₀ := by
    apply Ideal.span_le.mpr
    rintro r ⟨a, rfl⟩
    fin_cases a
    · exact hey
    · simp [hypersurfaceChartRelations, e₀, hyj]
  have hrel : ∀ r ∈ Ideal.span (Set.range (hypersurfaceChartRelations p j)),
      e₀ r = 0 := fun r hr ↦ hspan hr
  let e : Q →+* K := Ideal.Quotient.lift _ e₀ hrel
  let E := hypersurfaceChartRelationsEquiv p hp j
  let a : ChartRing (equationIdeal p hp) j →+* K := e.comp E.symm.toRingHom
  have ha_base : a.comp (chartBaseMap (equationIdeal p hp) j) = f := by
    ext r
    have hr : E.symm (chartBaseMap (equationIdeal p hp) j r) =
        Ideal.Quotient.mk _ (C r) := by
      apply E.injective
      simp [E, hypersurfaceChartRelationsEquiv_mk]
    change e (E.symm (chartBaseMap (equationIdeal p hp) j r)) = f r
    rw [hr]
    change (Ideal.Quotient.lift _ e₀ hrel) (Ideal.Quotient.mk _ (C r)) = f r
    rw [Ideal.Quotient.lift_mk]
    simp [e₀]
  let P := hypersurfaceChartPrePresentation p hp i j hij
  have hjac : P.jacobian =
      (pderiv i p).eval₂ (chartBaseMap (equationIdeal p hp) j)
        (chartCoordinate (equationIdeal p hp) j) :=
    hypersurfaceChartPrePresentation_jacobian p hp i j hij
  have ha_jac : a P.jacobian = (pderiv i p).eval₂ f y := by
    rw [hjac]
    have hr : E.symm
        ((pderiv i p).eval₂ (chartBaseMap (equationIdeal p hp) j)
          (chartCoordinate (equationIdeal p hp) j)) =
        Ideal.Quotient.mk _ (pderiv i p) := by
      apply E.injective
      simp [E, hypersurfaceChartRelationsEquiv_mk]
    change e (E.symm
      ((pderiv i p).eval₂ (chartBaseMap (equationIdeal p hp) j)
        (chartCoordinate (equationIdeal p hp) j))) = (pderiv i p).eval₂ f y
    rw [hr]
    change (Ideal.Quotient.lift _ e₀ hrel)
      (Ideal.Quotient.mk _ (pderiv i p)) = (pderiv i p).eval₂ f y
    rw [Ideal.Quotient.lift_mk]
    rfl
  have hajac : IsUnit (a P.jacobian) :=
    isUnit_iff_ne_zero.mpr (ha_jac.symm ▸ hdy)
  let A := Localization.Away P.jacobian
  let l : A →+* K := IsLocalization.Away.lift P.jacobian hajac
  let c : ChartRing (equationIdeal p hp) j →+* A := algebraMap _ _
  have hlc : l.comp c = a := by
    ext r
    change IsLocalization.Away.lift P.jacobian hajac
      (algebraMap (ChartRing (equationIdeal p hp) j) A r) = a r
    rw [IsLocalization.Away.lift_eq]
  let q : Spec (.of K) ⟶ scheme (equationIdeal p hp) :=
    Spec.map (CommRingCat.ofHom a) ≫ chartι (equationIdeal p hp) j
  have hq : q ≫ toBase (equationIdeal p hp) = Spec.map (CommRingCat.ofHom f) := by
    dsimp only [q]
    rw [Category.assoc, chartι_toBase, ← Spec.map_comp]
    exact congrArg (fun h : k →+* K ↦ Spec.map (CommRingCat.ofHom h)) ha_base
  let u : Spec (.of A) ⟶ scheme (equationIdeal p hp) :=
    Spec.map (CommRingCat.ofHom c) ≫ chartι (equationIdeal p hp) j
  have hu_smooth : Smooth (u ≫ toBase (equationIdeal p hp)) := by
    letI : Algebra.IsStandardSmooth k A :=
      (jacobianLocalizedPresentation P).isStandardSmooth
    have hc : c.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap k A := by
      rw [← RingHom.algebraMap_toAlgebra
        (chartBaseMap (equationIdeal p hp) j)]
      exact IsScalarTower.algebraMap_eq k _ A
    dsimp only [u]
    rw [Category.assoc, chartι_toBase, ← Spec.map_comp]
    change Smooth (Spec.map (CommRingCat.ofHom
      (c.comp (chartBaseMap (equationIdeal p hp) j))))
    rw [hc]
    exact (HasRingHomProperty.Spec_iff (P := @Smooth.{u})).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  have hfactor : Spec.map (CommRingCat.ofHom l) ≫ u = q := by
    dsimp only [u, q]
    change (Spec.map (CommRingCat.ofHom l) ≫ Spec.map (CommRingCat.ofHom c)) ≫
      chartι (equationIdeal p hp) j =
        Spec.map (CommRingCat.ofHom a) ≫ chartι (equationIdeal p hp) j
    rw [← Spec.map_comp]
    exact congrArg
      (fun h : ChartRing (equationIdeal p hp) j →+* K ↦
        Spec.map (CommRingCat.ofHom h) ≫ chartι (equationIdeal p hp) j) hlc
  let xK : Spec (.of K) := IsLocalRing.closedPoint K
  letI : IsOpenImmersion u := by
    dsimp only [u]
    infer_instance
  have hs :
      u (Spec.map (CommRingCat.ofHom l) xK) ∈
        (toBase (equationIdeal p hp)).smoothLocus := by
    have ht : Spec.map (CommRingCat.ofHom l) xK ∈
        (u ≫ toBase (equationIdeal p hp)).smoothLocus := by
      rw [(u ≫ toBase (equationIdeal p hp)).smoothLocus_eq_top]
      trivial
    rw [← Scheme.Hom.preimage_smoothLocus_eq] at ht
    exact ht
  refine ⟨q, hq, ?_⟩
  have hpoint := congrArg
    (fun m : Spec (.of K) ⟶ scheme (equationIdeal p hp) ↦ m xK) hfactor
  change u (Spec.map (CommRingCat.ofHom l) xK) = q xK at hpoint
  change q xK ∈ (toBase (equationIdeal p hp)).smoothLocus
  rw [← hpoint]
  exact hs

/-- Chartwise Jacobian covers prove smoothness of the projective
hypersurface. -/
theorem smooth_hypersurface_of_chart_pderiv_span
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hspan : ∀ j : Fin 4, Ideal.span (Set.range (chartPDeriv p hp j)) = ⊤) :
    Smooth (hypersurfaceToBase p hp) := by
  have : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth.{u})
    (coordinateOpenCover (equationIdeal p hp)).openCover).mpr
  intro j
  change Fin 4 at j
  dsimp only [hypersurfaceToBase, hypersurface]
  change Smooth (chartι (equationIdeal p hp) j ≫ toBase (equationIdeal p hp))
  rw [chartι_toBase]
  exact (HasRingHomProperty.Spec_iff (P := @Smooth.{u})).mpr
    (smooth_chartBaseMap_of_span_pderiv p hp j (hspan j))

/-- A projective hypersurface whose Jacobian basic opens cover every
normalized chart is smooth of relative dimension two. -/
theorem smoothOfRelativeDimension_two_hypersurface_of_chart_pderiv_span
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hspan : ∀ j : Fin 4, Ideal.span (Set.range (chartPDeriv p hp j)) = ⊤) :
    SmoothOfRelativeDimension 2 (hypersurfaceToBase p hp) := by
  letI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 2) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 2))
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension 2)
    (coordinateOpenCover (equationIdeal p hp)).openCover
  intro j
  change Fin 4 at j
  dsimp only [hypersurfaceToBase, hypersurface]
  change SmoothOfRelativeDimension 2
    (chartι (equationIdeal p hp) j ≫ toBase (equationIdeal p hp))
  rw [chartι_toBase]
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 2)).mpr
  change RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 2)
    (chartBaseMap (equationIdeal p hp) j)
  exact locally_standardSmoothOfRelativeDimension_two_chartBaseMap_of_span_pderiv
    p hp j (hspan j)

end HomogeneousProjective
end AllCharacteristics
