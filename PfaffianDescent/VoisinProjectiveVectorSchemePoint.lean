import PfaffianDescent.LinearNormalizedProjectivePoint
import PfaffianDescent.ProjectiveVectorIdeal
import PfaffianDescent.CubicSurfacePointEvaluation

/-!
# Scheme points from nonzero vectors on a projective zero locus

A nonzero vector annihilating a homogeneous ideal gives a rational point of
the corresponding projective scheme. The chosen nonzero coordinate is used
only to normalize a degree-one form to value one.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

private noncomputable def vectorNormalizingLinear
    {K : Type u} [Field K] (v : Fin 4 → K) (j : Fin 4) :
    MvPolynomial (Fin 4) K := C (v j)⁻¹ * X j

private theorem vectorNormalizingLinear_homogeneous
    {K : Type u} [Field K] (v : Fin 4 → K) (j : Fin 4) :
    (vectorNormalizingLinear v j).IsHomogeneous 1 :=
  isHomogeneous_C_mul_X (v j)⁻¹ j

private theorem vectorNormalizingLinear_eval_one
    {K : Type u} [Field K] (v : Fin 4 → K)
    (j : Fin 4) (hj : v j ≠ 0) :
    (vectorNormalizingLinear v j).eval v = 1 := by
  simp [vectorNormalizingLinear, hj]

/-- A vector zero of a homogeneous ideal, normalized at one nonzero
coordinate, determines an actual rational point of its projective scheme. -/
noncomputable def projectiveVectorSchemePointAt
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (v : Fin 4 → K)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (j : Fin 4) (hj : v j ≠ 0) :
    Spec (.of K) ⟶ scheme I := by
  let ell := vectorNormalizingLinear v j
  let z : CoordinateRing I := Ideal.Quotient.mk I.toIdeal ell
  have hell : ell.IsHomogeneous 1 := vectorNormalizingLinear_homogeneous v j
  have hz : z ∈ grading I 1 := polynomial_class_mem_grading I ell hell
  have he : ∀ p ∈ I.toIdeal,
      (eval₂Hom (algebraMap K K) v) p = 0 := by
    intro p hp
    simpa using hv p hp
  have hOne :
      (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K K) v) he) z = 1 := by
    change (eval₂Hom (algebraMap K K) v) ell = 1
    simpa using vectorNormalizingLinear_eval_one v j hj
  exact linearNormalizedPointAt I v he z hz hOne

/-- The vector-constructed point lies over the identity point of the
coefficient field. -/
theorem projectiveVectorSchemePointAt_toBase
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (v : Fin 4 → K)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (j : Fin 4) (hj : v j ≠ 0) :
    projectiveVectorSchemePointAt I v hv j hj ≫ toBase I =
      Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
  let ell := vectorNormalizingLinear v j
  let z : CoordinateRing I := Ideal.Quotient.mk I.toIdeal ell
  have hell : ell.IsHomogeneous 1 := vectorNormalizingLinear_homogeneous v j
  have hz : z ∈ grading I 1 := polynomial_class_mem_grading I ell hell
  have he : ∀ p ∈ I.toIdeal,
      (eval₂Hom (algebraMap K K) v) p = 0 := by
    intro p hp
    simpa using hv p hp
  have hOne :
      (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K K) v) he) z = 1 := by
    change (eval₂Hom (algebraMap K K) v) ell = 1
    simpa using vectorNormalizingLinear_eval_one v j hj
  simpa only [projectiveVectorSchemePointAt] using
    (linearNormalizedPointAt_toBase I v he z hz hOne)

/-- Every nonzero vector on the affine cone of a homogeneous ideal gives a
rational point of its projective scheme. -/
theorem exists_projectiveVectorSchemePoint_of_nonzero_zero
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (v : Fin 4 → K) (hv0 : v ≠ 0)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0) :
    ∃ t : Spec (.of K) ⟶ scheme I,
      t ≫ toBase I = Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
  obtain ⟨j, hj⟩ : ∃ j : Fin 4, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  exact ⟨projectiveVectorSchemePointAt I v hv j hj,
    projectiveVectorSchemePointAt_toBase I v hv j hj⟩

/-- In the coordinate chart `j`, a vector with coordinate `1` gives a
point represented by the same chart ring homomorphism used in the general
normalized-point construction. -/
noncomputable def projectiveUnitVectorSchemePointAt
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (v : Fin 4 → K)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (j : Fin 4) (hj : v j = 1) :
    Spec (.of K) ⟶ scheme I := by
  have he : ∀ p ∈ I.toIdeal,
      (eval₂Hom (algebraMap K K) v) p = 0 := by
    intro p hp
    simpa using hv p hp
  have hOne :
      (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K K) v) he)
        (coordinate I j) = 1 := by
    change (eval₂Hom (algebraMap K K) v) (X j) = 1
    simpa using hj
  exact linearNormalizedPointAt I v he (coordinate I j) (coordinate_mem I j) hOne

theorem projectiveUnitVectorSchemePointAt_toBase
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (v : Fin 4 → K)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (j : Fin 4) (hj : v j = 1) :
    projectiveUnitVectorSchemePointAt I v hv j hj ≫ toBase I =
      Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
  have he : ∀ p ∈ I.toIdeal,
      (eval₂Hom (algebraMap K K) v) p = 0 := by
    intro p hp
    simpa using hv p hp
  have hOne :
      (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K K) v) he)
        (coordinate I j) = 1 := by
    change (eval₂Hom (algebraMap K K) v) (X j) = 1
    simpa using hj
  simpa only [projectiveUnitVectorSchemePointAt] using
    (linearNormalizedPointAt_toBase I v he (coordinate I j)
      (coordinate_mem I j) hOne)

/-- Distinct vectors normalized to `1` in one coordinate determine distinct
rational points of the projective scheme. -/
theorem projectiveUnitVectorSchemePointAt_injective
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (j : Fin 4)
    {v w : Fin 4 → K}
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (hw : ∀ p ∈ I.toIdeal, p.eval w = 0)
    (hvj : v j = 1) (hwj : w j = 1)
    (h : projectiveUnitVectorSchemePointAt I v hv j hvj =
      projectiveUnitVectorSchemePointAt I w hw j hwj) : v = w := by
  simp only [projectiveUnitVectorSchemePointAt, linearNormalizedPointAt] at h
  have hmaps := (cancel_mono (Proj.awayι (grading I) (coordinate I j)
    (coordinate_mem I j) (by decide : 0 < 1))).mp h
  have h := Spec.map_injective hmaps
  funext k
  have hk := congrArg (fun g : CommRingCat.of (Away (grading I) (coordinate I j)) ⟶
      CommRingCat.of K =>
    g (linearChartCoordinate I (coordinate I j) (coordinate_mem I j) k)) h
  have heV : ∀ p ∈ I.toIdeal,
      (eval₂Hom (algebraMap K K) v) p = 0 := by
    intro p hp
    simpa using hv p hp
  have heW : ∀ p ∈ I.toIdeal,
      (eval₂Hom (algebraMap K K) w) p = 0 := by
    intro p hp
    simpa using hw p hp
  have hOneV :
      (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K K) v) heV)
        (coordinate I j) = 1 := by
    change (eval₂Hom (algebraMap K K) v) (X j) = 1
    simpa using hvj
  have hOneW :
      (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K K) w) heW)
        (coordinate I j) = 1 := by
    change (eval₂Hom (algebraMap K K) w) (X j) = 1
    simpa using hwj
  change linearNormalizedPointChartMapAt I v heV (coordinate I j)
      (coordinate_mem I j) hOneV
        (linearChartCoordinate I (coordinate I j) (coordinate_mem I j) k) =
    linearNormalizedPointChartMapAt I w heW (coordinate I j)
      (coordinate_mem I j) hOneW
        (linearChartCoordinate I (coordinate I j) (coordinate_mem I j) k) at hk
  rw [linearNormalizedPointChartMapAt_coordinate I v heV (coordinate I j)
      (coordinate_mem I j) hOneV k,
    linearNormalizedPointChartMapAt_coordinate I w heW (coordinate I j)
      (coordinate_mem I j) hOneW k] at hk
  exact hk

/-- The affine roots `t • a + b` of a line restriction remain distinct after
passing to projective directions, provided `a` and `b` span a genuine line. -/
theorem affineLineRoots_projectively_distinct
    {K : Type u} [Field K]
    {a b : Fin 4 → K}
    (hind : ∀ s t : K, s • a + t • b = 0 → s = 0 ∧ t = 0)
    {ι : Type*} {x : ι → Fin 4 → K}
    (hinj : Function.Injective x)
    (hform : ∀ i, ∃ t : K, x i = t • a + b)
    {i j : ι} (hij : i ≠ j) (c : K) : c • x i ≠ x j := by
  intro h
  obtain ⟨s, hs⟩ := hform i
  obtain ⟨t, ht⟩ := hform j
  have hzero : (c * s - t) • a + (c - 1) • b = 0 := by
    have h' : c • (s • a + b) = t • a + b := by simpa [hs, ht] using h
    funext k
    have hk := congrFun h' k
    simp only [Pi.add_apply, Pi.smul_apply] at hk ⊢
    simp only [Pi.zero_apply]
    calc
      (c * s - t) * a k + (c - 1) * b k =
          (c * (s * a k + b k) - (t * a k + b k)) := by ring
      _ = 0 := sub_eq_zero.mpr (by simpa [mul_add] using hk)
  have hc : c = 1 := sub_eq_zero.mp (hind _ _ hzero).2
  apply hij
  apply hinj
  simpa [hc] using h

/-- A finite family of nonzero vectors can be placed in one common
projective chart defined by a homogeneous linear form. -/
theorem exists_common_linear_chart_for_nonzero_vectors
    {K : Type u} [Field K] [Infinite K]
    {ι : Type*} [Finite ι]
    (x : ι → Fin 4 → K) (hx : ∀ i, x i ≠ 0) :
    ∃ c : Fin 4 → K, ∀ i,
      (homogeneousLinearForm c).eval (x i) ≠ 0 := by
  classical
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := K) x hx
  let c : Fin 4 → K := fun j => f (Pi.single j 1)
  refine ⟨c, ?_⟩
  intro i
  have hsum : x i = ∑ j, x i j • Pi.single j 1 := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [hkj.symm]
    · simp
  have hfi : f (x i) ≠ 0 := hf i
  rw [hsum, map_sum] at hfi
  have hdot : ∑ j, c j * x i j ≠ 0 := by
    simpa [c, smul_eq_mul, mul_comm] using hfi
  rw [← homogeneousLinearForm_eval, MvPolynomial.aeval_eq_eval] at hdot
  exact hdot

/-- A fixed normalized projective chart remembers every coordinate of its
field-valued point. This allows points normalized by a common linear form
to be compared without choosing one standard coordinate. -/
theorem linearNormalizedPointAt_injective_on_vectors
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    {v w : Fin 4 → K}
    (heV : ∀ p ∈ I.toIdeal,
      (eval₂Hom (algebraMap K K) v) p = 0)
    (heW : ∀ p ∈ I.toIdeal,
      (eval₂Hom (algebraMap K K) w) p = 0)
    (hOneV : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K K) v) heV) z = 1)
    (hOneW : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K K) w) heW) z = 1)
    (h : linearNormalizedPointAt I v heV z hz hOneV =
      linearNormalizedPointAt I w heW z hz hOneW) : v = w := by
  simp only [linearNormalizedPointAt] at h
  have hmaps := (cancel_mono (Proj.awayι (grading I) z hz
    (by decide : 0 < 1))).mp h
  have hring := Spec.map_injective hmaps
  funext k
  have hk := congrArg (fun g : CommRingCat.of (Away (grading I) z) ⟶
      CommRingCat.of K => g (linearChartCoordinate I z hz k)) hring
  change linearNormalizedPointChartMapAt I v heV z hz hOneV
      (linearChartCoordinate I z hz k) =
    linearNormalizedPointChartMapAt I w heW z hz hOneW
      (linearChartCoordinate I z hz k) at hk
  rw [linearNormalizedPointChartMapAt_coordinate I v heV z hz hOneV k,
    linearNormalizedPointChartMapAt_coordinate I w heW z hz hOneW k] at hk
  exact hk

/-- Construct a point from a vector normalized by a chosen homogeneous
linear form. All such points use the same Proj chart. -/
noncomputable def projectiveLinearNormalizedVectorSchemePoint
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (c v : Fin 4 → K)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (hOne : (homogeneousLinearForm c).eval v = 1) :
    Spec (.of K) ⟶ scheme I := by
  let z : CoordinateRing I := Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c)
  have hz : z ∈ grading I 1 := polynomial_class_mem_grading I
    (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
  have he : ∀ p ∈ I.toIdeal,
      (eval₂Hom (algebraMap K K) v) p = 0 := by
    intro p hp
    simpa using hv p hp
  have hOne' :
      (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K K) v) he) z = 1 := by
    change (eval₂Hom (algebraMap K K) v) (homogeneousLinearForm c) = 1
    simpa using hOne
  exact linearNormalizedPointAt I v he z hz hOne'

theorem projectiveLinearNormalizedVectorSchemePoint_toBase
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (c v : Fin 4 → K)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (hOne : (homogeneousLinearForm c).eval v = 1) :
    projectiveLinearNormalizedVectorSchemePoint I c v hv hOne ≫ toBase I =
      Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
  let z : CoordinateRing I := Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c)
  have hz : z ∈ grading I 1 := polynomial_class_mem_grading I
    (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
  have he : ∀ p ∈ I.toIdeal,
      (eval₂Hom (algebraMap K K) v) p = 0 := by
    intro p hp
    simpa using hv p hp
  have hOne' :
      (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K K) v) he) z = 1 := by
    change (eval₂Hom (algebraMap K K) v) (homogeneousLinearForm c) = 1
    simpa using hOne
  simpa only [projectiveLinearNormalizedVectorSchemePoint] using
    (linearNormalizedPointAt_toBase I v he z hz hOne')

/-- The affine cone of a homogeneous ideal is invariant under scalar
rescaling, including rescaling by zero. -/
theorem homogeneousIdeal_vector_zero_smul
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (v : Fin 4 → K)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (c : K) :
    ∀ p ∈ I.toIdeal, p.eval (c • v) = 0 := by
  intro p hp
  change (eval₂Hom (RingHom.id K) (c • v)) p = 0
  rw [← MvPolynomial.sum_homogeneousComponent p, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have hcomp : homogeneousComponent d p ∈ I.toIdeal := by
    rw [← decomposition.decompose'_apply]
    exact I.isHomogeneous d hp
  change (homogeneousComponent d p).eval₂ (RingHom.id K) (c • v) = 0
  rw [AllCharacteristics.eval₂_homogeneous_smul
    (homogeneousComponent d p) (homogeneousComponent_isHomogeneous d p)]
  have hzero : (homogeneousComponent d p).eval₂ (RingHom.id K) v = 0 := by
    simpa using hv _ hcomp
  simp [hzero]

/-- Normalize a nonzero vector with respect to a chosen linear form. -/
noncomputable def normalizedVectorInLinearChart
    {K : Type u} [Field K]
    (c v : Fin 4 → K) : Fin 4 → K :=
  ((homogeneousLinearForm c).eval v)⁻¹ • v

theorem normalizedVectorInLinearChart_eval_one
    {K : Type u} [Field K]
    (c v : Fin 4 → K)
    (hv : (homogeneousLinearForm c).eval v ≠ 0) :
    (homogeneousLinearForm c).eval (normalizedVectorInLinearChart c v) = 1 := by
  change (homogeneousLinearForm c).eval₂ (RingHom.id K)
    (((homogeneousLinearForm c).eval v)⁻¹ • v) = 1
  rw [AllCharacteristics.eval₂_homogeneous_smul
    (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)]
  rw [MvPolynomial.eval₂_id]
  simpa only [pow_one] using inv_mul_cancel₀ hv

theorem normalizedVectorInLinearChart_zero
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (c v : Fin 4 → K)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0) :
    ∀ p ∈ I.toIdeal,
      p.eval (normalizedVectorInLinearChart c v) = 0 :=
  homogeneousIdeal_vector_zero_smul I v hv _

/-- A vector zero whose chosen linear form is nonzero gives a rational
scheme point in that form's common chart. -/
noncomputable def projectiveVectorSchemePointInLinearChart
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (c v : Fin 4 → K)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (hcv : (homogeneousLinearForm c).eval v ≠ 0) :
    Spec (.of K) ⟶ scheme I :=
  projectiveLinearNormalizedVectorSchemePoint I c
    (normalizedVectorInLinearChart c v)
    (normalizedVectorInLinearChart_zero I c v hv)
    (normalizedVectorInLinearChart_eval_one c v hcv)

theorem projectiveVectorSchemePointInLinearChart_toBase
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (c v : Fin 4 → K)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (hcv : (homogeneousLinearForm c).eval v ≠ 0) :
    projectiveVectorSchemePointInLinearChart I c v hv hcv ≫ toBase I =
      Spec.map (CommRingCat.ofHom (RingHom.id K)) :=
  projectiveLinearNormalizedVectorSchemePoint_toBase I c
    (normalizedVectorInLinearChart c v)
    (normalizedVectorInLinearChart_zero I c v hv)
    (normalizedVectorInLinearChart_eval_one c v hcv)

/-- The point constructed from a vector really lies in the basic affine
open cut out by the chosen linear form. -/
theorem projectiveVectorSchemePointInLinearChart_mem_basicOpen
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (c v : Fin 4 → K)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (hcv : (homogeneousLinearForm c).eval v ≠ 0) :
    projectiveVectorSchemePointInLinearChart I c v hv hcv
        (IsLocalRing.closedPoint K) ∈
      Proj.basicOpen (grading I)
        (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c)) := by
  let z : CoordinateRing I :=
    Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c)
  have hz : z ∈ grading I 1 := polynomial_class_mem_grading I
    (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
  rw [← Proj.opensRange_awayι (grading I) z hz (by decide : 0 < 1)]
  unfold projectiveVectorSchemePointInLinearChart
    projectiveLinearNormalizedVectorSchemePoint linearNormalizedPointAt
  exact ⟨_, rfl⟩

theorem normalizedVectorInLinearChart_eq_imp_proportional
    {K : Type u} [Field K]
    (c v w : Fin 4 → K)
    (hw : (homogeneousLinearForm c).eval w ≠ 0)
    (h : normalizedVectorInLinearChart c v =
      normalizedVectorInLinearChart c w) :
    ∃ a : K, a • v = w := by
  let lv := (homogeneousLinearForm c).eval v
  let lw := (homogeneousLinearForm c).eval w
  refine ⟨lw * lv⁻¹, ?_⟩
  have h' := congrArg (fun y : Fin 4 → K => lw • y) h
  change lw • (lv⁻¹ • v) = lw • (lw⁻¹ • w) at h'
  rw [smul_smul, smul_smul, mul_inv_cancel₀ hw, one_smul] at h'
  exact h'

/-- In one fixed linear chart, normalized vector zeros give distinct scheme
points exactly when their coordinate vectors differ. -/
theorem projectiveLinearNormalizedVectorSchemePoint_injective
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (c : Fin 4 → K)
    {v w : Fin 4 → K}
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (hw : ∀ p ∈ I.toIdeal, p.eval w = 0)
    (hOneV : (homogeneousLinearForm c).eval v = 1)
    (hOneW : (homogeneousLinearForm c).eval w = 1)
    (h : projectiveLinearNormalizedVectorSchemePoint I c v hv hOneV =
      projectiveLinearNormalizedVectorSchemePoint I c w hw hOneW) : v = w := by
  let z : CoordinateRing I := Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c)
  have hz : z ∈ grading I 1 := polynomial_class_mem_grading I
    (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
  have heV : ∀ p ∈ I.toIdeal,
      (eval₂Hom (algebraMap K K) v) p = 0 := by
    intro p hp
    simpa using hv p hp
  have heW : ∀ p ∈ I.toIdeal,
      (eval₂Hom (algebraMap K K) w) p = 0 := by
    intro p hp
    simpa using hw p hp
  have hOneV' :
      (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K K) v) heV) z = 1 := by
    change (eval₂Hom (algebraMap K K) v) (homogeneousLinearForm c) = 1
    simpa using hOneV
  have hOneW' :
      (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K K) w) heW) z = 1 := by
    change (eval₂Hom (algebraMap K K) w) (homogeneousLinearForm c) = 1
    simpa using hOneW
  have h' : linearNormalizedPointAt I v heV z hz hOneV' =
      linearNormalizedPointAt I w heW z hz hOneW' := by
    simpa only [projectiveLinearNormalizedVectorSchemePoint] using h
  exact linearNormalizedPointAt_injective_on_vectors I z hz
    heV heW hOneV' hOneW' h'

/-- Distinct projective directions in a common linear chart yield distinct
field-valued points of the projective scheme. -/
theorem projectiveVectorSchemePointInLinearChart_ne_of_directions
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (c : Fin 4 → K)
    {v w : Fin 4 → K}
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (hw : ∀ p ∈ I.toIdeal, p.eval w = 0)
    (hcv : (homogeneousLinearForm c).eval v ≠ 0)
    (hcw : (homogeneousLinearForm c).eval w ≠ 0)
    (hdir : ∀ a : K, a • v ≠ w) :
    projectiveVectorSchemePointInLinearChart I c v hv hcv ≠
      projectiveVectorSchemePointInLinearChart I c w hw hcw := by
  intro h
  have hnorm : normalizedVectorInLinearChart c v =
      normalizedVectorInLinearChart c w :=
    projectiveLinearNormalizedVectorSchemePoint_injective I c
      (normalizedVectorInLinearChart_zero I c v hv)
      (normalizedVectorInLinearChart_zero I c w hw)
      (normalizedVectorInLinearChart_eval_one c v hcv)
      (normalizedVectorInLinearChart_eval_one c w hcw) h
  obtain ⟨a, ha⟩ := normalizedVectorInLinearChart_eq_imp_proportional
    c v w hcw hnorm
  exact hdir a ha

/-- A finite family of nonzero vector zeros with pairwise distinct
projective directions gives the same number of distinct rational sections
of the corresponding projective scheme. -/
theorem exists_distinct_projective_scheme_points_of_vector_directions
    {K : Type u} [Field K] [Infinite K]
    {ι : Type*} [Finite ι]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (x : ι → Fin 4 → K)
    (hzero : ∀ i, ∀ p ∈ I.toIdeal, p.eval (x i) = 0)
    (hnonzero : ∀ i, x i ≠ 0)
    (hdirections : ∀ i j, i ≠ j → ∀ a : K, a • x i ≠ x j) :
    ∃ t : ι → (Spec (.of K) ⟶ scheme I),
      (∀ i, t i ≫ toBase I =
        Spec.map (CommRingCat.ofHom (RingHom.id K))) ∧
      Function.Injective t := by
  obtain ⟨c, hc⟩ := exists_common_linear_chart_for_nonzero_vectors x hnonzero
  let t : ι → (Spec (.of K) ⟶ scheme I) := fun i =>
    projectiveVectorSchemePointInLinearChart I c (x i) (hzero i) (hc i)
  refine ⟨t, ?_, ?_⟩
  · intro i
    exact projectiveVectorSchemePointInLinearChart_toBase I c (x i)
      (hzero i) (hc i)
  · intro i j hij
    by_contra hne
    exact (projectiveVectorSchemePointInLinearChart_ne_of_directions
      I c (hzero i) (hzero j) (hc i) (hc j)
      (hdirections i j hne)) hij

end PfaffianDescent
