import PfaffianDescent.TripleCompleteIntersectionJacobian

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

section

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The Jacobian of a specialized finite cubic combination is the same
finite combination of the individual Jacobian polynomials. -/
theorem tripleCompleteIntersectionChartJacobianPolynomial_sum_C_mul_map
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (j : Fin 4) (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (c : Fin n → L) :
    tripleCompleteIntersectionChartJacobianPolynomial
        (p.map f) (q.map f)
        (∑ i, C (c i) * (v i).1.map f) j =
      ∑ i, C (c i) *
        (tripleCompleteIntersectionChartJacobianPolynomial p q (v i).1 j).map f := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact tripleCompleteIntersectionChartJacobianPolynomial_zero_right
        (p.map f) (q.map f) j
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        tripleCompleteIntersectionChartJacobianPolynomial_add_right, ih,
        tripleCompleteIntersectionChartJacobianPolynomial_C_mul_right,
        ← tripleCompleteIntersectionChartJacobianPolynomial_map
          f p q (v i).1 hp hq (v i).2 j]

/-- The cubic with projective source coordinates as its coefficients. -/
noncomputable def tripleCompleteIntersectionUniversalCubic
    {n : ℕ}
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) :
    MvPolynomial (Fin 4) (MvPolynomial (Fin n) K) :=
  ∑ i, C (X i) * (v i).1.map C

/-- One universal chart-Jacobian component over the same source coordinates
as the moving cubic.  It is defined even when the component specializes to
the zero sextic. -/
noncomputable def tripleCompleteIntersectionUniversalChartJacobian
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) :
    MvPolynomial (Fin 4) (MvPolynomial (Fin n) K) :=
  ∑ i, C (X i) *
    (tripleCompleteIntersectionChartJacobianPolynomial p q (v i).1 j).map C

theorem tripleCompleteIntersectionUniversalCubic_isHomogeneous
    {n : ℕ}
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) :
    (tripleCompleteIntersectionUniversalCubic v).IsHomogeneous 3 := by
  classical
  apply IsHomogeneous.sum
  intro i hi
  exact ((v i).2.map C).C_mul _

theorem tripleCompleteIntersectionUniversalChartJacobian_isHomogeneous
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (j : Fin 4) (v : Fin n → homogeneousSubmodule (Fin 4) K 3) :
    (tripleCompleteIntersectionUniversalChartJacobian p q j v).IsHomogeneous 6 := by
  classical
  apply IsHomogeneous.sum
  intro i hi
  exact ((tripleCompleteIntersectionChartJacobianPolynomial_isHomogeneous
    p q (v i).1 hp hq (v i).2 j).map C).C_mul _

theorem tripleCompleteIntersectionUniversalCubic_coeff
    {n : ℕ}
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (m : Fin 4 →₀ ℕ) :
    (tripleCompleteIntersectionUniversalCubic v).coeff m =
      ∑ i, X i * C ((v i).1.coeff m) := by
  classical
  simp [tripleCompleteIntersectionUniversalCubic,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map]

/-- Every ambient coefficient of the universal cubic is linear homogeneous
in the common source-projective coordinates. -/
theorem tripleCompleteIntersectionUniversalCubic_coeff_isHomogeneous
    {n : ℕ}
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (m : Fin 4 →₀ ℕ) :
    ((tripleCompleteIntersectionUniversalCubic v).coeff m).IsHomogeneous 1 := by
  rw [tripleCompleteIntersectionUniversalCubic_coeff]
  apply IsHomogeneous.sum
  intro i hi
  simpa only [Nat.add_zero] using
    (MvPolynomial.isHomogeneous_X (R := K) i).mul
      (MvPolynomial.isHomogeneous_C (Fin n) ((v i).1.coeff m))

theorem tripleCompleteIntersectionUniversalChartJacobian_coeff
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (m : Fin 4 →₀ ℕ) :
    (tripleCompleteIntersectionUniversalChartJacobian p q j v).coeff m =
      ∑ i, X i * C
        ((tripleCompleteIntersectionChartJacobianPolynomial p q (v i).1 j).coeff m) := by
  classical
  simp [tripleCompleteIntersectionUniversalChartJacobian,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map]

/-- Every ambient coefficient of every universal Jacobian component is
linear homogeneous in the common source-projective coordinates, including
when all of those coefficients specialize to zero. -/
theorem tripleCompleteIntersectionUniversalChartJacobian_coeff_isHomogeneous
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (m : Fin 4 →₀ ℕ) :
    ((tripleCompleteIntersectionUniversalChartJacobian p q j v).coeff m).IsHomogeneous 1 := by
  rw [tripleCompleteIntersectionUniversalChartJacobian_coeff]
  apply IsHomogeneous.sum
  intro i hi
  simpa only [Nat.add_zero] using
    (MvPolynomial.isHomogeneous_X (R := K) i).mul
      (MvPolynomial.isHomogeneous_C (Fin n)
        ((tripleCompleteIntersectionChartJacobianPolynomial p q (v i).1 j).coeff m))

theorem tripleCompleteIntersectionUniversalCubic_map
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L) (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (c : Fin n → L) :
    (tripleCompleteIntersectionUniversalCubic v).map
        (MvPolynomial.eval₂Hom f c) =
      ∑ i, C (c i) * (v i).1.map f := by
  classical
  simp only [tripleCompleteIntersectionUniversalCubic, map_sum, map_mul,
    map_C, map_map]
  have hfc : (MvPolynomial.eval₂Hom f c).comp C = f := by
    ext a
    simp
  simp only [hfc]
  apply Finset.sum_congr rfl
  intro i hi
  rw [MvPolynomial.eval₂Hom_X']

/-- A nonzero projective source-coordinate vector specializes the universal
cubic to a nonzero equation whenever the source frame is independent. -/
theorem tripleCompleteIntersectionUniversalCubic_map_ne_zero
    {L : Type u} [Field L] {m n : ℕ}
    (f : K →+* L) (e : Fin m ≃ Monomials (Fin 4) 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (hv : LinearIndependent K v) (c : Fin n → L) (hc : c ≠ 0) :
    (tripleCompleteIntersectionUniversalCubic v).map
        (MvPolynomial.eval₂Hom f c) ≠ 0 := by
  rw [tripleCompleteIntersectionUniversalCubic_map f v c]
  exact homogeneousFrameCombination_map_ne_zero_of_ne_zero
    3 f e v hv c hc

theorem tripleCompleteIntersectionUniversalChartJacobian_map
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (j : Fin 4) (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (c : Fin n → L) :
    (tripleCompleteIntersectionUniversalChartJacobian p q j v).map
        (MvPolynomial.eval₂Hom f c) =
      tripleCompleteIntersectionChartJacobianPolynomial
        (p.map f) (q.map f)
        ((tripleCompleteIntersectionUniversalCubic v).map
          (MvPolynomial.eval₂Hom f c)) j := by
  rw [tripleCompleteIntersectionUniversalCubic_map f v c,
    tripleCompleteIntersectionUniversalChartJacobian]
  simp only [map_sum, map_mul, map_C, map_map]
  have hfc : (MvPolynomial.eval₂Hom f c).comp C = f := by
    ext a
    simp
  simp only [hfc]
  rw [tripleCompleteIntersectionChartJacobianPolynomial_sum_C_mul_map
    f p q hp hq j v c]
  apply Finset.sum_congr rfl
  intro i hi
  rw [MvPolynomial.eval₂Hom_X']

/-- The two fixed cubics, the moving cubic, and all four Jacobian components,
as equations over the affine cone of their common projective source
coordinates. -/
noncomputable def tripleCompleteIntersectionUniversalSingularEquationSet
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) :
    Set (MvPolynomial (Fin 4) (MvPolynomial (Fin n) K)) :=
  {p.map C, q.map C, tripleCompleteIntersectionUniversalCubic v} ∪
    Set.range (fun j : Fin 4 =>
      tripleCompleteIntersectionUniversalChartJacobian p q j v)

theorem tripleCompleteIntersectionUniversalSingularEquationSet_homogeneous
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) :
    ∀ r ∈ tripleCompleteIntersectionUniversalSingularEquationSet p q v,
      ∃ d, r.IsHomogeneous d := by
  intro r hr
  rcases hr with hr | hr
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨3, hp.map C⟩
    · exact ⟨3, hq.map C⟩
    · exact ⟨3, tripleCompleteIntersectionUniversalCubic_isHomogeneous v⟩
  · obtain ⟨j, rfl⟩ := hr
    exact ⟨6,
      tripleCompleteIntersectionUniversalChartJacobian_isHomogeneous
        p q hp hq j v⟩

/-- The seven simultaneous singularity equations of one specialized third
cubic. -/
noncomputable def tripleCompleteIntersectionSingularEquationSet
    {L : Type u} [Field L]
    (p q r : MvPolynomial (Fin 4) L) : Set (MvPolynomial (Fin 4) L) :=
  {p, q, r} ∪ Set.range (fun j : Fin 4 =>
    tripleCompleteIntersectionChartJacobianPolynomial p q r j)

/-- Specializing the common source coordinates carries the universal five
equations to the cubic and its four actual chart-Jacobian components. -/
theorem image_tripleCompleteIntersectionUniversalSingularEquationSet
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (c : Fin n → L) :
    (MvPolynomial.map (MvPolynomial.eval₂Hom f c)) ''
        tripleCompleteIntersectionUniversalSingularEquationSet p q v =
      tripleCompleteIntersectionSingularEquationSet (p.map f) (q.map f)
        ((tripleCompleteIntersectionUniversalCubic v).map
          (MvPolynomial.eval₂Hom f c)) := by
  have hfc : (MvPolynomial.eval₂Hom f c).comp C = f := by
    ext a
    simp
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases hr with hr | hr
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl | rfl
      · left
        rw [MvPolynomial.map_map, hfc]
        simp
      · left
        rw [MvPolynomial.map_map, hfc]
        simp
      · left
        simp
    · right
      obtain ⟨j, rfl⟩ := hr
      refine ⟨j, ?_⟩
      exact (tripleCompleteIntersectionUniversalChartJacobian_map
        f p q hp hq j v c).symm
  · intro hz
    rcases hz with hz | hz
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · refine ⟨p.map C, Or.inl (Or.inl rfl), ?_⟩
        rw [MvPolynomial.map_map, hfc]
      · refine ⟨q.map C, Or.inl (Or.inr (Or.inl rfl)), ?_⟩
        rw [MvPolynomial.map_map, hfc]
      · exact ⟨tripleCompleteIntersectionUniversalCubic v,
          Or.inl (Or.inr (Or.inr rfl)), rfl⟩
    · obtain ⟨j, rfl⟩ := hz
      refine ⟨tripleCompleteIntersectionUniversalChartJacobian p q j v,
        Or.inr ⟨j, rfl⟩, ?_⟩
      exact tripleCompleteIntersectionUniversalChartJacobian_map
        f p q hp hq j v c

noncomputable def tripleCompleteIntersectionSingularIdeal
    {L : Type u} [Field L]
    (p q r : MvPolynomial (Fin 4) L) : Ideal (MvPolynomial (Fin 4) L) :=
  Ideal.span (tripleCompleteIntersectionSingularEquationSet p q r)

theorem tripleCompleteIntersectionSingularEquationSet_homogeneous
    {L : Type u} [Field L]
    (p q r : MvPolynomial (Fin 4) L)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hr : r.IsHomogeneous 3) :
    ∀ s ∈ tripleCompleteIntersectionSingularEquationSet p q r,
      ∃ d, s.IsHomogeneous d := by
  intro s hs
  rcases hs with hs | hs
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨3, hp⟩
    · exact ⟨3, hq⟩
    · exact ⟨3, hr⟩
  · obtain ⟨j, rfl⟩ := hs
    exact ⟨6,
      tripleCompleteIntersectionChartJacobianPolynomial_isHomogeneous
        p q r hp hq hr j⟩

noncomputable def tripleCompleteIntersectionSingularHomogeneousIdeal
    {L : Type u} [Field L]
    (p q r : MvPolynomial (Fin 4) L)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hr : r.IsHomogeneous 3) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) L) :=
  ⟨tripleCompleteIntersectionSingularIdeal p q r,
    Ideal.homogeneous_span _ _
      (tripleCompleteIntersectionSingularEquationSet_homogeneous
        p q r hp hq hr)⟩

@[simp] theorem tripleCompleteIntersectionSingularHomogeneousIdeal_toIdeal
    {L : Type u} [Field L]
    (p q r : MvPolynomial (Fin 4) L)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hr : r.IsHomogeneous 3) :
    (tripleCompleteIntersectionSingularHomogeneousIdeal
      p q r hp hq hr).toIdeal =
      tripleCompleteIntersectionSingularIdeal p q r := rfl

/-- The relative projective zero scheme of the two fixed cubics, the universal
cubic, and all four Jacobian components over the affine parameter cone.
Unlike four separate maps to sextic projective space, this remains defined
when any component is identically zero at a parameter. -/
noncomputable def tripleCompleteIntersectionUniversalSingularHomogeneousIdeal
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) :
    HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (MvPolynomial (Fin n) K)) :=
  ⟨Ideal.span (tripleCompleteIntersectionUniversalSingularEquationSet p q v),
    Ideal.homogeneous_span _ _
      (tripleCompleteIntersectionUniversalSingularEquationSet_homogeneous
        p q hp hq v)⟩

/-- The fiber ideal of the universal simultaneous singularity family is the
ideal generated by the two fixed cubics, the specialized cubic, and its four
actual Jacobian components. -/
theorem tripleCompleteIntersectionUniversalSingularHomogeneousIdeal_map
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (c : Fin n → L) :
    (tripleCompleteIntersectionUniversalSingularHomogeneousIdeal
        p q hp hq v).toIdeal.map
        (MvPolynomial.map (MvPolynomial.eval₂Hom f c)) =
      tripleCompleteIntersectionSingularIdeal (p.map f) (q.map f)
        ((tripleCompleteIntersectionUniversalCubic v).map
          (MvPolynomial.eval₂Hom f c)) := by
  rw [tripleCompleteIntersectionUniversalSingularHomogeneousIdeal,
    tripleCompleteIntersectionSingularIdeal, Ideal.map_span,
    image_tripleCompleteIntersectionUniversalSingularEquationSet
      f p q hp hq v c]

noncomputable abbrev tripleCompleteIntersectionUniversalSingularFamily
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) : Scheme.{u} :=
  scheme (tripleCompleteIntersectionUniversalSingularHomogeneousIdeal
    p q hp hq v)

noncomputable abbrev tripleCompleteIntersectionUniversalSingularFamilyToCone
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) :
    tripleCompleteIntersectionUniversalSingularFamily p q hp hq v ⟶
      Spec (.of (MvPolynomial (Fin n) K)) :=
  toBase (tripleCompleteIntersectionUniversalSingularHomogeneousIdeal
    p q hp hq v)

/-- The universal simultaneous singularity family is proper over the affine
parameter cone. -/
instance tripleCompleteIntersectionUniversalSingularFamilyToCone_isProper
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) :
    IsProper (tripleCompleteIntersectionUniversalSingularFamilyToCone
      p q hp hq v) := by
  dsimp [tripleCompleteIntersectionUniversalSingularFamilyToCone]
  infer_instance

/-- The normalized coefficient specialization on one standard chart of the
common source projective space. -/
noncomputable def tripleCompleteIntersectionParameterChartCoefficientMap
    {n : ℕ} (i : Fin n) :
    MvPolynomial (Fin n) K →+*
      ChartRing
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i :=
  MvPolynomial.eval₂Hom
    (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)
    (chartCoordinate
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)

@[simp] theorem tripleCompleteIntersectionParameterChartCoefficientMap_X
    {n : ℕ} (i k : Fin n) :
    tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i (X k) =
      chartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i k := by
  simp [tripleCompleteIntersectionParameterChartCoefficientMap]

@[simp] theorem tripleCompleteIntersectionParameterChartCoefficientMap_C
    {n : ℕ} (i : Fin n) (a : K) :
    tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i (C a) =
      chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i a := by
  simp [tripleCompleteIntersectionParameterChartCoefficientMap]

/-- A field-valued point of a normalized parameter chart evaluates the
homogeneous source coordinates at its normalized chart coordinates. -/
theorem tripleCompleteIntersectionParameterChartCoefficientMap_comp
    {L : Type u} [Field L] {n : ℕ} (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    g.comp (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i) =
      MvPolynomial.eval₂Hom
        (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i))
        (fun k => g (chartCoordinate
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i k)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [tripleCompleteIntersectionParameterChartCoefficientMap]
  · intro k
    simp [tripleCompleteIntersectionParameterChartCoefficientMap]

/-- A normalized parameter-chart point specializes an independent cubic
frame to a nonzero cubic.  The normalized coordinate is one, so its
coefficient vector cannot vanish. -/
theorem tripleCompleteIntersectionUniversalCubic_parameterChart_map_ne_zero
    {L : Type u} [Field L] {n : ℕ}
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (hv : LinearIndependent K v)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    ((tripleCompleteIntersectionUniversalCubic v).map
      (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g ≠ 0 := by
  let m := Fintype.card (Monomials (Fin 4) 3)
  let e : Fin m ≃ Monomials (Fin 4) 3 := (Fintype.equivFin _).symm
  let c : Fin n → L := fun k => g (chartCoordinate
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i k)
  have hc : c ≠ 0 := by
    intro hzero
    have hi := congrFun hzero i
    change g (chartCoordinate
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i i) = 0 at hi
    rw [chartCoordinate_self, map_one] at hi
    exact one_ne_zero hi
  rw [MvPolynomial.map_map,
    tripleCompleteIntersectionParameterChartCoefficientMap_comp]
  exact tripleCompleteIntersectionUniversalCubic_map_ne_zero
    (g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i))
    e v hv c hc

/-- On every field-valued normalized source chart, the local universal
Jacobian equation specializes to the actual chart-Jacobian polynomial of the
local universal cubic.  No nonzeroness condition is imposed on the Jacobian
component. -/
theorem tripleCompleteIntersectionUniversalChartJacobian_parameterChart_map
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (i : Fin n) (j : Fin 4)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    ((tripleCompleteIntersectionUniversalChartJacobian p q j v).map
        (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g =
      tripleCompleteIntersectionChartJacobianPolynomial
        (p.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (q.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (((tripleCompleteIntersectionUniversalCubic v).map
          (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g) j := by
  rw [MvPolynomial.map_map,
    tripleCompleteIntersectionParameterChartCoefficientMap_comp]
  rw [tripleCompleteIntersectionUniversalChartJacobian_map
    (g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i))
    p q hp hq j v
    (fun k => g (chartCoordinate
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i k))]
  rw [MvPolynomial.map_map,
    tripleCompleteIntersectionParameterChartCoefficientMap_comp]

/-- The seven universal singularity equations restricted to one normalized
affine chart of their common projective parameter space. -/
noncomputable def tripleCompleteIntersectionUniversalSingularChartEquationSet
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) (i : Fin n) :
    Set (MvPolynomial (Fin 4)
      (ChartRing
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)) :=
  (MvPolynomial.map
    (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)) ''
      tripleCompleteIntersectionUniversalSingularEquationSet p q v

theorem tripleCompleteIntersectionUniversalSingularChartEquationSet_homogeneous
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) (i : Fin n) :
    ∀ r ∈ tripleCompleteIntersectionUniversalSingularChartEquationSet p q v i,
      ∃ d, r.IsHomogeneous d := by
  rintro r ⟨s, hs, rfl⟩
  obtain ⟨d, hd⟩ :=
    tripleCompleteIntersectionUniversalSingularEquationSet_homogeneous
      p q hp hq v s hs
  exact ⟨d, hd.map _⟩

/-- The simultaneous singularity ideal on a normalized source-parameter
chart. -/
noncomputable def tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) (i : Fin n) :
    HomogeneousIdeal
      (homogeneousSubmodule (Fin 4)
        (ChartRing
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)) :=
  ⟨Ideal.span
      (tripleCompleteIntersectionUniversalSingularChartEquationSet p q v i),
    Ideal.homogeneous_span _ _
      (tripleCompleteIntersectionUniversalSingularChartEquationSet_homogeneous
        p q hp hq v i)⟩

/-- Restricting the affine-cone universal ideal to a normalized parameter
chart is ordinary coefficient change along the chart specialization. -/
theorem tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal_toIdeal
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) (i : Fin n) :
    (tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal
        p q hp hq v i).toIdeal =
      (tripleCompleteIntersectionUniversalSingularHomogeneousIdeal
        p q hp hq v).toIdeal.map
        (MvPolynomial.map
          (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)) := by
  rw [tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal,
    tripleCompleteIntersectionUniversalSingularHomogeneousIdeal, Ideal.map_span]
  rfl

/-- Every field-valued fiber of a normalized parameter chart is cut out by
the specialized cubic and its four actual Jacobian components. -/
theorem tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal_map
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    (tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal
        p q hp hq v i).toIdeal.map (MvPolynomial.map g) =
      tripleCompleteIntersectionSingularIdeal
        (p.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (q.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (((tripleCompleteIntersectionUniversalCubic v).map
          (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g) := by
  rw [tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal_toIdeal,
    Ideal.map_map]
  have hcoeff := tripleCompleteIntersectionParameterChartCoefficientMap_comp
    (K := K) i g
  have hpoly :
      (MvPolynomial.map (σ := Fin 4) g).comp
          (MvPolynomial.map (σ := Fin 4)
            (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)) =
        MvPolynomial.map (σ := Fin 4)
          (MvPolynomial.eval₂Hom
            (g.comp (chartBaseMap
              (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i))
            (fun k => g (chartCoordinate
              (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i k))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C]
      exact congrArg C (DFunLike.congr_fun hcoeff a)
    · intro k
      simp
  rw [hpoly]
  rw [tripleCompleteIntersectionUniversalSingularHomogeneousIdeal_map
    (g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i))
    p q hp hq v
    (fun k => g (chartCoordinate
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i k))]
  rw [MvPolynomial.map_map, hcoeff]

/-- The homogeneous ideal of one field-valued fiber of a normalized source
parameter chart. -/
noncomputable def tripleCompleteIntersectionUniversalSingularChartFiberIdeal
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) L) :=
  tripleCompleteIntersectionSingularHomogeneousIdeal
    (p.map (g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
    (q.map (g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
    (((tripleCompleteIntersectionUniversalCubic v).map
      (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g)
    (hp.map _)
    (hq.map _)
    ((tripleCompleteIntersectionUniversalCubic_isHomogeneous v).map _ |>.map g)

theorem tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal_map_eq_fiber
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    (tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal
        p q hp hq v i).toIdeal.map (MvPolynomial.map g) =
      (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
        p q hp hq v i g).toIdeal := by
  rw [tripleCompleteIntersectionUniversalSingularChartFiberIdeal,
    tripleCompleteIntersectionSingularHomogeneousIdeal_toIdeal]
  exact tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal_map
    p q hp hq v i g

/-- The projective coefficient-change morphism from a field-valued fiber to
the normalized universal simultaneous-zero family. -/
noncomputable def tripleCompleteIntersectionUniversalSingularChartFiberToFamily
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    scheme (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
      p q hp hq v i g) ⟶
      scheme (tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal
        p q hp hq v i) :=
  projectiveCoefficientMap g
    (tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal
      p q hp hq v i)
    (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
      p q hp hq v i g)
    (tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal_map_eq_fiber
      p q hp hq v i g)

theorem tripleCompleteIntersectionUniversalSingularChartFiberToFamily_toBase
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    (tripleCompleteIntersectionUniversalSingularChartFiberToFamily
        p q hp hq v i g) ≫
      toBase (tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal
        p q hp hq v i) =
      toBase (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
        p q hp hq v i g) ≫ Spec.map (CommRingCat.ofHom g) := by
  exact projectiveCoefficientMap_toBase g
    (tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal
      p q hp hq v i)
    (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
      p q hp hq v i g)
    (tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal_map_eq_fiber
      p q hp hq v i g)

noncomputable abbrev tripleCompleteIntersectionUniversalSingularChartFamily
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) (i : Fin n) : Scheme.{u} :=
  scheme (tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal
    p q hp hq v i)

noncomputable abbrev tripleCompleteIntersectionUniversalSingularChartFamilyToBase
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) (i : Fin n) :
    tripleCompleteIntersectionUniversalSingularChartFamily p q hp hq v i ⟶
      Spec (.of
        (ChartRing
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)) :=
  toBase (tripleCompleteIntersectionUniversalSingularChartHomogeneousIdeal
    p q hp hq v i)

instance tripleCompleteIntersectionUniversalSingularChartFamilyToBase_isProper
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) (i : Fin n) :
    IsProper (tripleCompleteIntersectionUniversalSingularChartFamilyToBase
      p q hp hq v i) := by
  dsimp [tripleCompleteIntersectionUniversalSingularChartFamilyToBase]
  infer_instance

/-- Parameters on one normalized source chart for which the cubic and all
four Jacobian components have a common projective zero. -/
noncomputable def tripleCompleteIntersectionUniversalSingularChartBadLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) (i : Fin n) :
    Set (Spec (.of
      (ChartRing
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i))) :=
  let f := tripleCompleteIntersectionUniversalSingularChartFamilyToBase
    p q hp hq v i
  Set.range f

/-- Every point of a specialized simultaneous-singularity fiber maps to the
corresponding parameter point in the chartwise bad locus. -/
theorem
    tripleCompleteIntersectionUniversalSingularChartFiber_point_mem_badLocus
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L)
    (z : scheme (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
      p q hp hq v i g)) :
    Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L) ∈
      tripleCompleteIntersectionUniversalSingularChartBadLocus
        p q hp hq v i := by
  change Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L) ∈
    Set.range (tripleCompleteIntersectionUniversalSingularChartFamilyToBase
      p q hp hq v i)
  refine ⟨tripleCompleteIntersectionUniversalSingularChartFiberToFamily
    p q hp hq v i g z, ?_⟩
  rw [← Scheme.Hom.comp_apply,
    tripleCompleteIntersectionUniversalSingularChartFiberToFamily_toBase,
    Scheme.Hom.comp_apply]
  congr 1
  exact Subsingleton.elim _ _

/-- A chart parameter outside the bad image has an empty specialized
projective simultaneous-singularity fiber. -/
theorem
    tripleCompleteIntersectionUniversalSingularChartFiber_isEmpty_of_not_mem_badLocus
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L)
    (hgood : Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L) ∉
      tripleCompleteIntersectionUniversalSingularChartBadLocus
        p q hp hq v i) :
    IsEmpty (scheme
      (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
        p q hp hq v i g)) :=
  ⟨fun z => hgood
    (tripleCompleteIntersectionUniversalSingularChartFiber_point_mem_badLocus
      p q hp hq v i g z)⟩

/-- Properness of the simultaneous zero family makes its bad-parameter image
closed on every normalized source chart. -/
theorem isClosed_tripleCompleteIntersectionUniversalSingularChartBadLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) (i : Fin n) :
    IsClosed (tripleCompleteIntersectionUniversalSingularChartBadLocus
      p q hp hq v i) := by
  let f := tripleCompleteIntersectionUniversalSingularChartFamilyToBase
    p q hp hq v i
  change IsClosed (Set.range f)
  letI : IsProper f :=
    tripleCompleteIntersectionUniversalSingularChartFamilyToBase_isProper
      p q hp hq v i
  exact f.isClosedMap.isClosed_range

/-- The global good set is the union, over all normalized source charts, of
the open complements of the proper simultaneous-zero images. -/
noncomputable def tripleCompleteIntersectionUniversalNonsingularParameterLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) :
    Set (projectiveLinearSystemParameters (K := K) (τ := Fin n)) :=
  ⋃ i : Fin n,
    chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i ''
      (tripleCompleteIntersectionUniversalSingularChartBadLocus
        p q hp hq v i)ᶜ

theorem isOpen_tripleCompleteIntersectionUniversalNonsingularParameterLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) :
    IsOpen (tripleCompleteIntersectionUniversalNonsingularParameterLocus
      p q hp hq v) := by
  apply isOpen_iUnion
  intro i
  exact (chartι
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i).isOpenMap _
      (isClosed_tripleCompleteIntersectionUniversalSingularChartBadLocus
        p q hp hq v i).isOpen_compl

/-- The global simultaneous singular-member locus in the common source
projective parameter space.  It is defined using the local families, so all
four Jacobian components are allowed to vanish identically. -/
noncomputable def tripleCompleteIntersectionUniversalSingularParameterLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) :
    Set (projectiveLinearSystemParameters (K := K) (τ := Fin n)) :=
  (tripleCompleteIntersectionUniversalNonsingularParameterLocus
    p q hp hq v)ᶜ

/-- The simultaneous singular-member locus is globally closed on the source
projective parameter space. -/
theorem isClosed_tripleCompleteIntersectionUniversalSingularParameterLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3) :
    IsClosed (tripleCompleteIntersectionUniversalSingularParameterLocus
      p q hp hq v) := by
  exact (isOpen_tripleCompleteIntersectionUniversalNonsingularParameterLocus
    p q hp hq v).isClosed_compl

/-- If the universal simultaneous singular-member locus is proper, the
generic function-field parameter avoids it. -/
theorem
    genericFunctionField_closedPoint_avoids_tripleCompleteIntersectionUniversalSingularParameterLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    [IsIntegral (projectiveLinearSystemParameters (K := K) (τ := Fin n))]
    (hproper : tripleCompleteIntersectionUniversalSingularParameterLocus
      p q hp hq v ≠ Set.univ) :
    (projectiveLinearSystemParameters (K := K) (τ := Fin n)).fromSpecStalk
        (genericPoint
          (projectiveLinearSystemParameters (K := K) (τ := Fin n)))
        (IsLocalRing.closedPoint
          (projectiveLinearSystemParameters
            (K := K) (τ := Fin n)).functionField) ∉
      tripleCompleteIntersectionUniversalSingularParameterLocus
        p q hp hq v := by
  exact genericFunctionField_closedPoint_avoids_proper_closed
    (projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (isClosed_tripleCompleteIntersectionUniversalSingularParameterLocus
      p q hp hq v) hproper

/-- One explicit nonsingular parameter proves properness and hence generic
avoidance of the universal singular-member locus. -/
theorem
    genericFunctionField_closedPoint_avoids_tripleCompleteIntersectionUniversalSingularParameterLocus_of_exists
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    [IsIntegral (projectiveLinearSystemParameters (K := K) (τ := Fin n))]
    (hgood : ∃ t : projectiveLinearSystemParameters (K := K) (τ := Fin n),
      t ∉ tripleCompleteIntersectionUniversalSingularParameterLocus
        p q hp hq v) :
    (projectiveLinearSystemParameters (K := K) (τ := Fin n)).fromSpecStalk
        (genericPoint
          (projectiveLinearSystemParameters (K := K) (τ := Fin n)))
        (IsLocalRing.closedPoint
          (projectiveLinearSystemParameters
            (K := K) (τ := Fin n)).functionField) ∉
      tripleCompleteIntersectionUniversalSingularParameterLocus
        p q hp hq v := by
  apply
    genericFunctionField_closedPoint_avoids_tripleCompleteIntersectionUniversalSingularParameterLocus
      p q hp hq v
  rintro hbad
  obtain ⟨t, ht⟩ := hgood
  exact ht (by rw [hbad]; exact Set.mem_univ t)

/-- Avoiding the global closed locus supplies a normalized parameter chart on
which the simultaneous projective zero family has empty fiber at that
parameter. -/
theorem exists_parameterChart_not_mem_badLocus_of_not_mem_singularParameterLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (x : projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (hx : x ∉ tripleCompleteIntersectionUniversalSingularParameterLocus
      p q hp hq v) :
    ∃ (i : Fin n)
      (y : Spec (.of
        (ChartRing
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i))),
      chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i y = x ∧
      y ∉ tripleCompleteIntersectionUniversalSingularChartBadLocus
        p q hp hq v i := by
  have hxgood : x ∈
      tripleCompleteIntersectionUniversalNonsingularParameterLocus
        p q hp hq v := by
    simpa [tripleCompleteIntersectionUniversalSingularParameterLocus] using hx
  simp only [tripleCompleteIntersectionUniversalNonsingularParameterLocus,
    Set.mem_iUnion, Set.mem_image, Set.mem_compl_iff] at hxgood
  obtain ⟨i, y, hy, rfl⟩ := hxgood
  exact ⟨i, y, rfl, hy⟩

/-- A field-valued parameter outside the global singular locus factors
through a normalized source chart whose specialized singular fiber is empty.
The returned chart homomorphism retains the original coefficient-field map. -/
theorem
    exists_parameterChartHom_not_mem_badLocus_of_fieldPoint_not_mem_singularParameterLocus
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (t : Spec (.of L) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (ht : t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
        Spec.map (CommRingCat.ofHom f))
    (hgood : t (IsLocalRing.closedPoint L) ∉
      tripleCompleteIntersectionUniversalSingularParameterLocus
        p q hp hq v) :
    ∃ (i : Fin n)
      (g : ChartRing
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L),
      g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i) = f ∧
      Spec.map (CommRingCat.ofHom g) ≫
        chartι (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin n) K)) i = t ∧
      Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L) ∉
        tripleCompleteIntersectionUniversalSingularChartBadLocus
          p q hp hq v i := by
  obtain ⟨i, y, hy, hygood⟩ :=
    exists_parameterChart_not_mem_badLocus_of_not_mem_singularParameterLocus
      p q hp hq v (t (IsLocalRing.closedPoint L)) hgood
  obtain ⟨g, hgbase, hgt⟩ := exists_chart_hom_eq_of_point_of_mem_range
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
    f t ht i ⟨y, hy⟩
  refine ⟨i, g, hgbase, hgt, ?_⟩
  intro hgbad
  apply hygood
  have hinj : Function.Injective
      (chartι (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin n) K)) i) :=
    (inferInstance : IsOpenImmersion
      (chartι (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin n) K)) i)).1.injective
  have heq : y =
      Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L) := by
    apply hinj
    rw [hy, ← hgt]
    rfl
  rw [heq]
  exact hgbad

/-- A field-valued parameter outside the global singular locus therefore has,
on a normalized parameter chart, no projective point satisfying the two fixed
cubics, the moving cubic, and all four Jacobian-minor equations. -/
theorem
    exists_parameterChartHom_empty_singularFiber_of_fieldPoint_not_mem_singularParameterLocus
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (t : Spec (.of L) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (ht : t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
        Spec.map (CommRingCat.ofHom f))
    (hgood : t (IsLocalRing.closedPoint L) ∉
      tripleCompleteIntersectionUniversalSingularParameterLocus
        p q hp hq v) :
    ∃ (i : Fin n)
      (g : ChartRing
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L),
      g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i) = f ∧
      Spec.map (CommRingCat.ofHom g) ≫
        chartι (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin n) K)) i = t ∧
      IsEmpty (scheme
        (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
          p q hp hq v i g)) := by
  obtain ⟨i, g, hgbase, hgt, hgoodChart⟩ :=
    exists_parameterChartHom_not_mem_badLocus_of_fieldPoint_not_mem_singularParameterLocus
      f p q hp hq v t ht hgood
  exact ⟨i, g, hgbase, hgt,
    tripleCompleteIntersectionUniversalSingularChartFiber_isEmpty_of_not_mem_badLocus
      p q hp hq v i g hgoodChart⟩

end

end PfaffianDescent
