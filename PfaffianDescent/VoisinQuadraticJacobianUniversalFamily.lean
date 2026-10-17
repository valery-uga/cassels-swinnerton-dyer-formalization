import PfaffianDescent.VoisinCubicTwoQuadricSingularScheme

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

section

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The Jacobian of a specialized finite quadratic combination is the same
finite combination of the individual Jacobian polynomials. -/
theorem cubicTwoQuadricChartJacobianPolynomial_sum_C_mul_map
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (j : Fin 4) (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
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

/-- The quadric with projective source coordinates as its coefficients. -/
noncomputable def cubicTwoQuadricUniversalQuadric
    {n : ℕ}
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    MvPolynomial (Fin 4) (MvPolynomial (Fin n) K) :=
  ∑ i, C (X i) * (v i).1.map C

/-- One universal chart-Jacobian component over the same source coordinates
as the moving quadric.  It is defined even when the component specializes to
the zero sextic. -/
noncomputable def cubicTwoQuadricUniversalChartJacobian
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    MvPolynomial (Fin 4) (MvPolynomial (Fin n) K) :=
  ∑ i, C (X i) *
    (tripleCompleteIntersectionChartJacobianPolynomial p q (v i).1 j).map C

theorem cubicTwoQuadricUniversalQuadric_isHomogeneous
    {n : ℕ}
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    (cubicTwoQuadricUniversalQuadric v).IsHomogeneous 2 := by
  classical
  apply IsHomogeneous.sum
  intro i hi
  exact ((v i).2.map C).C_mul _

theorem cubicTwoQuadricUniversalChartJacobian_isHomogeneous
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (j : Fin 4) (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    (cubicTwoQuadricUniversalChartJacobian p q j v).IsHomogeneous 4 := by
  classical
  apply IsHomogeneous.sum
  intro i hi
  exact ((cubicTwoQuadricChartJacobianPolynomial_isHomogeneous
    p q (v i).1 hp hq (v i).2 j).map C).C_mul _

theorem cubicTwoQuadricUniversalQuadric_coeff
    {n : ℕ}
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (m : Fin 4 →₀ ℕ) :
    (cubicTwoQuadricUniversalQuadric v).coeff m =
      ∑ i, X i * C ((v i).1.coeff m) := by
  classical
  simp [cubicTwoQuadricUniversalQuadric,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map]

/-- Every ambient coefficient of the universal quadric is linear homogeneous
in the common source-projective coordinates. -/
theorem cubicTwoQuadricUniversalQuadric_coeff_isHomogeneous
    {n : ℕ}
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (m : Fin 4 →₀ ℕ) :
    ((cubicTwoQuadricUniversalQuadric v).coeff m).IsHomogeneous 1 := by
  rw [cubicTwoQuadricUniversalQuadric_coeff]
  apply IsHomogeneous.sum
  intro i hi
  simpa only [Nat.add_zero] using
    (MvPolynomial.isHomogeneous_X (R := K) i).mul
      (MvPolynomial.isHomogeneous_C (Fin n) ((v i).1.coeff m))

theorem cubicTwoQuadricUniversalChartJacobian_coeff
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (m : Fin 4 →₀ ℕ) :
    (cubicTwoQuadricUniversalChartJacobian p q j v).coeff m =
      ∑ i, X i * C
        ((tripleCompleteIntersectionChartJacobianPolynomial p q (v i).1 j).coeff m) := by
  classical
  simp [cubicTwoQuadricUniversalChartJacobian,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map]

/-- Every ambient coefficient of every universal Jacobian component is
linear homogeneous in the common source-projective coordinates, including
when all of those coefficients specialize to zero. -/
theorem cubicTwoQuadricUniversalChartJacobian_coeff_isHomogeneous
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K) (j : Fin 4)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (m : Fin 4 →₀ ℕ) :
    ((cubicTwoQuadricUniversalChartJacobian p q j v).coeff m).IsHomogeneous 1 := by
  rw [cubicTwoQuadricUniversalChartJacobian_coeff]
  apply IsHomogeneous.sum
  intro i hi
  simpa only [Nat.add_zero] using
    (MvPolynomial.isHomogeneous_X (R := K) i).mul
      (MvPolynomial.isHomogeneous_C (Fin n)
        ((tripleCompleteIntersectionChartJacobianPolynomial p q (v i).1 j).coeff m))

theorem cubicTwoQuadricUniversalQuadric_map
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L) (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (c : Fin n → L) :
    (cubicTwoQuadricUniversalQuadric v).map
        (MvPolynomial.eval₂Hom f c) =
      ∑ i, C (c i) * (v i).1.map f := by
  classical
  simp only [cubicTwoQuadricUniversalQuadric, map_sum, map_mul,
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
theorem cubicTwoQuadricUniversalQuadric_map_ne_zero
    {L : Type u} [Field L] {m n : ℕ}
    (f : K →+* L) (e : Fin m ≃ Monomials (Fin 4) 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (hv : LinearIndependent K v) (c : Fin n → L) (hc : c ≠ 0) :
    (cubicTwoQuadricUniversalQuadric v).map
        (MvPolynomial.eval₂Hom f c) ≠ 0 := by
  rw [cubicTwoQuadricUniversalQuadric_map f v c]
  exact homogeneousFrameCombination_map_ne_zero_of_ne_zero
    2 f e v hv c hc

theorem cubicTwoQuadricUniversalChartJacobian_map
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (j : Fin 4) (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (c : Fin n → L) :
    (cubicTwoQuadricUniversalChartJacobian p q j v).map
        (MvPolynomial.eval₂Hom f c) =
      tripleCompleteIntersectionChartJacobianPolynomial
        (p.map f) (q.map f)
        ((cubicTwoQuadricUniversalQuadric v).map
          (MvPolynomial.eval₂Hom f c)) j := by
  rw [cubicTwoQuadricUniversalQuadric_map f v c,
    cubicTwoQuadricUniversalChartJacobian]
  simp only [map_sum, map_mul, map_C, map_map]
  have hfc : (MvPolynomial.eval₂Hom f c).comp C = f := by
    ext a
    simp
  simp only [hfc]
  rw [cubicTwoQuadricChartJacobianPolynomial_sum_C_mul_map
    f p q hp hq j v c]
  apply Finset.sum_congr rfl
  intro i hi
  rw [MvPolynomial.eval₂Hom_X']

/-- The two fixed cubics, the moving quadric, and all four Jacobian components,
as equations over the affine cone of their common projective source
coordinates. -/
noncomputable def cubicTwoQuadricUniversalSingularEquationSet
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    Set (MvPolynomial (Fin 4) (MvPolynomial (Fin n) K)) :=
  {p.map C, q.map C, cubicTwoQuadricUniversalQuadric v} ∪
    Set.range (fun j : Fin 4 =>
      cubicTwoQuadricUniversalChartJacobian p q j v)

theorem cubicTwoQuadricUniversalSingularEquationSet_homogeneous
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    ∀ r ∈ cubicTwoQuadricUniversalSingularEquationSet p q v,
      ∃ d, r.IsHomogeneous d := by
  intro r hr
  rcases hr with hr | hr
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨3, hp.map C⟩
    · exact ⟨2, hq.map C⟩
    · exact ⟨2, cubicTwoQuadricUniversalQuadric_isHomogeneous v⟩
  · obtain ⟨j, rfl⟩ := hr
    exact ⟨4,
      cubicTwoQuadricUniversalChartJacobian_isHomogeneous
        p q hp hq j v⟩

/-- Specializing the common source coordinates carries the universal five
equations to the cubic and its four actual chart-Jacobian components. -/
theorem image_cubicTwoQuadricUniversalSingularEquationSet
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (c : Fin n → L) :
    (MvPolynomial.map (MvPolynomial.eval₂Hom f c)) ''
        cubicTwoQuadricUniversalSingularEquationSet p q v =
      cubicTwoQuadricSingularEquationSet (p.map f) (q.map f)
        ((cubicTwoQuadricUniversalQuadric v).map
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
      exact (cubicTwoQuadricUniversalChartJacobian_map
        f p q hp hq j v c).symm
  · intro hz
    rcases hz with hz | hz
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · refine ⟨p.map C, Or.inl (Or.inl rfl), ?_⟩
        rw [MvPolynomial.map_map, hfc]
      · refine ⟨q.map C, Or.inl (Or.inr (Or.inl rfl)), ?_⟩
        rw [MvPolynomial.map_map, hfc]
      · exact ⟨cubicTwoQuadricUniversalQuadric v,
          Or.inl (Or.inr (Or.inr rfl)), rfl⟩
    · obtain ⟨j, rfl⟩ := hz
      refine ⟨cubicTwoQuadricUniversalChartJacobian p q j v,
        Or.inr ⟨j, rfl⟩, ?_⟩
      exact cubicTwoQuadricUniversalChartJacobian_map
        f p q hp hq j v c

/-- The relative projective zero scheme of the two fixed cubics, the universal
cubic, and all four Jacobian components over the affine parameter cone.
Unlike four separate maps to sextic projective space, this remains defined
when any component is identically zero at a parameter. -/
noncomputable def cubicTwoQuadricUniversalSingularHomogeneousIdeal
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (MvPolynomial (Fin n) K)) :=
  ⟨Ideal.span (cubicTwoQuadricUniversalSingularEquationSet p q v),
    Ideal.homogeneous_span _ _
      (cubicTwoQuadricUniversalSingularEquationSet_homogeneous
        p q hp hq v)⟩

/-- The fiber ideal of the universal simultaneous singularity family is the
ideal generated by the two fixed cubics, the specialized quadric, and its four
actual Jacobian components. -/
theorem cubicTwoQuadricUniversalSingularHomogeneousIdeal_map
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (c : Fin n → L) :
    (cubicTwoQuadricUniversalSingularHomogeneousIdeal
        p q hp hq v).toIdeal.map
        (MvPolynomial.map (MvPolynomial.eval₂Hom f c)) =
      cubicTwoQuadricSingularIdeal (p.map f) (q.map f)
        ((cubicTwoQuadricUniversalQuadric v).map
          (MvPolynomial.eval₂Hom f c)) := by
  rw [cubicTwoQuadricUniversalSingularHomogeneousIdeal,
    cubicTwoQuadricSingularIdeal, Ideal.map_span,
    image_cubicTwoQuadricUniversalSingularEquationSet
      f p q hp hq v c]

noncomputable abbrev cubicTwoQuadricUniversalSingularFamily
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) : Scheme.{u} :=
  scheme (cubicTwoQuadricUniversalSingularHomogeneousIdeal
    p q hp hq v)

noncomputable abbrev cubicTwoQuadricUniversalSingularFamilyToCone
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    cubicTwoQuadricUniversalSingularFamily p q hp hq v ⟶
      Spec (.of (MvPolynomial (Fin n) K)) :=
  toBase (cubicTwoQuadricUniversalSingularHomogeneousIdeal
    p q hp hq v)

/-- The universal simultaneous singularity family is proper over the affine
parameter cone. -/
instance cubicTwoQuadricUniversalSingularFamilyToCone_isProper
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    IsProper (cubicTwoQuadricUniversalSingularFamilyToCone
      p q hp hq v) := by
  dsimp [cubicTwoQuadricUniversalSingularFamilyToCone]
  infer_instance

/-- The normalized coefficient specialization on one standard chart of the
common source projective space. -/
noncomputable def cubicTwoQuadricParameterChartCoefficientMap
    {n : ℕ} (i : Fin n) :
    MvPolynomial (Fin n) K →+*
      ChartRing
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i :=
  MvPolynomial.eval₂Hom
    (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)
    (chartCoordinate
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)

@[simp] theorem cubicTwoQuadricParameterChartCoefficientMap_X
    {n : ℕ} (i k : Fin n) :
    cubicTwoQuadricParameterChartCoefficientMap (K := K) i (X k) =
      chartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i k := by
  simp [cubicTwoQuadricParameterChartCoefficientMap]

@[simp] theorem cubicTwoQuadricParameterChartCoefficientMap_C
    {n : ℕ} (i : Fin n) (a : K) :
    cubicTwoQuadricParameterChartCoefficientMap (K := K) i (C a) =
      chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i a := by
  simp [cubicTwoQuadricParameterChartCoefficientMap]

/-- A field-valued point of a normalized parameter chart evaluates the
homogeneous source coordinates at its normalized chart coordinates. -/
theorem cubicTwoQuadricParameterChartCoefficientMap_comp
    {L : Type u} [Field L] {n : ℕ} (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    g.comp (cubicTwoQuadricParameterChartCoefficientMap (K := K) i) =
      MvPolynomial.eval₂Hom
        (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i))
        (fun k => g (chartCoordinate
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i k)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [cubicTwoQuadricParameterChartCoefficientMap]
  · intro k
    simp [cubicTwoQuadricParameterChartCoefficientMap]

/-- A normalized parameter-chart point specializes an independent cubic
frame to a nonzero cubic.  The normalized coordinate is one, so its
coefficient vector cannot vanish. -/
theorem cubicTwoQuadricUniversalQuadric_parameterChart_map_ne_zero
    {L : Type u} [Field L] {n : ℕ}
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (hv : LinearIndependent K v)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    ((cubicTwoQuadricUniversalQuadric v).map
      (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g ≠ 0 := by
  let m := Fintype.card (Monomials (Fin 4) 2)
  let e : Fin m ≃ Monomials (Fin 4) 2 := (Fintype.equivFin _).symm
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
    cubicTwoQuadricParameterChartCoefficientMap_comp]
  exact cubicTwoQuadricUniversalQuadric_map_ne_zero
    (g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i))
    e v hv c hc

/-- On every field-valued normalized source chart, the local universal
Jacobian equation specializes to the actual chart-Jacobian polynomial of the
local universal quadric.  No nonzeroness condition is imposed on the Jacobian
component. -/
theorem cubicTwoQuadricUniversalChartJacobian_parameterChart_map
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (i : Fin n) (j : Fin 4)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    ((cubicTwoQuadricUniversalChartJacobian p q j v).map
        (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g =
      tripleCompleteIntersectionChartJacobianPolynomial
        (p.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (q.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (((cubicTwoQuadricUniversalQuadric v).map
          (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g) j := by
  rw [MvPolynomial.map_map,
    cubicTwoQuadricParameterChartCoefficientMap_comp]
  rw [cubicTwoQuadricUniversalChartJacobian_map
    (g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i))
    p q hp hq j v
    (fun k => g (chartCoordinate
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i k))]
  rw [MvPolynomial.map_map,
    cubicTwoQuadricParameterChartCoefficientMap_comp]

/-- The seven universal singularity equations restricted to one normalized
affine chart of their common projective parameter space. -/
noncomputable def cubicTwoQuadricUniversalSingularChartEquationSet
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) (i : Fin n) :
    Set (MvPolynomial (Fin 4)
      (ChartRing
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)) :=
  (MvPolynomial.map
    (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)) ''
      cubicTwoQuadricUniversalSingularEquationSet p q v

theorem cubicTwoQuadricUniversalSingularChartEquationSet_homogeneous
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) (i : Fin n) :
    ∀ r ∈ cubicTwoQuadricUniversalSingularChartEquationSet p q v i,
      ∃ d, r.IsHomogeneous d := by
  rintro r ⟨s, hs, rfl⟩
  obtain ⟨d, hd⟩ :=
    cubicTwoQuadricUniversalSingularEquationSet_homogeneous
      p q hp hq v s hs
  exact ⟨d, hd.map _⟩

/-- The simultaneous singularity ideal on a normalized source-parameter
chart. -/
noncomputable def cubicTwoQuadricUniversalSingularChartHomogeneousIdeal
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) (i : Fin n) :
    HomogeneousIdeal
      (homogeneousSubmodule (Fin 4)
        (ChartRing
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)) :=
  ⟨Ideal.span
      (cubicTwoQuadricUniversalSingularChartEquationSet p q v i),
    Ideal.homogeneous_span _ _
      (cubicTwoQuadricUniversalSingularChartEquationSet_homogeneous
        p q hp hq v i)⟩

/-- Restricting the affine-cone universal ideal to a normalized parameter
chart is ordinary coefficient change along the chart specialization. -/
theorem cubicTwoQuadricUniversalSingularChartHomogeneousIdeal_toIdeal
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) (i : Fin n) :
    (cubicTwoQuadricUniversalSingularChartHomogeneousIdeal
        p q hp hq v i).toIdeal =
      (cubicTwoQuadricUniversalSingularHomogeneousIdeal
        p q hp hq v).toIdeal.map
        (MvPolynomial.map
          (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)) := by
  rw [cubicTwoQuadricUniversalSingularChartHomogeneousIdeal,
    cubicTwoQuadricUniversalSingularHomogeneousIdeal, Ideal.map_span]
  rfl

/-- Every field-valued fiber of a normalized parameter chart is cut out by
the specialized quadric and its four actual Jacobian components. -/
theorem cubicTwoQuadricUniversalSingularChartHomogeneousIdeal_map
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    (cubicTwoQuadricUniversalSingularChartHomogeneousIdeal
        p q hp hq v i).toIdeal.map (MvPolynomial.map g) =
      cubicTwoQuadricSingularIdeal
        (p.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (q.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (((cubicTwoQuadricUniversalQuadric v).map
          (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g) := by
  rw [cubicTwoQuadricUniversalSingularChartHomogeneousIdeal_toIdeal,
    Ideal.map_map]
  have hcoeff := cubicTwoQuadricParameterChartCoefficientMap_comp
    (K := K) i g
  have hpoly :
      (MvPolynomial.map (σ := Fin 4) g).comp
          (MvPolynomial.map (σ := Fin 4)
            (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)) =
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
  rw [cubicTwoQuadricUniversalSingularHomogeneousIdeal_map
    (g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i))
    p q hp hq v
    (fun k => g (chartCoordinate
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i k))]
  rw [MvPolynomial.map_map, hcoeff]

/-- The homogeneous ideal of one field-valued fiber of a normalized source
parameter chart. -/
noncomputable def cubicTwoQuadricUniversalSingularChartFiberIdeal
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 4) L) :=
  cubicTwoQuadricSingularHomogeneousIdeal
    (p.map (g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
    (q.map (g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
    (((cubicTwoQuadricUniversalQuadric v).map
      (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g)
    (hp.map _)
    (hq.map _)
    ((cubicTwoQuadricUniversalQuadric_isHomogeneous v).map _ |>.map g)

theorem cubicTwoQuadricUniversalSingularChartHomogeneousIdeal_map_eq_fiber
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    (cubicTwoQuadricUniversalSingularChartHomogeneousIdeal
        p q hp hq v i).toIdeal.map (MvPolynomial.map g) =
      (cubicTwoQuadricUniversalSingularChartFiberIdeal
        p q hp hq v i g).toIdeal := by
  rw [cubicTwoQuadricUniversalSingularChartFiberIdeal,
    cubicTwoQuadricSingularHomogeneousIdeal_toIdeal]
  exact cubicTwoQuadricUniversalSingularChartHomogeneousIdeal_map
    p q hp hq v i g

/-- The projective coefficient-change morphism from a field-valued fiber to
the normalized universal simultaneous-zero family. -/
noncomputable def cubicTwoQuadricUniversalSingularChartFiberToFamily
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    scheme (cubicTwoQuadricUniversalSingularChartFiberIdeal
      p q hp hq v i g) ⟶
      scheme (cubicTwoQuadricUniversalSingularChartHomogeneousIdeal
        p q hp hq v i) :=
  projectiveCoefficientMap g
    (cubicTwoQuadricUniversalSingularChartHomogeneousIdeal
      p q hp hq v i)
    (cubicTwoQuadricUniversalSingularChartFiberIdeal
      p q hp hq v i g)
    (cubicTwoQuadricUniversalSingularChartHomogeneousIdeal_map_eq_fiber
      p q hp hq v i g)

theorem cubicTwoQuadricUniversalSingularChartFiberToFamily_toBase
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L) :
    (cubicTwoQuadricUniversalSingularChartFiberToFamily
        p q hp hq v i g) ≫
      toBase (cubicTwoQuadricUniversalSingularChartHomogeneousIdeal
        p q hp hq v i) =
      toBase (cubicTwoQuadricUniversalSingularChartFiberIdeal
        p q hp hq v i g) ≫ Spec.map (CommRingCat.ofHom g) := by
  exact projectiveCoefficientMap_toBase g
    (cubicTwoQuadricUniversalSingularChartHomogeneousIdeal
      p q hp hq v i)
    (cubicTwoQuadricUniversalSingularChartFiberIdeal
      p q hp hq v i g)
    (cubicTwoQuadricUniversalSingularChartHomogeneousIdeal_map_eq_fiber
      p q hp hq v i g)

noncomputable abbrev cubicTwoQuadricUniversalSingularChartFamily
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) (i : Fin n) : Scheme.{u} :=
  scheme (cubicTwoQuadricUniversalSingularChartHomogeneousIdeal
    p q hp hq v i)

noncomputable abbrev cubicTwoQuadricUniversalSingularChartFamilyToBase
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) (i : Fin n) :
    cubicTwoQuadricUniversalSingularChartFamily p q hp hq v i ⟶
      Spec (.of
        (ChartRing
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)) :=
  toBase (cubicTwoQuadricUniversalSingularChartHomogeneousIdeal
    p q hp hq v i)

instance cubicTwoQuadricUniversalSingularChartFamilyToBase_isProper
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) (i : Fin n) :
    IsProper (cubicTwoQuadricUniversalSingularChartFamilyToBase
      p q hp hq v i) := by
  dsimp [cubicTwoQuadricUniversalSingularChartFamilyToBase]
  infer_instance

/-- Parameters on one normalized source chart for which the cubic and all
four Jacobian components have a common projective zero. -/
noncomputable def cubicTwoQuadricUniversalSingularChartBadLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) (i : Fin n) :
    Set (Spec (.of
      (ChartRing
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i))) :=
  let f := cubicTwoQuadricUniversalSingularChartFamilyToBase
    p q hp hq v i
  Set.range f

/-- Every point of a specialized simultaneous-singularity fiber maps to the
corresponding parameter point in the chartwise bad locus. -/
theorem
    cubicTwoQuadricUniversalSingularChartFiber_point_mem_badLocus
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L)
    (z : scheme (cubicTwoQuadricUniversalSingularChartFiberIdeal
      p q hp hq v i g)) :
    Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L) ∈
      cubicTwoQuadricUniversalSingularChartBadLocus
        p q hp hq v i := by
  change Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L) ∈
    Set.range (cubicTwoQuadricUniversalSingularChartFamilyToBase
      p q hp hq v i)
  refine ⟨cubicTwoQuadricUniversalSingularChartFiberToFamily
    p q hp hq v i g z, ?_⟩
  rw [← Scheme.Hom.comp_apply,
    cubicTwoQuadricUniversalSingularChartFiberToFamily_toBase,
    Scheme.Hom.comp_apply]
  congr 1
  exact Subsingleton.elim _ _

/-- A chart parameter outside the bad image has an empty specialized
projective simultaneous-singularity fiber. -/
theorem
    cubicTwoQuadricUniversalSingularChartFiber_isEmpty_of_not_mem_badLocus
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L)
    (hgood : Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint L) ∉
      cubicTwoQuadricUniversalSingularChartBadLocus
        p q hp hq v i) :
    IsEmpty (scheme
      (cubicTwoQuadricUniversalSingularChartFiberIdeal
        p q hp hq v i g)) :=
  ⟨fun z => hgood
    (cubicTwoQuadricUniversalSingularChartFiber_point_mem_badLocus
      p q hp hq v i g z)⟩

/-- Properness of the simultaneous zero family makes its bad-parameter image
closed on every normalized source chart. -/
theorem isClosed_cubicTwoQuadricUniversalSingularChartBadLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) (i : Fin n) :
    IsClosed (cubicTwoQuadricUniversalSingularChartBadLocus
      p q hp hq v i) := by
  let f := cubicTwoQuadricUniversalSingularChartFamilyToBase
    p q hp hq v i
  change IsClosed (Set.range f)
  letI : IsProper f :=
    cubicTwoQuadricUniversalSingularChartFamilyToBase_isProper
      p q hp hq v i
  exact f.isClosedMap.isClosed_range

/-- The global good set is the union, over all normalized source charts, of
the open complements of the proper simultaneous-zero images. -/
noncomputable def cubicTwoQuadricUniversalNonsingularParameterLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    Set (projectiveLinearSystemParameters (K := K) (τ := Fin n)) :=
  ⋃ i : Fin n,
    chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i ''
      (cubicTwoQuadricUniversalSingularChartBadLocus
        p q hp hq v i)ᶜ

theorem isOpen_cubicTwoQuadricUniversalNonsingularParameterLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    IsOpen (cubicTwoQuadricUniversalNonsingularParameterLocus
      p q hp hq v) := by
  apply isOpen_iUnion
  intro i
  exact (chartι
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i).isOpenMap _
      (isClosed_cubicTwoQuadricUniversalSingularChartBadLocus
        p q hp hq v i).isOpen_compl

/-- The global simultaneous singular-member locus in the common source
projective parameter space.  It is defined using the local families, so all
four Jacobian components are allowed to vanish identically. -/
noncomputable def cubicTwoQuadricUniversalSingularParameterLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    Set (projectiveLinearSystemParameters (K := K) (τ := Fin n)) :=
  (cubicTwoQuadricUniversalNonsingularParameterLocus
    p q hp hq v)ᶜ

/-- The simultaneous singular-member locus is globally closed on the source
projective parameter space. -/
theorem isClosed_cubicTwoQuadricUniversalSingularParameterLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2) :
    IsClosed (cubicTwoQuadricUniversalSingularParameterLocus
      p q hp hq v) := by
  exact (isOpen_cubicTwoQuadricUniversalNonsingularParameterLocus
    p q hp hq v).isClosed_compl

/-- If the universal simultaneous singular-member locus is proper, the
generic function-field parameter avoids it. -/
theorem
    genericFunctionField_closedPoint_avoids_cubicTwoQuadricUniversalSingularParameterLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    [IsIntegral (projectiveLinearSystemParameters (K := K) (τ := Fin n))]
    (hproper : cubicTwoQuadricUniversalSingularParameterLocus
      p q hp hq v ≠ Set.univ) :
    (projectiveLinearSystemParameters (K := K) (τ := Fin n)).fromSpecStalk
        (genericPoint
          (projectiveLinearSystemParameters (K := K) (τ := Fin n)))
        (IsLocalRing.closedPoint
          (projectiveLinearSystemParameters
            (K := K) (τ := Fin n)).functionField) ∉
      cubicTwoQuadricUniversalSingularParameterLocus
        p q hp hq v := by
  exact genericFunctionField_closedPoint_avoids_proper_closed
    (projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (isClosed_cubicTwoQuadricUniversalSingularParameterLocus
      p q hp hq v) hproper

/-- One explicit nonsingular parameter proves properness and hence generic
avoidance of the universal singular-member locus. -/
theorem
    genericFunctionField_closedPoint_avoids_cubicTwoQuadricUniversalSingularParameterLocus_of_exists
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    [IsIntegral (projectiveLinearSystemParameters (K := K) (τ := Fin n))]
    (hgood : ∃ t : projectiveLinearSystemParameters (K := K) (τ := Fin n),
      t ∉ cubicTwoQuadricUniversalSingularParameterLocus
        p q hp hq v) :
    (projectiveLinearSystemParameters (K := K) (τ := Fin n)).fromSpecStalk
        (genericPoint
          (projectiveLinearSystemParameters (K := K) (τ := Fin n)))
        (IsLocalRing.closedPoint
          (projectiveLinearSystemParameters
            (K := K) (τ := Fin n)).functionField) ∉
      cubicTwoQuadricUniversalSingularParameterLocus
        p q hp hq v := by
  apply
    genericFunctionField_closedPoint_avoids_cubicTwoQuadricUniversalSingularParameterLocus
      p q hp hq v
  rintro hbad
  obtain ⟨t, ht⟩ := hgood
  exact ht (by rw [hbad]; exact Set.mem_univ t)

/-- Avoiding the global closed locus supplies a normalized parameter chart on
which the simultaneous projective zero family has empty fiber at that
parameter. -/
theorem exists_cubicTwoQuadric_parameterChart_not_mem_badLocus_of_not_mem_singularParameterLocus
    {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (x : projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (hx : x ∉ cubicTwoQuadricUniversalSingularParameterLocus
      p q hp hq v) :
    ∃ (i : Fin n)
      (y : Spec (.of
        (ChartRing
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i))),
      chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i y = x ∧
      y ∉ cubicTwoQuadricUniversalSingularChartBadLocus
        p q hp hq v i := by
  have hxgood : x ∈
      cubicTwoQuadricUniversalNonsingularParameterLocus
        p q hp hq v := by
    simpa [cubicTwoQuadricUniversalSingularParameterLocus] using hx
  simp only [cubicTwoQuadricUniversalNonsingularParameterLocus,
    Set.mem_iUnion, Set.mem_image, Set.mem_compl_iff] at hxgood
  obtain ⟨i, y, hy, rfl⟩ := hxgood
  exact ⟨i, y, rfl, hy⟩

/-- A field-valued parameter outside the global singular locus factors
through a normalized source chart whose specialized singular fiber is empty.
The returned chart homomorphism retains the original coefficient-field map. -/
theorem
    exists_cubicTwoQuadric_parameterChartHom_not_mem_badLocus_of_fieldPoint_not_mem_singularParameterLocus
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (t : Spec (.of L) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (ht : t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
        Spec.map (CommRingCat.ofHom f))
    (hgood : t (IsLocalRing.closedPoint L) ∉
      cubicTwoQuadricUniversalSingularParameterLocus
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
        cubicTwoQuadricUniversalSingularChartBadLocus
          p q hp hq v i := by
  obtain ⟨i, y, hy, hygood⟩ :=
    exists_cubicTwoQuadric_parameterChart_not_mem_badLocus_of_not_mem_singularParameterLocus
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
cubics, the moving quadric, and all four Jacobian-minor equations. -/
theorem
    exists_cubicTwoQuadric_parameterChartHom_empty_singularFiber_of_fieldPoint_not_mem_singularParameterLocus
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (t : Spec (.of L) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (ht : t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
        Spec.map (CommRingCat.ofHom f))
    (hgood : t (IsLocalRing.closedPoint L) ∉
      cubicTwoQuadricUniversalSingularParameterLocus
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
        (cubicTwoQuadricUniversalSingularChartFiberIdeal
          p q hp hq v i g)) := by
  obtain ⟨i, g, hgbase, hgt, hgoodChart⟩ :=
    exists_cubicTwoQuadric_parameterChartHom_not_mem_badLocus_of_fieldPoint_not_mem_singularParameterLocus
      f p q hp hq v t ht hgood
  exact ⟨i, g, hgbase, hgt,
    cubicTwoQuadricUniversalSingularChartFiber_isEmpty_of_not_mem_badLocus
      p q hp hq v i g hgoodChart⟩

end

end PfaffianDescent
