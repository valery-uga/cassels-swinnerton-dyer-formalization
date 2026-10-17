import PfaffianDescent.VoisinTwelvePointSplitDescent
import PfaffianDescent.VoisinTwelvePointHilbertRegularity
import PfaffianDescent.CubicLineFiniteSubscheme
import PfaffianDescent.VoisinFiniteProjectiveCone

/-!
# Covering a cubic--quadric--quadric intersection by four line sections

If each of the two quadrics factors into two linear forms, their common
projective zero set lies on four lines. A three-point description of each
line's cubic section therefore gives the twelve-line affine-cone coverage
needed by the quadratic detection theorem. This isolates the remaining
line-section existence and transversality problems.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Four three-point line-section descriptions cover the affine cone of the
cubic and the two reducible quadrics. -/
theorem cubic_reducible_two_quadric_four_line_coverage
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K)
    (l m : Fin 2 → MvPolynomial (Fin 4) K)
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hp : p ∈ I) (hl : l 0 * l 1 ∈ I) (hm : m 0 * m 1 ∈ I)
    (x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → K)
    (hline : ∀ (a b : Fin 2) (y : Fin 4 → K),
      p.eval y = 0 → (l a).eval y = 0 → (m b).eval y = 0 →
      y = 0 ∨ ∃ (k : Fin 3) (c : K), y = c • x a b k) :
    ∀ y ∈ MvPolynomial.zeroLocus K I,
      y = 0 ∨ ∃ (a b : Fin 2) (k : Fin 3) (c : K),
        y = c • x a b k := by
  intro y hy
  have hp0 : p.eval y = 0 := hy p hp
  have hl0 : (l 0).eval y * (l 1).eval y = 0 := by
    simpa [MvPolynomial.eval_mul] using hy (l 0 * l 1) hl
  have hm0 : (m 0).eval y * (m 1).eval y = 0 := by
    simpa [MvPolynomial.eval_mul] using hy (m 0 * m 1) hm
  have ⟨a, ha⟩ : ∃ a : Fin 2, (l a).eval y = 0 := by
    rcases mul_eq_zero.mp hl0 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have ⟨b, hb⟩ : ∃ b : Fin 2, (m b).eval y = 0 := by
    rcases mul_eq_zero.mp hm0 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  rcases hline a b y hp0 ha hb with hzero | ⟨k, c, hxc⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨a, b, k, c, hxc⟩

/-- Reindex the four triples as twelve representatives for the existing
Nullstellensatz detection interface. -/
theorem cubic_reducible_two_quadric_twelve_point_coverage
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K)
    (l m : Fin 2 → MvPolynomial (Fin 4) K)
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hp : p ∈ I) (hl : l 0 * l 1 ∈ I) (hm : m 0 * m 1 ∈ I)
    (x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → K)
    (hline : ∀ (a b : Fin 2) (y : Fin 4 → K),
      p.eval y = 0 → (l a).eval y = 0 → (m b).eval y = 0 →
      y = 0 ∨ ∃ (k : Fin 3) (c : K), y = c • x a b k) :
    ∃ x₁₂ : Fin 12 → Fin 4 → K,
      (∀ i, ∃ (a b : Fin 2) (k : Fin 3), x₁₂ i = x a b k) ∧
      ∀ y ∈ MvPolynomial.zeroLocus K I,
        y = 0 ∨ ∃ (i : Fin 12) (c : K), y = c • x₁₂ i := by
  classical
  let e : Fin 12 ≃ Fin 2 × Fin 2 × Fin 3 :=
    (Fintype.equivFinOfCardEq (by decide :
      Fintype.card (Fin 2 × Fin 2 × Fin 3) = 12)).symm
  let x₁₂ : Fin 12 → Fin 4 → K := fun i => x (e i).1 (e i).2.1 (e i).2.2
  refine ⟨x₁₂, ?_, ?_⟩
  · intro i
    exact ⟨(e i).1, (e i).2.1, (e i).2.2, rfl⟩
  intro y hy
  rcases cubic_reducible_two_quadric_four_line_coverage
      p l m I hp hl hm x hline y hy with hzero | ⟨a, b, k, c, hxc⟩
  · exact Or.inl hzero
  · right
    refine ⟨e.symm (a, b, k), c, ?_⟩
    simpa [x₁₂] using hxc

/-- Four finite cubic line sections make the projective triple intersection
finite, even when its homogeneous ideal is not known to be radical. -/
theorem cubic_reducible_two_quadric_intersection_finite_of_four_line_coverage
    {L : Type u} [Field L] [IsAlgClosed L]
    (p q r : MvPolynomial (Fin 4) L)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hr : r.IsHomogeneous 2)
    (l m : Fin 2 → MvPolynomial (Fin 4) L)
    (hqfactor : q = l 0 * l 1)
    (hrfactor : r = m 0 * m 1)
    (x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L)
    (hline : ∀ (a b : Fin 2) (y : Fin 4 → L),
      p.eval y = 0 → (l a).eval y = 0 → (m b).eval y = 0 →
      y = 0 ∨ ∃ (k : Fin 3) (c : L), y = c • x a b k) :
    IsFinite (AllCharacteristics.HomogeneousProjective.toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  have hpI : p ∈ I.toIdeal := Ideal.subset_span (by simp)
  have hqI : q ∈ I.toIdeal := Ideal.subset_span (by simp)
  have hrI : r ∈ I.toIdeal := Ideal.subset_span (by simp)
  obtain ⟨x₁₂, -, hcover⟩ :=
    cubic_reducible_two_quadric_twelve_point_coverage
      p l m I.toIdeal hpI (hqfactor ▸ hqI) (hrfactor ▸ hrI) x hline
  exact isFinite_projective_of_finite_cone_coverage I x₁₂ hcover

/-- Four split line sections detect every positive-degree homogeneous
ground-field equation after passing to an algebraically closed extension.
This is the all-degree version of the quadratic detector below and is the
input needed for an eventual Hilbert bound. -/
theorem homogeneous_detection_descends_from_four_split_line_sections
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p q r t : MvPolynomial (Fin 4) K)
    (d : ℕ) (hd : 0 < d) (ht : t.IsHomogeneous d)
    (IL : Ideal (MvPolynomial (Fin 4) L))
    (hIL : IL = Ideal.span ({p.map (algebraMap K L),
      q.map (algebraMap K L), r.map (algebraMap K L)} :
        Set (MvPolynomial (Fin 4) L)))
    (hrad : IL.IsRadical)
    (l m : Fin 2 → MvPolynomial (Fin 4) L)
    (hqfactor : q.map (algebraMap K L) = l 0 * l 1)
    (hrfactor : r.map (algebraMap K L) = m 0 * m 1)
    (x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L)
    (hline : ∀ (a b : Fin 2) (y : Fin 4 → L),
      (p.map (algebraMap K L)).eval y = 0 →
      (l a).eval y = 0 → (m b).eval y = 0 →
      y = 0 ∨ ∃ (k : Fin 3) (c : L), y = c • x a b k)
    (hzero : ∀ (a b : Fin 2) (k : Fin 3),
      MvPolynomial.aeval (x a b k) (t.map (algebraMap K L)) = 0) :
    t ∈ Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)) := by
  have hpI : p.map (algebraMap K L) ∈ IL := by
    rw [hIL]
    exact Ideal.subset_span (by simp)
  have hqI : q.map (algebraMap K L) ∈ IL := by
    rw [hIL]
    exact Ideal.subset_span (by simp)
  have hrI : r.map (algebraMap K L) ∈ IL := by
    rw [hIL]
    exact Ideal.subset_span (by simp)
  obtain ⟨x₁₂, hindex, hcover⟩ :=
    cubic_reducible_two_quadric_twelve_point_coverage
      (p.map (algebraMap K L)) l m IL hpI
      (hqfactor ▸ hqI) (hrfactor ▸ hrI) x hline
  have hzero₁₂ : ∀ i, MvPolynomial.aeval (x₁₂ i)
      (t.map (algebraMap K L)) = 0 := by
    intro i
    obtain ⟨a, b, k, hx⟩ := hindex i
    rw [hx]
    exact hzero a b k
  exact homogeneous_detection_descends_from_split_twelve_points
    p q r t d hd ht IL hIL hrad x₁₂ hcover hzero₁₂

/-- Roots of the cubic on the four lines cut out by the two split quadrics
are automatically points of the full triple-intersection zero locus. -/
theorem cubic_reducible_two_quadric_line_roots_mem_zeroLocus
    {L : Type u} [Field L]
    (p q r : MvPolynomial (Fin 4) L)
    (l m : Fin 2 → MvPolynomial (Fin 4) L)
    (hqfactor : q = l 0 * l 1)
    (hrfactor : r = m 0 * m 1)
    (x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L)
    (hroots : ∀ (a b : Fin 2) (k : Fin 3),
      MvPolynomial.aeval (x a b k) p = 0 ∧
      MvPolynomial.aeval (x a b k) (l a) = 0 ∧
      MvPolynomial.aeval (x a b k) (m b) = 0) :
    ∀ (a b : Fin 2) (k : Fin 3),
      x a b k ∈ MvPolynomial.zeroLocus L
        (tripleCompleteIntersectionIdeal p q r) := by
  intro a b k
  rw [tripleCompleteIntersectionIdeal, MvPolynomial.zeroLocus_span]
  rintro s (rfl | rfl | rfl)
  · exact (hroots a b k).1
  · obtain ⟨_, hl, _⟩ := hroots a b k
    rw [hqfactor, map_mul]
    fin_cases a <;> simp_all
  · obtain ⟨_, _, hm⟩ := hroots a b k
    rw [hrfactor, map_mul]
    fin_cases b <;> simp_all

/-- A separable restriction of a cubic to one parametrized line supplies the
three roots, their line equations, and complete affine-cone coverage of that
line section. The parameterization hypothesis is purely linear algebra. -/
theorem exists_three_cubic_line_roots_cover_of_separable
    {L : Type u} [Field L] [IsAlgClosed L]
    (p ell mu : MvPolynomial (Fin 4) L)
    (hell : ell.IsHomogeneous 1) (hmu : mu.IsHomogeneous 1)
    (c : Cubic L 4) (hc : c.toMvPolynomial = p)
    (a b : Vec L 4)
    (ha : c.eval a ≠ 0)
    (hella : ell.eval a = 0) (hellb : ell.eval b = 0)
    (hmua : mu.eval a = 0) (hmub : mu.eval b = 0)
    (hparam : ∀ y : Fin 4 → L,
      ell.eval y = 0 → mu.eval y = 0 →
      ∃ s t : L, y = s • a + t • b)
    (hsep : (AllCharacteristics.cubicLinePolynomial c a b).Separable) :
    ∃ x : Fin 3 → Fin 4 → L,
      Function.Injective x ∧
      (∀ k, p.eval (x k) = 0 ∧
        ell.eval (x k) = 0 ∧ mu.eval (x k) = 0) ∧
      ∀ y : Fin 4 → L,
        p.eval y = 0 → ell.eval y = 0 → mu.eval y = 0 →
        y = 0 ∨ ∃ (k : Fin 3) (t : L), y = t • x k := by
  obtain ⟨x, hx, hxinj, hxform, hcover⟩ :=
    AllCharacteristics.exists_three_cubic_line_points_cover_of_separable
      c a b ha hsep
  refine ⟨x, hxinj, ?_, ?_⟩
  · intro k
    obtain ⟨t, ht⟩ := hxform k
    have hp0 : p.eval (x k) = 0 := by
      rw [← hc]
      change MvPolynomial.eval₂ (RingHom.id L) (x k) c.toMvPolynomial = 0
      rw [Cubic.eval_toMvPolynomial]
      change c.eval (x k) = 0
      exact hx k
    have hell0 : ell.eval (x k) = 0 := by
      rw [ht]
      change ell.eval₂ (RingHom.id L) (t • a + b) = 0
      simpa [hella, hellb] using
        (eval₂_homogeneous_degree_one_line (RingHom.id L) ell hell a b t)
    have hmu0 : mu.eval (x k) = 0 := by
      rw [ht]
      change mu.eval₂ (RingHom.id L) (t • a + b) = 0
      simpa [hmua, hmub] using
        (eval₂_homogeneous_degree_one_line (RingHom.id L) mu hmu a b t)
    exact ⟨hp0, hell0, hmu0⟩
  · intro y hp0 hell0 hmu0
    obtain ⟨s, t, hy⟩ := hparam y hell0 hmu0
    subst y
    apply hcover s t
    rw [← hc] at hp0
    change MvPolynomial.eval₂ (RingHom.id L) (s • a + t • b) c.toMvPolynomial = 0 at hp0
    rw [Cubic.eval_toMvPolynomial] at hp0
    change c.eval (s • a + t • b) = 0 at hp0
    exact hp0

/-- Four separable cubic line restrictions provide the four triples of
projective roots and the exact four-line coverage predicate used below. -/
theorem exists_four_three_point_line_sections_of_separable
    {L : Type u} [Field L] [IsAlgClosed L]
    (c : Cubic L 4)
    (l m : Fin 2 → MvPolynomial (Fin 4) L)
    (hl : ∀ i, (l i).IsHomogeneous 1)
    (hm : ∀ i, (m i).IsHomogeneous 1)
    (u v : Fin 2 → Fin 2 → Vec L 4)
    (hu : ∀ i j, c.eval (u i j) ≠ 0)
    (hlroots : ∀ i j, (l i).eval (u i j) = 0 ∧
      (l i).eval (v i j) = 0)
    (hmroots : ∀ i j, (m j).eval (u i j) = 0 ∧
      (m j).eval (v i j) = 0)
    (hparam : ∀ i j (y : Fin 4 → L),
      (l i).eval y = 0 → (m j).eval y = 0 →
      ∃ s t : L, y = s • u i j + t • v i j)
    (hsep : ∀ i j,
      (AllCharacteristics.cubicLinePolynomial c (u i j) (v i j)).Separable) :
    ∃ x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L,
      (∀ i j, Function.Injective (x i j)) ∧
      (∀ i j k,
        c.toMvPolynomial.eval (x i j k) = 0 ∧
        (l i).eval (x i j k) = 0 ∧
        (m j).eval (x i j k) = 0) ∧
      ∀ i j (y : Fin 4 → L),
        c.toMvPolynomial.eval y = 0 →
        (l i).eval y = 0 → (m j).eval y = 0 →
        y = 0 ∨ ∃ (k : Fin 3) (t : L), y = t • x i j k := by
  classical
  have hlocal : ∀ i j : Fin 2,
      ∃ x : Fin 3 → Fin 4 → L,
        Function.Injective x ∧
        (∀ k, c.toMvPolynomial.eval (x k) = 0 ∧
          (l i).eval (x k) = 0 ∧ (m j).eval (x k) = 0) ∧
        ∀ y : Fin 4 → L,
          c.toMvPolynomial.eval y = 0 →
          (l i).eval y = 0 → (m j).eval y = 0 →
          y = 0 ∨ ∃ (k : Fin 3) (t : L), y = t • x k := by
    intro i j
    exact exists_three_cubic_line_roots_cover_of_separable
      c.toMvPolynomial (l i) (m j) (hl i) (hm j) c rfl
      (u i j) (v i j) (hu i j)
      (hlroots i j).1 (hlroots i j).2
      (hmroots i j).1 (hmroots i j).2
      (hparam i j) (hsep i j)
  choose x hxinj hxroots hxcover using hlocal
  exact ⟨x, hxinj, hxroots, hxcover⟩

/-- Four split line sections certify ground-field quadratic detection, even
when the line factors and twelve intersection representatives exist only over
an algebraically closed extension. -/
theorem quadratic_detection_descends_from_four_split_line_sections
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p q r t : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (ht : t.IsHomogeneous 2)
    (I : Ideal (MvPolynomial (Fin 4) K))
    (hI : I = Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) K)))
    (IL : Ideal (MvPolynomial (Fin 4) L))
    (hIL : IL = Ideal.span ({p.map (algebraMap K L),
      q.map (algebraMap K L), r.map (algebraMap K L)} :
        Set (MvPolynomial (Fin 4) L)))
    (hrad : IL.IsRadical)
    (l m : Fin 2 → MvPolynomial (Fin 4) L)
    (hqfactor : q.map (algebraMap K L) = l 0 * l 1)
    (hrfactor : r.map (algebraMap K L) = m 0 * m 1)
    (x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L)
    (hline : ∀ (a b : Fin 2) (y : Fin 4 → L),
      (p.map (algebraMap K L)).eval y = 0 →
      (l a).eval y = 0 → (m b).eval y = 0 →
      y = 0 ∨ ∃ (k : Fin 3) (c : L), y = c • x a b k)
    (hzero : ∀ (a b : Fin 2) (k : Fin 3),
      MvPolynomial.aeval (x a b k) (t.map (algebraMap K L)) = 0) :
    t ∈ I := by
  rw [hI]
  exact homogeneous_detection_descends_from_four_split_line_sections
    p q r t 2 (by decide) ht IL hIL hrad l m hqfactor hrfactor
    x hline hzero

/-- A four-line description of a reduced cubic--quadric--quadric intersection
certifies regularity of the quadratic pair over the ground field. The line
representatives may exist only over the algebraically closed extension. -/
theorem cubic_two_quadric_regular_descends_from_four_split_line_sections
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hp0L : p.map (algebraMap K L) ≠ 0)
    (hrelL : IsRelPrime (p.map (algebraMap K L))
      (q.map (algebraMap K L)))
    (hrad : (tripleCompleteIntersectionIdeal
      (p.map (algebraMap K L)) (q.map (algebraMap K L))
      (r.map (algebraMap K L))).IsRadical)
    (l m : Fin 2 → MvPolynomial (Fin 4) L)
    (hqfactor : q.map (algebraMap K L) = l 0 * l 1)
    (hrfactor : r.map (algebraMap K L) = m 0 * m 1)
    (x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L)
    (hroots : ∀ (a b : Fin 2) (k : Fin 3),
      MvPolynomial.aeval (x a b k) (p.map (algebraMap K L)) = 0 ∧
      MvPolynomial.aeval (x a b k) (l a) = 0 ∧
      MvPolynomial.aeval (x a b k) (m b) = 0)
    (hline : ∀ (a b : Fin 2) (y : Fin 4 → L),
      (p.map (algebraMap K L)).eval y = 0 →
      (l a).eval y = 0 → (m b).eval y = 0 →
      y = 0 ∨ ∃ (k : Fin 3) (c : L), y = c • x a b k) :
    ∀ f : MvPolynomial (Fin 4) K,
      r * f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  let φ := algebraMap K L
  let I := tripleCompleteIntersectionIdeal (p.map φ) (q.map φ) (r.map φ)
  have hpI : p.map φ ∈ I := Ideal.subset_span (by simp)
  have hqI : q.map φ ∈ I := Ideal.subset_span (by simp)
  have hrI : r.map φ ∈ I := Ideal.subset_span (by simp)
  obtain ⟨x₁₂, hindex, hcover⟩ :=
    cubic_reducible_two_quadric_twelve_point_coverage
      (p.map φ) l m I hpI (hqfactor ▸ hqI) (hrfactor ▸ hrI)
      x hline
  have hpoints₁₂ : ∀ i, x₁₂ i ∈ MvPolynomial.zeroLocus L I := by
    intro i
    obtain ⟨a, b, k, hx⟩ := hindex i
    rw [hx]
    exact cubic_reducible_two_quadric_line_roots_mem_zeroLocus
      (p.map φ) (q.map φ) (r.map φ) l m hqfactor hrfactor
      x hroots a b k
  exact twelve_point_cubic_two_quadric_regular_descends
    p q r hp hq hr hp0L hrelL hrad x₁₂ hpoints₁₂ hcover

/-- Separable cubic restrictions on the four lines supply the root and
coverage hypotheses of the four-line regularity descent theorem. -/
theorem cubic_two_quadric_regular_descends_from_four_separable_line_sections
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hp0L : p.map (algebraMap K L) ≠ 0)
    (hrelL : IsRelPrime (p.map (algebraMap K L))
      (q.map (algebraMap K L)))
    (hrad : (tripleCompleteIntersectionIdeal
      (p.map (algebraMap K L)) (q.map (algebraMap K L))
      (r.map (algebraMap K L))).IsRadical)
    (c : Cubic L 4) (hc : c.toMvPolynomial = p.map (algebraMap K L))
    (l m : Fin 2 → MvPolynomial (Fin 4) L)
    (hl : ∀ i, (l i).IsHomogeneous 1)
    (hm : ∀ i, (m i).IsHomogeneous 1)
    (hqfactor : q.map (algebraMap K L) = l 0 * l 1)
    (hrfactor : r.map (algebraMap K L) = m 0 * m 1)
    (u v : Fin 2 → Fin 2 → Vec L 4)
    (hu : ∀ i j, c.eval (u i j) ≠ 0)
    (hlroots : ∀ i j, (l i).eval (u i j) = 0 ∧
      (l i).eval (v i j) = 0)
    (hmroots : ∀ i j, (m j).eval (u i j) = 0 ∧
      (m j).eval (v i j) = 0)
    (hparam : ∀ i j (y : Fin 4 → L),
      (l i).eval y = 0 → (m j).eval y = 0 →
      ∃ s t : L, y = s • u i j + t • v i j)
    (hsep : ∀ i j,
      (AllCharacteristics.cubicLinePolynomial c (u i j) (v i j)).Separable) :
    ∀ f : MvPolynomial (Fin 4) K,
      r * f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  obtain ⟨x, -, hroots, hline⟩ :=
    exists_four_three_point_line_sections_of_separable
      c l m hl hm u v hu hlroots hmroots hparam hsep
  apply cubic_two_quadric_regular_descends_from_four_split_line_sections
    p q r hp hq hr hp0L hrelL hrad l m hqfactor hrfactor x
  · intro a b k
    simpa [hc] using hroots a b k
  · intro a b y hpzero hlzero hmzero
    exact hline a b y (by simpa [hc] using hpzero) hlzero hmzero

end PfaffianDescent
