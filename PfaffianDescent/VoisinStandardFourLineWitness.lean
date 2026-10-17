import PfaffianDescent.VoisinFourLineFiniteWithoutSeparability
import PfaffianDescent.MultivariateCubic
import PfaffianDescent.ProjectiveVectorIdeal
import PfaffianDescent.VoisinProjectiveVectorSchemePoint
import Mathlib.Algebra.CharZero.Infinite

/-!
# A coordinate four-line witness

Two reducible quadrics cut four genuine lines through the first coordinate
point. A cubic nonzero there restricts nontrivially to all four lines.
-/

namespace PfaffianDescent

open MvPolynomial AlgebraicGeometry CategoryTheory AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

private def e {L : Type u} [Field L] (i : Fin 4) : Vec L 4 := Pi.single i 1

/-- A nonzero cubic over an infinite field is nonzero at a vector in the
first standard affine chart. -/
theorem exists_cubic_nonzero_in_first_chart
    {L : Type u} [Field L] [Infinite L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0) :
    ∃ a : Fin 4 → L, p.eval a ≠ 0 ∧ a 0 ≠ 0 := by
  have hprod : (p * X 0).IsHomogeneous 4 := hp.mul (isHomogeneous_X L 0)
  have hprod0 : p * X 0 ≠ 0 :=
    mul_ne_zero hp0 (MvPolynomial.X_ne_zero 0)
  obtain ⟨a, ha⟩ := exists_vector_eval_ne_zero_of_homogeneous
    (p * X 0) hprod hprod0
  refine ⟨a, ?_, ?_⟩
  · exact (mul_ne_zero_iff.mp (by simpa using ha)).1
  · exact (mul_ne_zero_iff.mp (by simpa using ha)).2

def lineDirection {L : Type u} [Field L] (a b : Fin 2) : Vec L 4 :=
  if a = 0 then
    if b = 0 then Pi.single 2 1 else Pi.single 2 1 - Pi.single 3 1
  else
    if b = 0 then Pi.single 1 1 else Pi.single 1 1 - Pi.single 3 1

private noncomputable def firstLinear {L : Type u} [Field L] (a : Fin 2) :
    MvPolynomial (Fin 4) L := if a = 0 then X 1 else X 2

private noncomputable def secondLinear {L : Type u} [Field L] (b : Fin 2) :
    MvPolynomial (Fin 4) L := if b = 0 then X 3 else X 1 + X 2 + X 3

/-- The four coordinate line sections have genuine two-dimensional spans. -/
theorem standardFourLines_genuine
    {L : Type u} [Field L] (a b : Fin 2) (t : L) :
    t • e (L := L) 0 + lineDirection a b ≠ 0 := by
  intro h
  have hk := congrFun h (if a = 0 then (2 : Fin 4) else 1)
  fin_cases a <;> fin_cases b <;>
    simp [lineDirection, e] at hk

/-- Every joint linear kernel is spanned by its designated pair. -/
theorem standardFourLines_span
    {L : Type u} [Field L] (a b : Fin 2) (y : Fin 4 → L)
    (ha : (firstLinear a).eval y = 0)
    (hb : (secondLinear b).eval y = 0) :
    ∃ s t : L, y = s • e 0 + t • lineDirection a b := by
  refine ⟨y 0, if a = 0 then y 2 else y 1, ?_⟩
  fin_cases a <;> fin_cases b
  all_goals
    simp [firstLinear, secondLinear] at ha hb
    funext i
    fin_cases i <;>
      simp [lineDirection, e, Pi.single, ha, hb] <;> grind

/-- A cubic nonzero at the first coordinate point has finite intersection
with the two standard split quadrics. -/
theorem standardFourLines_finite
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (hpoint : p.eval (e 0) ≠ 0) :
    IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      p (X 1 * X 2) (X 3 * (X 1 + X 2 + X 3)) hp
      ((isHomogeneous_X L 1).mul (isHomogeneous_X L 2))
      ((isHomogeneous_X L 3).mul
        (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
          (isHomogeneous_X L 3))))) := by
  obtain ⟨c, hc⟩ := homogeneous_cubic_has_tensor p hp
  apply cubic_reducible_two_quadric_intersection_finite_of_four_nonzero_line_sections
    p (X 1 * X 2) (X 3 * (X 1 + X 2 + X 3)) hp
    ((isHomogeneous_X L 1).mul (isHomogeneous_X L 2))
    ((isHomogeneous_X L 3).mul
      (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
        (isHomogeneous_X L 3)))
    c hc firstLinear secondLinear
    (by simp [firstLinear]) (by simp [secondLinear])
    (fun _ _ => e 0) lineDirection
  · intro a b
    rw [← hc] at hpoint
    change MvPolynomial.eval₂ (RingHom.id L) (e 0) c.toMvPolynomial ≠ 0 at hpoint
    rwa [Cubic.eval_toMvPolynomial] at hpoint
  · intro a b y ha hb
    exact standardFourLines_span a b y ha hb

/-- The same explicit witness makes the second quadric a non-zero-divisor
modulo the cubic and first quadric. -/
theorem standardFourLines_regular
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (hpoint : p.eval (e 0) ≠ 0) :
    ∀ F : MvPolynomial (Fin 4) L,
      (X 3 * (X 1 + X 2 + X 3)) * F ∈
        Ideal.span ({p, X 1 * X 2} : Set (MvPolynomial (Fin 4) L)) →
      F ∈ Ideal.span ({p, X 1 * X 2} : Set (MvPolynomial (Fin 4) L)) := by
  obtain ⟨c, hc⟩ := homogeneous_cubic_has_tensor p hp
  apply cubic_two_quadric_regular_descends_from_four_nonzero_line_sections
    p (X 1 * X 2) (X 3 * (X 1 + X 2 + X 3)) hp
    ((isHomogeneous_X L 1).mul (isHomogeneous_X L 2))
    ((isHomogeneous_X L 3).mul
      (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
        (isHomogeneous_X L 3)))
    c (by simpa only [Algebra.algebraMap_self, MvPolynomial.map_id] using hc)
    firstLinear secondLinear
    (by intro i; fin_cases i <;> simp [firstLinear, isHomogeneous_X])
    (by
      intro i
      fin_cases i
      · exact isHomogeneous_X L 3
      · exact ((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
          (isHomogeneous_X L 3))
    (by simp [firstLinear]) (by simp [secondLinear])
    (fun _ _ => e 0) lineDirection
  · intro a b
    rw [← hc] at hpoint
    change MvPolynomial.eval₂ (RingHom.id L) (e 0) c.toMvPolynomial ≠ 0 at hpoint
    rwa [Cubic.eval_toMvPolynomial] at hpoint
  · exact standardFourLines_genuine
  · intro a b
    constructor <;> fin_cases a <;> fin_cases b <;>
      simp [firstLinear, lineDirection, e, Pi.single]
  · intro a b
    constructor <;> fin_cases a <;> fin_cases b <;>
      simp [secondLinear, lineDirection, e, Pi.single]
  · intro a b y ha hb
    exact standardFourLines_span a b y ha hb

private noncomputable def shearLinear {L : Type u} [Field L]
    (a : Fin 4 → L) (i : Fin 4) : MvPolynomial (Fin 4) L :=
  X i - C (a i / a 0) * X 0

private noncomputable def firstSheared {L : Type u} [Field L]
    (a : Fin 4 → L) (i : Fin 2) : MvPolynomial (Fin 4) L :=
  if i = 0 then shearLinear a 1 else shearLinear a 2

private noncomputable def secondSheared {L : Type u} [Field L]
    (a : Fin 4 → L) (i : Fin 2) : MvPolynomial (Fin 4) L :=
  if i = 0 then shearLinear a 3
  else shearLinear a 1 + shearLinear a 2 + shearLinear a 3

private theorem shearLinear_eval
    {L : Type u} [Field L] (a y : Fin 4 → L) (i : Fin 4) :
    (shearLinear a i).eval y = (y - (y 0 / a 0) • a) i := by
  simp [shearLinear, Pi.sub_apply, Pi.smul_apply]
  ring

private theorem firstSheared_eval
    {L : Type u} [Field L] (a y : Fin 4 → L) (i : Fin 2) :
    (firstSheared a i).eval y =
      (firstLinear i).eval (y - (y 0 / a 0) • a) := by
  fin_cases i <;> simp [firstSheared, firstLinear, shearLinear_eval]

private theorem secondSheared_eval
    {L : Type u} [Field L] (a y : Fin 4 → L) (i : Fin 2) :
    (secondSheared a i).eval y =
      (secondLinear i).eval (y - (y 0 / a 0) • a) := by
  fin_cases i <;>
    simp [secondSheared, secondLinear, shearLinear_eval, MvPolynomial.eval_add]

/-- The sheared four-line equations have exactly the expected line kernels. -/
theorem shearedFourLines_span
    {L : Type u} [Field L]
    (a y : Fin 4 → L) (ha0 : a 0 ≠ 0) (i j : Fin 2)
    (hi : (firstSheared a i).eval y = 0)
    (hj : (secondSheared a j).eval y = 0) :
    ∃ s t : L, y = s • a + t • lineDirection i j := by
  let z := y - (y 0 / a 0) • a
  have hz0 : z 0 = 0 := by
    simp [z, Pi.sub_apply, Pi.smul_apply, ha0]
  have hzi : (firstLinear i).eval z = 0 := by
    simpa only [firstSheared_eval, z] using hi
  have hzj : (secondLinear j).eval z = 0 := by
    simpa only [secondSheared_eval, z] using hj
  obtain ⟨s, t, hzt⟩ := standardFourLines_span i j z hzi hzj
  have hs : s = 0 := by
    have h := congrFun hzt 0
    have hv0 : (lineDirection (L := L) i j) 0 = 0 := by
      fin_cases i <;> fin_cases j <;> simp [lineDirection, e]
    simpa [hz0, e, hv0] using h.symm
  subst s
  refine ⟨y 0 / a 0, t, ?_⟩
  calc
    y = (y 0 / a 0) • a + z := by simp [z]
    _ = (y 0 / a 0) • a + t • lineDirection i j := by rw [hzt]; simp

private theorem shearLinear_homogeneous
    {L : Type u} [Field L] (a : Fin 4 → L) (i : Fin 4) :
    (shearLinear a i).IsHomogeneous 1 :=
  (isHomogeneous_X L i).sub
    ((isHomogeneous_C_mul_X (a i / a 0) 0))

/-- Every nonzero homogeneous cubic admits two explicit split quadrics whose
projective triple intersection is finite. -/
theorem exists_split_quadric_pair_finite_intersection
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0) :
    ∃ (q r : MvPolynomial (Fin 4) L)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  obtain ⟨a, hpa, ha0⟩ := exists_cubic_nonzero_in_first_chart p hp hp0
  let l := firstSheared a
  let m := secondSheared a
  let q := l 0 * l 1
  let r := m 0 * m 1
  have hl : ∀ i, (l i).IsHomogeneous 1 := by
    intro i
    fin_cases i <;> simp [l, firstSheared, shearLinear_homogeneous]
  have hm : ∀ j, (m j).IsHomogeneous 1 := by
    intro j
    fin_cases j
    · exact shearLinear_homogeneous a 3
    · exact ((shearLinear_homogeneous a 1).add
        (shearLinear_homogeneous a 2)).add (shearLinear_homogeneous a 3)
  have hq : q.IsHomogeneous 2 := (hl 0).mul (hl 1)
  have hr : r.IsHomogeneous 2 := (hm 0).mul (hm 1)
  refine ⟨q, r, hq, hr, ?_⟩
  obtain ⟨c, hc⟩ := homogeneous_cubic_has_tensor p hp
  apply cubic_reducible_two_quadric_intersection_finite_of_four_nonzero_line_sections
    p q r hp hq hr c hc l m rfl rfl
    (fun _ _ => a) lineDirection
  · intro i j
    rw [← hc] at hpa
    change MvPolynomial.eval₂ (RingHom.id L) a c.toMvPolynomial ≠ 0 at hpa
    rwa [Cubic.eval_toMvPolynomial] at hpa
  · intro i j y hi hj
    exact shearedFourLines_span a y ha0 i j hi hj

private theorem shearedFourLines_genuine
    {L : Type u} [Field L] (a : Fin 4 → L) (ha0 : a 0 ≠ 0)
    (i j : Fin 2) (t : L) : t • a + lineDirection i j ≠ 0 := by
  intro h
  have hv0 : (lineDirection (L := L) i j) 0 = 0 := by
    fin_cases i <;> fin_cases j <;> simp [lineDirection, e]
  have ht0 : t * a 0 = 0 := by
    have h0 := congrFun h 0
    simpa [hv0] using h0
  have ht : t = 0 := (mul_eq_zero.mp ht0).resolve_right ha0
  subst t
  exact standardFourLines_genuine (L := L) i j (0 : L) (by simpa using h)

/-- The base vector and each of the four line directions have unique
two-coefficient representations. -/
theorem shearedFourLines_unique_representation
    {L : Type u} [Field L] (a : Fin 4 → L) (ha0 : a 0 ≠ 0)
    (i j : Fin 2) (s t : L)
    (h : s • a + t • lineDirection i j = 0) : s = 0 ∧ t = 0 := by
  have hd0 : (lineDirection (L := L) i j) 0 = 0 := by
    fin_cases i <;> fin_cases j <;> simp [lineDirection, e]
  have hs0 : s * a 0 = 0 := by
    have h0 := congrFun h 0
    simpa [hd0] using h0
  have hs : s = 0 := (mul_eq_zero.mp hs0).resolve_right ha0
  have hd : lineDirection (L := L) i j ≠ 0 := by
    simpa using shearedFourLines_genuine a ha0 i j (0 : L)
  have ht0 : t • lineDirection (L := L) i j = 0 := by simpa [hs] using h
  exact ⟨hs, (smul_eq_zero.mp ht0).resolve_right hd⟩

/-- Different members of the explicit four-line arrangement have
nonproportional directions, even before choosing the base point. -/
theorem lineDirection_nonproportional
    {L : Type u} [Field L]
    {i j i' j' : Fin 2} (hpair : (i, j) ≠ (i', j')) (c : L) :
    lineDirection (L := L) i j ≠ c • lineDirection i' j' := by
  intro h
  have h1 := congrFun h (1 : Fin 4)
  have h2 := congrFun h (2 : Fin 4)
  have h3 := congrFun h (3 : Fin 4)
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j'
  all_goals simp [lineDirection, e, Pi.single_apply, Pi.smul_apply] at hpair h1 h2 h3
  all_goals first
    | exact one_ne_zero (h2.trans h3)
    | exact one_ne_zero (h1.trans h3)

/-- Roots on different members of the explicit four-line arrangement can
never represent the same projective direction. -/
theorem shearedFourLines_cross_line_projectively_distinct
    {L : Type u} [Field L]
    (a : Fin 4 → L) (ha0 : a 0 ≠ 0)
    {ι : Type*} (x : Fin 2 → Fin 2 → ι → Fin 4 → L)
    (hform : ∀ i j k, ∃ t : L, x i j k = t • a + lineDirection i j)
    {i j i' j' : Fin 2} (hpair : (i, j) ≠ (i', j'))
    (k k' : ι) (c : L) : c • x i j k ≠ x i' j' k' := by
  intro h
  obtain ⟨s, hs⟩ := hform i j k
  obtain ⟨t, ht⟩ := hform i' j' k'
  have hd0 : ∀ p q : Fin 2, (lineDirection (L := L) p q) 0 = 0 := by
    intro p q
    fin_cases p <;> fin_cases q <;> simp [lineDirection, e]
  have h' : c • (s • a + lineDirection i j) =
      t • a + lineDirection i' j' := by simpa [hs, ht] using h
  have hcs : c * s = t := by
    have h0 := congrFun h' 0
    simp only [Pi.add_apply, Pi.smul_apply, hd0] at h0
    exact mul_right_cancel₀ ha0 (by simpa [mul_assoc] using h0)
  have hdir : lineDirection (L := L) i' j' =
      c • lineDirection i j := by
    funext m
    have hm := congrFun h' m
    simp only [Pi.add_apply, Pi.smul_apply] at hm ⊢
    calc
      (lineDirection (L := L) i' j') m =
          c * (s * a m + (lineDirection (L := L) i j) m) - t * a m := by
            linear_combination -hm
      _ = c * (lineDirection (L := L) i j) m := by rw [← hcs]; ring
  exact lineDirection_nonproportional hpair.symm c hdir

/-- All twelve roots arising from three roots on each of the four explicit
line sections have pairwise distinct projective directions. -/
theorem shearedFourLines_twelve_roots_projectively_distinct
    {L : Type u} [Field L]
    (a : Fin 4 → L) (ha0 : a 0 ≠ 0)
    (x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L)
    (hinj : ∀ i j, Function.Injective (x i j))
    (hform : ∀ i j k, ∃ t : L, x i j k = t • a + lineDirection i j)
    {i j i' j' : Fin 2} {k k' : Fin 3}
    (hindex : (i, j, k) ≠ (i', j', k')) (c : L) :
    c • x i j k ≠ x i' j' k' := by
  by_cases hpair : (i, j) = (i', j')
  · have hi : i = i' := congrArg Prod.fst hpair
    have hj : j = j' := congrArg Prod.snd hpair
    subst i'
    subst j'
    have hk : k ≠ k' := by
      intro hkk
      exact hindex (by simpa [hkk])
    exact affineLineRoots_projectively_distinct
      (shearedFourLines_unique_representation a ha0 i j)
      (hinj i j) (hform i j) hk c
  · exact shearedFourLines_cross_line_projectively_distinct
      a ha0 x hform hpair k k' c

/-- The twelve roots on the four explicit lines become twelve genuinely
distinct rational scheme points whenever they satisfy the equations of a
homogeneous projective subscheme. -/
theorem exists_twelve_distinct_scheme_points_of_sheared_line_roots
    {L : Type u} [Field L] [Infinite L]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (a : Fin 4 → L) (ha0 : a 0 ≠ 0)
    (x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L)
    (hinj : ∀ i j, Function.Injective (x i j))
    (hform : ∀ i j k, ∃ t : L, x i j k = t • a + lineDirection i j)
    (hzero : ∀ i j k, ∀ p ∈ I.toIdeal, p.eval (x i j k) = 0) :
    ∃ t : (Fin 2 × Fin 2 × Fin 3) → (Spec (.of L) ⟶ scheme I),
      (∀ u, t u ≫ toBase I =
        Spec.map (CommRingCat.ofHom (RingHom.id L))) ∧
      Function.Injective t := by
  let x₁₂ : (Fin 2 × Fin 2 × Fin 3) → Fin 4 → L :=
    fun u => x u.1 u.2.1 u.2.2
  apply exists_distinct_projective_scheme_points_of_vector_directions I x₁₂
  · rintro ⟨i, j, k⟩ p hp
    exact hzero i j k p hp
  · rintro ⟨i, j, k⟩
    obtain ⟨s, hs⟩ := hform i j k
    change x i j k ≠ 0
    rw [hs]
    intro h
    have hrep := shearedFourLines_unique_representation a ha0 i j s 1 (by simpa using h)
    exact one_ne_zero hrep.2
  · rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ hindex c
    exact shearedFourLines_twelve_roots_projectively_distinct
      a ha0 x hinj hform hindex c

private theorem shearedLinear_base_zero
    {L : Type u} [Field L] (a : Fin 4 → L) (ha0 : a 0 ≠ 0)
    (i : Fin 4) : (shearLinear a i).eval a = 0 := by
  rw [shearLinear_eval]
  simp [Pi.sub_apply, ha0]

private theorem shearedLinear_direction_eval
    {L : Type u} [Field L] (a : Fin 4 → L) (i j : Fin 2) (k : Fin 4) :
    (shearLinear a k).eval (lineDirection i j) = lineDirection i j k := by
  rw [shearLinear_eval]
  have hv0 : (lineDirection (L := L) i j) 0 = 0 := by
    fin_cases i <;> fin_cases j <;> simp [lineDirection, e]
  simp [Pi.sub_apply, hv0]

private theorem firstSheared_ne_zero
    {L : Type u} [Field L] (a : Fin 4 → L) (i : Fin 2) :
    firstSheared a i ≠ 0 := by
  intro h
  have heval : (firstSheared a i).eval (e (if i = 0 then 1 else 2)) = 1 := by
    fin_cases i <;> simp [firstSheared, shearLinear, e]
  simp [h] at heval

/-- The explicitly constructed split pair is a regular cubic--quadric--
quadric sequence. The cubic may be any nonzero homogeneous cubic over an
algebraically closed characteristic-zero field. -/
theorem exists_split_quadric_pair_regular_intersection
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0) :
    ∃ (q r : MvPolynomial (Fin 4) L)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 ∧ ∀ F : MvPolynomial (Fin 4) L,
        r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) L)) →
        F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) L)) := by
  obtain ⟨a, hpa, ha0⟩ := exists_cubic_nonzero_in_first_chart p hp hp0
  let l := firstSheared a
  let m := secondSheared a
  let q := l 0 * l 1
  let r := m 0 * m 1
  have hl : ∀ i, (l i).IsHomogeneous 1 := by
    intro i
    fin_cases i <;> simp [l, firstSheared, shearLinear_homogeneous]
  have hm : ∀ j, (m j).IsHomogeneous 1 := by
    intro j
    fin_cases j
    · exact shearLinear_homogeneous a 3
    · exact ((shearLinear_homogeneous a 1).add
        (shearLinear_homogeneous a 2)).add (shearLinear_homogeneous a 3)
  have hq : q.IsHomogeneous 2 := (hl 0).mul (hl 1)
  have hr : r.IsHomogeneous 2 := (hm 0).mul (hm 1)
  have hq0 : q ≠ 0 := mul_ne_zero
    (firstSheared_ne_zero a 0) (firstSheared_ne_zero a 1)
  refine ⟨q, r, hq, hr, hq0, ?_⟩
  obtain ⟨c, hc⟩ := homogeneous_cubic_has_tensor p hp
  apply cubic_two_quadric_regular_descends_from_four_nonzero_line_sections
    p q r hp hq hr
    c (by simpa only [Algebra.algebraMap_self, MvPolynomial.map_id] using hc)
    l m hl hm
    (by rw [Algebra.algebraMap_self, MvPolynomial.map_id])
    (by rw [Algebra.algebraMap_self, MvPolynomial.map_id])
    (fun _ _ => a) lineDirection
  · intro i j
    rw [← hc] at hpa
    change MvPolynomial.eval₂ (RingHom.id L) a c.toMvPolynomial ≠ 0 at hpa
    rwa [Cubic.eval_toMvPolynomial] at hpa
  · exact shearedFourLines_genuine a ha0
  · intro i j
    constructor
    · fin_cases i <;> simp [l, firstSheared, shearedLinear_base_zero a ha0]
    · fin_cases i <;> fin_cases j <;>
        simp [l, firstSheared, shearLinear, lineDirection, e]
  · intro i j
    constructor
    · fin_cases j <;>
        simp [m, secondSheared, shearedLinear_base_zero a ha0]
    · fin_cases i <;> fin_cases j <;>
        simp [m, secondSheared, shearLinear, lineDirection, e]
  · intro i j y hi hj
    exact shearedFourLines_span a y ha0 i j hi hj

/-- For a smooth cubic, the constructed first quadric is also relatively
prime to its defining cubic equation. -/
theorem exists_split_quadric_pair_regular_relprime_of_smooth
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (q r : MvPolynomial (Fin 4) L)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 ∧ IsRelPrime p q ∧
        ∀ F : MvPolynomial (Fin 4) L,
          r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) L)) →
          F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) L)) := by
  obtain ⟨q, r, hq, hr, hq0, hregular⟩ :=
    exists_split_quadric_pair_regular_intersection p hp hp0
  have hpprime : Prime p :=
    (Ideal.span_singleton_prime hp0).mp
      (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)
  have hrel : IsRelPrime p q :=
    isRelPrime_of_prime_homogeneous_degree_lt hp hq hpprime hq0 (by decide)
  exact ⟨q, r, hq, hr, hq0, hrel, hregular⟩

private theorem shearLinear_map
    {K L : Type u} [Field K] [Field L]
    (φ : K →+* L) (a : Fin 4 → K) (i : Fin 4) :
    (shearLinear a i).map φ =
      shearLinear (fun j => φ (a j)) i := by
  simp [shearLinear]

private theorem firstSheared_map
    {K L : Type u} [Field K] [Field L]
    (φ : K →+* L) (a : Fin 4 → K) (i : Fin 2) :
    (firstSheared a i).map φ =
      firstSheared (fun j => φ (a j)) i := by
  fin_cases i <;> simp [firstSheared, shearLinear_map]

private theorem secondSheared_map
    {K L : Type u} [Field K] [Field L]
    (φ : K →+* L) (a : Fin 4 → K) (i : Fin 2) :
    (secondSheared a i).map φ =
      secondSheared (fun j => φ (a j)) i := by
  fin_cases i <;> simp [secondSheared, shearLinear_map]

private theorem cubic_eval_ne_zero_of_polynomial_eval_ne_zero
    {L : Type u} [Field L]
    (c : Cubic L 4) (p : MvPolynomial (Fin 4) L)
    (y : Fin 4 → L) (hc : c.toMvPolynomial = p)
    (hp : p.eval y ≠ 0) : c.eval y ≠ 0 := by
  rw [← hc] at hp
  change MvPolynomial.eval₂ (RingHom.id L) y c.toMvPolynomial ≠ 0 at hp
  rwa [Cubic.eval_toMvPolynomial] at hp

/-- The two split quadrics have independent evaluations in two fixed
directions, even after the shear moves their common vertex. -/
private theorem sheared_split_quadric_pair_linearIndependent
    {K : Type u} [Field K] (a : Fin 4 → K) :
    LinearIndependent K ![
      firstSheared a 0 * firstSheared a 1,
      secondSheared a 0 * secondSheared a 1] := by
  let q := firstSheared a 0 * firstSheared a 1
  let r := secondSheared a 0 * secondSheared a 1
  let v := e (L := K) 1 + e 2
  let w := e (L := K) 3
  have hqv : q.eval v = 1 := by
    simp [q, v, firstSheared, shearLinear, e, Pi.single]
  have hrv : r.eval v = 0 := by
    simp [r, v, secondSheared, shearLinear, e, Pi.single]
  have hqw : q.eval w = 0 := by
    simp [q, w, firstSheared, shearLinear, e, Pi.single]
  have hrw : r.eval w = 1 := by
    simp [r, w, secondSheared, shearLinear, e, Pi.single]
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hcv := congrArg (MvPolynomial.eval v) hc
  have hcw := congrArg (MvPolynomial.eval w) hc
  have hc0 : c 0 = 0 := by
    simpa [q, r, hqv, hrv, Fin.sum_univ_succ] using hcv
  have hc1 : c 1 = 0 := by
    simpa [q, r, hqw, hrw, Fin.sum_univ_succ] using hcw
  intro i
  fin_cases i <;> assumption

/-- The explicit split pair is defined over the original field. Over any
characteristic-zero field, its regularity descends from the algebraic closure;
there is no need to choose the quadrics over that closure. -/
theorem exists_split_quadric_pair_regular_over_charZero_field
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0) :
    ∃ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 ∧ LinearIndependent K ![q, r] ∧
      ∀ F : MvPolynomial (Fin 4) K,
        r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  letI : Infinite K := CharZero.infinite K
  obtain ⟨a, hpa, ha0⟩ := exists_cubic_nonzero_in_first_chart p hp hp0
  let l := firstSheared a
  let m := secondSheared a
  let q := l 0 * l 1
  let r := m 0 * m 1
  have hl : ∀ i, (l i).IsHomogeneous 1 := by
    intro i
    fin_cases i <;> simp [l, firstSheared, shearLinear_homogeneous]
  have hm : ∀ j, (m j).IsHomogeneous 1 := by
    intro j
    fin_cases j
    · exact shearLinear_homogeneous a 3
    · exact ((shearLinear_homogeneous a 1).add
        (shearLinear_homogeneous a 2)).add (shearLinear_homogeneous a 3)
  have hq : q.IsHomogeneous 2 := (hl 0).mul (hl 1)
  have hr : r.IsHomogeneous 2 := (hm 0).mul (hm 1)
  have hq0 : q ≠ 0 := mul_ne_zero
    (firstSheared_ne_zero a 0) (firstSheared_ne_zero a 1)
  refine ⟨q, r, hq, hr, hq0,
    sheared_split_quadric_pair_linearIndependent a, ?_⟩
  let L := AlgebraicClosure K
  let φ : K →+* L := algebraMap K L
  let aL : Fin 4 → L := fun i => φ (a i)
  let lL := firstSheared aL
  let mL := secondSheared aL
  have ha0L : aL 0 ≠ 0 := by
    simpa only [aL, map_zero] using φ.injective.ne ha0
  have hpaL : (p.map φ).eval aL ≠ 0 := by
    have heval : (p.map φ).eval aL = φ (p.eval a) := by
      rw [MvPolynomial.eval_map]
      exact (MvPolynomial.eval₂_comp φ a p).symm
    rw [heval]
    simpa only [map_zero] using φ.injective.ne hpa
  have hlL : ∀ i, (lL i).IsHomogeneous 1 := by
    intro i
    fin_cases i <;> simp [lL, firstSheared, shearLinear_homogeneous]
  have hmL : ∀ j, (mL j).IsHomogeneous 1 := by
    intro j
    fin_cases j
    · exact shearLinear_homogeneous aL 3
    · exact ((shearLinear_homogeneous aL 1).add
        (shearLinear_homogeneous aL 2)).add (shearLinear_homogeneous aL 3)
  have hqfac : q.map φ = lL 0 * lL 1 := by
    change ((firstSheared a 0) * (firstSheared a 1)).map φ =
      firstSheared aL 0 * firstSheared aL 1
    rw [map_mul, firstSheared_map, firstSheared_map]
  have hrfac : r.map φ = mL 0 * mL 1 := by
    change ((secondSheared a 0) * (secondSheared a 1)).map φ =
      secondSheared aL 0 * secondSheared aL 1
    rw [map_mul, secondSheared_map, secondSheared_map]
  obtain ⟨c, hc⟩ := homogeneous_cubic_has_tensor (p.map φ) (hp.map φ)
  apply cubic_two_quadric_regular_descends_from_four_nonzero_line_sections
    p q r hp hq hr c hc lL mL hlL hmL hqfac hrfac
    (fun _ _ => aL) lineDirection
  · intro i j
    exact cubic_eval_ne_zero_of_polynomial_eval_ne_zero
      c (p.map φ) aL hc hpaL
  · exact shearedFourLines_genuine aL ha0L
  · intro i j
    constructor
    · fin_cases i <;> simp [lL, firstSheared, shearedLinear_base_zero aL ha0L]
    · fin_cases i <;> fin_cases j <;>
        simp [lL, firstSheared, shearLinear, lineDirection, e]
  · intro i j
    constructor
    · fin_cases j <;>
        simp [mL, secondSheared, shearedLinear_base_zero aL ha0L]
    · fin_cases i <;> fin_cases j <;>
        simp [mL, secondSheared, shearLinear, lineDirection, e]
  · intro i j y hi hj
    exact shearedFourLines_span aL y ha0L i j hi hj

/-- Smoothness makes the descended first quadric relatively prime to the
cubic, over the original characteristic-zero field. -/
theorem exists_split_quadric_pair_regular_relprime_over_charZero_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      q ≠ 0 ∧ LinearIndependent K ![q, r] ∧ IsRelPrime p q ∧
        ∀ F : MvPolynomial (Fin 4) K,
          r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  obtain ⟨q, r, hq, hr, hq0, hli, hregular⟩ :=
    exists_split_quadric_pair_regular_over_charZero_field p hp hp0
  have hpprime : Prime p :=
    (Ideal.span_singleton_prime hp0).mp
      (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)
  have hrel : IsRelPrime p q :=
    isRelPrime_of_prime_homogeneous_degree_lt hp hq hpprime hq0 (by decide)
  exact ⟨q, r, hq, hr, hq0, hli, hrel, hregular⟩

/-- The resulting projective cubic--quadric--quadric intersection is finite
over the original characteristic-zero ground field. -/
theorem exists_split_quadric_pair_finite_over_charZero_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2),
      IsFinite (toBase
        (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := by
  obtain ⟨q, r, hq, hr, hq0, _, hrel, hregular⟩ :=
    exists_split_quadric_pair_regular_relprime_over_charZero_of_smooth p hp hp0
  exact ⟨q, r, hq, hr,
    cubic_two_quadrics_intersection_finite
      p q r hp hq hr hp0 hq0 hrel hregular⟩

end PfaffianDescent
