import PfaffianDescent.VoisinEightVectorConfigurationPoint

/-!
# Normalized eight-point quadratic evaluation

Independent nonzero rescaling of the eight projective vector representatives
preserves the homogeneous quadratic kernel.  This lets the explicit
split-quadrics pencil be used in any common linear chart.
-/

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics

universe u

theorem homogeneous_eval_zero_iff_smul
    {K : Type u} [Field K]
    (s : MvPolynomial (Fin 4) K) {d : ℕ} (hs : s.IsHomogeneous d)
    (v : Fin 4 → K) (a : K) (ha : a ≠ 0) :
    s.aeval (a • v) = 0 ↔ s.aeval v = 0 := by
  change s.eval₂ (algebraMap K K) (a • v) = 0 ↔
    s.eval₂ (algebraMap K K) v = 0
  rw [eval₂_homogeneous_smul s hs]
  simp [pow_ne_zero _ ha]

/-- The homogeneous restriction kernel is invariant under rescaling each
vector by its own nonzero scalar. -/
theorem homogeneousSectionRestriction_kernel_eq_of_pointwise_smul
    {K : Type u} [Field K] {n d : ℕ}
    (y : Fin n → Fin 4 → K) (a : Fin n → K)
    (ha : ∀ i, a i ≠ 0) :
    LinearMap.ker (homogeneousSectionRestriction (K := K)
      (fun j i => (a i • y i) j : Fin 4 → Fin n → K) d) =
    LinearMap.ker (homogeneousSectionRestriction (K := K)
      (fun j i => y i j : Fin 4 → Fin n → K) d) := by
  ext s
  constructor
  · intro hs
    apply LinearMap.mem_ker.mpr
    apply _root_.funext
    intro i
    have hi := congrFun (LinearMap.mem_ker.mp hs) i
    have hi' : s.1.aeval (a i • y i) = 0 := by
      simpa only [homogeneousSectionRestriction_apply,
        finite_product_evaluation_apply, Pi.zero_apply] using hi
    have hz := (homogeneous_eval_zero_iff_smul s.1 s.2
      (y i) (a i) (ha i)).mp hi'
    simpa only [homogeneousSectionRestriction_apply,
      finite_product_evaluation_apply, Pi.zero_apply] using hz
  · intro hs
    apply LinearMap.mem_ker.mpr
    apply _root_.funext
    intro i
    have hi := congrFun (LinearMap.mem_ker.mp hs) i
    have hi' : s.1.aeval (y i) = 0 := by
      simpa only [homogeneousSectionRestriction_apply,
        finite_product_evaluation_apply, Pi.zero_apply] using hi
    have hz := (homogeneous_eval_zero_iff_smul s.1 s.2
      (y i) (a i) (ha i)).mpr hi'
    simpa only [homogeneousSectionRestriction_apply,
      finite_product_evaluation_apply, Pi.zero_apply] using hz

/-- Normalizing eight projective representatives in a common linear chart
preserves the kernel spanned by any independent pair of vanishing
quadrics. -/
theorem quadrics_span_normalized_eight_evaluation_kernel
    {L : Type u} [Field L]
    (y : Fin 8 → Fin 4 → L) (c : Fin 4 → L)
    (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0)
    (q r : MvPolynomial (Fin 4) L)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hlin : LinearIndependent L
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2), ⟨r, hr⟩])
    (hsurj : Function.Surjective (homogeneousSectionRestriction (K := L)
      (fun j i => y i j : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ i, q.eval (y i) = 0 ∧ r.eval (y i) = 0) :
    let x : Fin 4 → Fin 8 → L :=
      fun j i => normalizedVectorInLinearChart c (y i) j
    let Q : Fin 2 → homogeneousSubmodule (Fin 4) L 2 :=
      ![(⟨q, hq⟩), (⟨r, hr⟩)]
    Function.Surjective (homogeneousSectionRestriction (K := L) x 2) ∧
      LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) =
        Submodule.span L (Set.range Q) := by
  dsimp only
  let a : Fin 8 → L := fun i => ((homogeneousLinearForm c).eval (y i))⁻¹
  have ha : ∀ i, a i ≠ 0 := fun i => inv_ne_zero (hc i)
  have hker := homogeneousSectionRestriction_kernel_eq_of_pointwise_smul
    (d := 2) y a ha
  have hspan := quadrics_span_eight_evaluation_kernel
    y q r hq hr hlin hsurj hquad
  have hdimraw : Module.finrank L (LinearMap.ker
      (homogeneousSectionRestriction (K := L)
        (fun j i => y i j : Fin 4 → Fin 8 → L) 2)) = 2 :=
    quadric_degree_eight_vanishing_sections_finrank_eq_two_of_surjective
      (fun j i => y i j) (by simp) hsurj
  have hdim : Module.finrank L (LinearMap.ker
      (homogeneousSectionRestriction (K := L)
        (fun j i => normalizedVectorInLinearChart c (y i) j :
          Fin 4 → Fin 8 → L) 2)) = 2 := by
    simpa only [normalizedVectorInLinearChart] using hker ▸ hdimraw
  have hsurj' :=
    (quadric_degree_eight_restriction_surjective_iff_kernel_finrank_eq_two
      (fun j i => normalizedVectorInLinearChart c (y i) j)
      (by simp)).mpr hdim
  refine ⟨hsurj', ?_⟩
  simpa only [normalizedVectorInLinearChart] using hker.trans hspan

/-- In any common nonvanishing linear chart, the normalized eight roots
still impose independent quadratic conditions, and their full vanishing
pencil is the span of the two split quadrics. -/
theorem split_quadrics_span_normalized_eight_evaluation_kernel
    {L : Type u} [Field L]
    (y : Fin 8 → Fin 4 → L) (c : Fin 4 → L)
    (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0)
    (hsurj : Function.Surjective (homogeneousSectionRestriction (K := L)
      (fun j i => y i j : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ i,
      (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (y i) = 0 ∧
      (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval (y i) = 0) :
    let x : Fin 4 → Fin 8 → L :=
      fun j i => normalizedVectorInLinearChart c (y i) j
    let Q : Fin 2 → homogeneousSubmodule (Fin 4) L 2 :=
      ![(⟨(X 1 * X 2 : MvPolynomial (Fin 4) L),
        (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)⟩),
        (⟨(X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L),
          (isHomogeneous_X L 3).mul
            (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
              (isHomogeneous_X L 3))⟩)]
    Function.Surjective (homogeneousSectionRestriction (K := L) x 2) ∧
      LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) =
        Submodule.span L (Set.range Q) := by
  dsimp only
  let a : Fin 8 → L := fun i => ((homogeneousLinearForm c).eval (y i))⁻¹
  have ha : ∀ i, a i ≠ 0 := fun i => inv_ne_zero (hc i)
  have hker := homogeneousSectionRestriction_kernel_eq_of_pointwise_smul
    (d := 2) y a ha
  have hspan := split_quadrics_span_eight_evaluation_kernel y hsurj hquad
  have hdimraw : Module.finrank L (LinearMap.ker
      (homogeneousSectionRestriction (K := L)
        (fun j i => y i j : Fin 4 → Fin 8 → L) 2)) = 2 :=
    quadric_degree_eight_vanishing_sections_finrank_eq_two_of_surjective
      (fun j i => y i j) (by simp) hsurj
  have hdim : Module.finrank L (LinearMap.ker
      (homogeneousSectionRestriction (K := L)
        (fun j i => normalizedVectorInLinearChart c (y i) j :
          Fin 4 → Fin 8 → L) 2)) = 2 := by
    simpa only [normalizedVectorInLinearChart] using hker ▸ hdimraw
  have hsurj' :=
    (quadric_degree_eight_restriction_surjective_iff_kernel_finrank_eq_two
      (fun j i => normalizedVectorInLinearChart c (y i) j)
      (by simp)).mpr hdim
  refine ⟨hsurj', ?_⟩
  simpa only [normalizedVectorInLinearChart] using hker.trans hspan

/-- An algebra equivalence with a product of fields identifies restriction
to a finite coordinate algebra with simultaneous evaluation at its labels. -/
theorem homogeneousSectionRestriction_algEquiv_pi_apply
    {L A : Type u} [Field L] [CommRing A] [Algebra L A]
    [FiniteDimensional L A] {n d : ℕ}
    (e : A ≃ₐ[L] (Fin n → L)) (x : Fin 4 → A)
    (s : homogeneousSubmodule (Fin 4) L d) (i : Fin n) :
    e (homogeneousSectionRestriction (K := L) x d s) i =
      (homogeneousSectionRestriction (K := L)
        (fun j k => e (x j) k : Fin 4 → Fin n → L) d s) i := by
  let f : A →+* L := (Pi.evalRingHom (fun _ : Fin n => L) i).comp e.toRingHom
  have hf : f.comp (algebraMap L A) = algebraMap L L := by
    ext a
    change e (algebraMap L A a) i = a
    rw [e.commutes]
    rfl
  have h := MvPolynomial.hom_eval₂ s.1 (algebraMap L A) f x
  change f (s.1.eval₂ (algebraMap L A) x) = _
  rw [h, hf]
  exact (finite_product_evaluation_apply
    (fun k j => e (x j) k) s.1 i).symm

/-- Polynomial evaluation in a split finite algebra is evaluated separately
at each of its field-valued labels. -/
theorem polynomial_eval_algEquiv_pi_apply
    {L A : Type u} [Field L] [CommRing A] [Algebra L A]
    (e : A ≃ₐ[L] (Fin 8 → L)) (x : Fin 4 → A)
    (s : MvPolynomial (Fin 4) L) (i : Fin 8) :
    e (s.eval₂ (algebraMap L A) x) i =
      s.aeval (fun j => e (x j) i) := by
  let f : A →+* L := (Pi.evalRingHom (fun _ : Fin 8 => L) i).comp e.toRingHom
  have hf : f.comp (algebraMap L A) = algebraMap L L := by
    ext a
    change e (algebraMap L A a) i = a
    rw [e.commutes]
    rfl
  have h := MvPolynomial.hom_eval₂ s (algebraMap L A) f x
  change f (s.eval₂ (algebraMap L A) x) = _
  rw [h, hf]
  rfl

/-- The inverse images of normalized labeled vectors lie in the common
linear chart of the split finite algebra. -/
theorem normalized_eight_coordinates_linear_form_eq_one
    {L A : Type u} [Field L] [CommRing A] [Algebra L A]
    (e : A ≃ₐ[L] (Fin 8 → L))
    (y : Fin 8 → Fin 4 → L) (c : Fin 4 → L)
    (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0) :
    let x : Fin 4 → A := fun j =>
      e.symm (fun i => normalizedVectorInLinearChart c (y i) j)
    (homogeneousLinearForm c).eval₂ (algebraMap L A) x = 1 := by
  dsimp only
  apply e.injective
  apply _root_.funext
  intro i
  rw [polynomial_eval_algEquiv_pi_apply, map_one]
  simpa only [AlgEquiv.apply_symm_apply, Pi.one_apply,
    MvPolynomial.aeval_eq_eval] using
    normalizedVectorInLinearChart_eval_one c (y i) (hc i)

/-- If all labeled vectors lie on a homogeneous cubic, their normalized
coordinates in the split finite algebra satisfy the same cubic equation. -/
theorem normalized_eight_coordinates_cubic_eq_zero
    {L A : Type u} [Field L] [CommRing A] [Algebra L A]
    (e : A ≃ₐ[L] (Fin 8 → L))
    (y : Fin 8 → Fin 4 → L) (c : Fin 4 → L)
    (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0)
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3)
    (hzero : ∀ i, p.eval (y i) = 0) :
    let x : Fin 4 → A := fun j =>
      e.symm (fun i => normalizedVectorInLinearChart c (y i) j)
    p.eval₂ (algebraMap L A) x = 0 := by
  dsimp only
  apply e.injective
  apply _root_.funext
  intro i
  rw [polynomial_eval_algEquiv_pi_apply, map_zero]
  have hi := (homogeneous_eval_zero_iff_smul p hp (y i)
    ((homogeneousLinearForm c).eval (y i))⁻¹
    (inv_ne_zero (hc i))).mpr (by simpa using hzero i)
  simpa only [normalizedVectorInLinearChart, AlgEquiv.apply_symm_apply,
    Pi.zero_apply] using hi

/-- Surjectivity of one homogeneous restriction map already says the
coordinate tuple generates the whole finite algebra as a polynomial algebra. -/
theorem polynomial_evaluation_surjective_of_homogeneous_restriction_surjective
    {L A : Type u} [Field L] [CommRing A] [Algebra L A]
    [FiniteDimensional L A] (x : Fin 4 → A) (d : ℕ)
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := L) x d)) :
    Function.Surjective (eval₂Hom (algebraMap L A) x) := by
  intro a
  obtain ⟨s, hs⟩ := hsurj a
  exact ⟨s.1, hs⟩

/-- Surjectivity of quadratic restriction can be checked after splitting the
finite algebra into its labeled field factors. -/
theorem homogeneousSectionRestriction_surjective_iff_algEquiv_pi
    {L A : Type u} [Field L] [CommRing A] [Algebra L A]
    [FiniteDimensional L A] {n d : ℕ}
    (e : A ≃ₐ[L] (Fin n → L)) (x : Fin 4 → A) :
    Function.Surjective (homogeneousSectionRestriction (K := L) x d) ↔
      Function.Surjective (homogeneousSectionRestriction (K := L)
        (fun j k => e (x j) k : Fin 4 → Fin n → L) d) := by
  constructor
  · intro h b
    obtain ⟨s, hs⟩ := h (e.symm b)
    refine ⟨s, ?_⟩
    apply _root_.funext
    intro i
    rw [← homogeneousSectionRestriction_algEquiv_pi_apply e x s i, hs]
    exact congrFun (e.apply_symm_apply b) i
  · intro h b
    obtain ⟨s, hs⟩ := h (e b)
    refine ⟨s, e.injective ?_⟩
    apply _root_.funext
    intro i
    rw [homogeneousSectionRestriction_algEquiv_pi_apply e x s i]
    exact congrFun hs i

/-- Splitting the finite algebra preserves the entire homogeneous
restriction kernel, not only its dimension. -/
theorem homogeneousSectionRestriction_ker_eq_algEquiv_pi
    {L A : Type u} [Field L] [CommRing A] [Algebra L A]
    [FiniteDimensional L A] {n d : ℕ}
    (e : A ≃ₐ[L] (Fin n → L)) (x : Fin 4 → A) :
    LinearMap.ker (homogeneousSectionRestriction (K := L) x d) =
      LinearMap.ker (homogeneousSectionRestriction (K := L)
        (fun j k => e (x j) k : Fin 4 → Fin n → L) d) := by
  ext s
  constructor
  · intro hs
    apply LinearMap.mem_ker.mpr
    apply _root_.funext
    intro i
    rw [← homogeneousSectionRestriction_algEquiv_pi_apply e x s i,
      LinearMap.mem_ker.mp hs, map_zero]
  · intro hs
    apply LinearMap.mem_ker.mpr
    apply e.injective
    apply _root_.funext
    intro i
    rw [homogeneousSectionRestriction_algEquiv_pi_apply e x s i,
      LinearMap.mem_ker.mp hs]
    simp

/-- The explicit split pencil can be realized inside any finite algebra
identified with the eight labeled points.  The coordinates are the inverse
images of the normalized pointwise coordinates. -/
theorem split_quadrics_span_finite_algebra_eight_evaluation_kernel
    {L A : Type u} [Field L] [CommRing A] [Algebra L A]
    [FiniteDimensional L A]
    (e : A ≃ₐ[L] (Fin 8 → L))
    (y : Fin 8 → Fin 4 → L) (c : Fin 4 → L)
    (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0)
    (hsurj : Function.Surjective (homogeneousSectionRestriction (K := L)
      (fun j i => y i j : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ i,
      (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (y i) = 0 ∧
      (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval (y i) = 0) :
    let x : Fin 4 → A := fun j =>
      e.symm (fun i => normalizedVectorInLinearChart c (y i) j)
    let Q : Fin 2 → homogeneousSubmodule (Fin 4) L 2 :=
      ![(⟨(X 1 * X 2 : MvPolynomial (Fin 4) L),
        (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)⟩),
        (⟨(X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L),
          (isHomogeneous_X L 3).mul
            (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
              (isHomogeneous_X L 3))⟩)]
    Function.Surjective (homogeneousSectionRestriction (K := L) x 2) ∧
      LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) =
        Submodule.span L (Set.range Q) := by
  dsimp only
  let x : Fin 4 → A := fun j =>
    e.symm (fun i => normalizedVectorInLinearChart c (y i) j)
  have hx : (fun j k => e (x j) k : Fin 4 → Fin 8 → L) =
      (fun j i => normalizedVectorInLinearChart c (y i) j) := by
    funext j i
    exact congrFun (e.apply_symm_apply _) i
  obtain ⟨hs, hk⟩ :=
    split_quadrics_span_normalized_eight_evaluation_kernel y c hc hsurj hquad
  constructor
  · exact (homogeneousSectionRestriction_surjective_iff_algEquiv_pi e x).mpr
      (hx ▸ hs)
  · exact (homogeneousSectionRestriction_ker_eq_algEquiv_pi e x).trans
      (hx ▸ hk)

/-- The arbitrary-pair version of the finite coordinate-algebra kernel
identification. -/
theorem quadrics_span_finite_algebra_eight_evaluation_kernel
    {L A : Type u} [Field L] [CommRing A] [Algebra L A]
    [FiniteDimensional L A]
    (e : A ≃ₐ[L] (Fin 8 → L))
    (y : Fin 8 → Fin 4 → L) (c : Fin 4 → L)
    (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0)
    (q r : MvPolynomial (Fin 4) L)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hlin : LinearIndependent L
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2), ⟨r, hr⟩])
    (hsurj : Function.Surjective (homogeneousSectionRestriction (K := L)
      (fun j i => y i j : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ i, q.eval (y i) = 0 ∧ r.eval (y i) = 0) :
    let x : Fin 4 → A := fun j =>
      e.symm (fun i => normalizedVectorInLinearChart c (y i) j)
    let Q : Fin 2 → homogeneousSubmodule (Fin 4) L 2 :=
      ![(⟨q, hq⟩), (⟨r, hr⟩)]
    Function.Surjective (homogeneousSectionRestriction (K := L) x 2) ∧
      LinearMap.ker (homogeneousSectionRestriction (K := L) x 2) =
        Submodule.span L (Set.range Q) := by
  dsimp only
  let x : Fin 4 → A := fun j =>
    e.symm (fun i => normalizedVectorInLinearChart c (y i) j)
  have hx : (fun j k => e (x j) k : Fin 4 → Fin 8 → L) =
      (fun j i => normalizedVectorInLinearChart c (y i) j) := by
    funext j i
    exact congrFun (e.apply_symm_apply _) i
  obtain ⟨hs, hk⟩ := quadrics_span_normalized_eight_evaluation_kernel
    y c hc q r hq hr hlin hsurj hquad
  constructor
  · exact (homogeneousSectionRestriction_surjective_iff_algEquiv_pi e x).mpr
      (hx ▸ hs)
  · exact (homogeneousSectionRestriction_ker_eq_algEquiv_pi e x).trans
      (hx ▸ hk)

end PfaffianDescent
