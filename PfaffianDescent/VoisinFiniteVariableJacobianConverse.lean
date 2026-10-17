import PfaffianDescent.VoisinPrincipalJacobianConverse

/-!
# Principal Jacobian converse for any finite variable set

The normalized cubic chart is a principal quotient of a polynomial algebra
in the three remaining variables. These finite-variable lemmas adapt the
square-zero Taylor and conormal cancellation proof to that presentation.
-/

namespace PfaffianDescent

open MvPolynomial

universe u v w
variable {K : Type u} [Field K]
variable {σ : Type v} [Fintype σ]

private noncomputable def finiteFirstOrderTerm
    {A : Type w} [CommRing A]
    (f : K →+* A) (x y : σ → A) (p : MvPolynomial σ K) : A :=
  ∑ i : σ, y i * (pderiv i p).eval₂ f x

private lemma finiteFirstOrderTerm_C
    {A : Type w} [CommRing A]
    (f : K →+* A) (x y : σ → A) (a : K) :
    finiteFirstOrderTerm f x y (C a) = 0 := by
  simp [finiteFirstOrderTerm]

private lemma finiteFirstOrderTerm_add
    {A : Type w} [CommRing A]
    (f : K →+* A) (x y : σ → A) (p q : MvPolynomial σ K) :
    finiteFirstOrderTerm f x y (p + q) =
      finiteFirstOrderTerm f x y p + finiteFirstOrderTerm f x y q := by
  simp [finiteFirstOrderTerm, mul_add, Finset.sum_add_distrib]

private lemma finiteFirstOrderTerm_X
    {A : Type w} [CommRing A]
    (f : K →+* A) (x y : σ → A) (n : σ) :
    finiteFirstOrderTerm f x y (X n) = y n := by
  classical
  unfold finiteFirstOrderTerm
  rw [Finset.sum_eq_single n]
  · simp
  · intro i _ hi
    simp [pderiv_X_of_ne hi.symm]
  · simp

private lemma finiteFirstOrderTerm_mul
    {A : Type w} [CommRing A]
    (f : K →+* A) (x y : σ → A) (p q : MvPolynomial σ K) :
    finiteFirstOrderTerm f x y (p * q) =
      finiteFirstOrderTerm f x y p * q.eval₂ f x +
        p.eval₂ f x * finiteFirstOrderTerm f x y q := by
  simp only [finiteFirstOrderTerm, pderiv_mul, eval₂_add, eval₂_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

private lemma finiteFirstOrderTerm_mem
    {A : Type w} [CommRing A]
    (f : K →+* A) (x y : σ → A)
    (J : Ideal A) (hy : ∀ i, y i ∈ J) (p : MvPolynomial σ K) :
    finiteFirstOrderTerm f x y p ∈ J := by
  unfold finiteFirstOrderTerm
  exact Submodule.sum_mem J (fun i hi => J.mul_mem_right _ (hy i))

/-- Characteristic-free Taylor expansion in an arbitrary finite set of
variables, for coordinate increments in a square-zero ideal. -/
theorem finiteMvPolynomial_eval₂_add_of_squareZero
    {A : Type w} [CommRing A]
    (f : K →+* A) (x y : σ → A)
    (J : Ideal A) (hy : ∀ i, y i ∈ J) (hJ : J ^ 2 = ⊥)
    (p : MvPolynomial σ K) :
    p.eval₂ f (fun i => x i + y i) =
      p.eval₂ f x + ∑ i : σ, y i * (pderiv i p).eval₂ f x := by
  have hmul {a b : A} (ha : a ∈ J) (hb : b ∈ J) : a * b = 0 := by
    have h : a * b ∈ J ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul ha hb
    simpa [hJ] using h
  change p.eval₂ f (fun i => x i + y i) =
    p.eval₂ f x + finiteFirstOrderTerm f x y p
  induction p using MvPolynomial.induction_on with
  | C a => simp [finiteFirstOrderTerm_C]
  | add p q hp hq =>
      simp only [eval₂_add, finiteFirstOrderTerm_add, hp, hq]
      ring
  | mul_X p n hp =>
      have hz : finiteFirstOrderTerm f x y p * y n = 0 :=
        hmul (finiteFirstOrderTerm_mem f x y J hy p) (hy n)
      rw [eval₂_mul, eval₂_X, hp, finiteFirstOrderTerm_mul,
        finiteFirstOrderTerm_X, eval₂_X]
      simp only [eval₂_mul, eval₂_X, mul_add, add_mul, hz, add_zero]
      ring

/-- The first-order difference of two polynomial algebra homomorphisms,
with an arbitrary finite variable type. -/
theorem finiteMvPolynomial_algHom_difference_of_squareZero
    {A : Type w} [CommRing A] [Algebra K A]
    (u v : MvPolynomial σ K →ₐ[K] A)
    (J : Ideal A) (hJ : J ^ 2 = ⊥)
    (hvars : ∀ i : σ, v (X i) - u (X i) ∈ J)
    (p : MvPolynomial σ K) :
    v p = u p + ∑ i : σ,
      (v (X i) - u (X i)) * u (pderiv i p) := by
  let x : σ → A := fun i => u (X i)
  let y : σ → A := fun i => v (X i) - u (X i)
  have hy : ∀ i, y i ∈ J := hvars
  have hxy : ∀ i, x i + y i = v (X i) := by
    intro i
    simp [x, y]
  have hu : u = MvPolynomial.aeval x := by
    simpa [x, Function.comp_def] using (MvPolynomial.aeval_unique u)
  have hv : v = MvPolynomial.aeval (fun i => x i + y i) := by
    rw [MvPolynomial.aeval_unique v]
    congr 1
    funext i
    exact (hxy i).symm
  calc
    v p = p.eval₂ (algebraMap K A) (fun i => x i + y i) := by
      rw [hv]
      rfl
    _ = p.eval₂ (algebraMap K A) x +
        ∑ i : σ, y i * (pderiv i p).eval₂ (algebraMap K A) x :=
      finiteMvPolynomial_eval₂_add_of_squareZero (algebraMap K A) x y J hy hJ p
    _ = u p + ∑ i : σ,
        (v (X i) - u (X i)) * u (pderiv i p) := by
      rw [hu]
      change (MvPolynomial.aeval x) p +
          ∑ i : σ, y i * (MvPolynomial.aeval x) (pderiv i p) =
        (MvPolynomial.aeval x) p +
          ∑ i : σ, (v (X i) - (MvPolynomial.aeval x) (X i)) *
            (MvPolynomial.aeval x) (pderiv i p)
      simp only [MvPolynomial.aeval_X]
      rfl

/-- A section of the square-zero thickening gives a Taylor relation
for a defining polynomial in the kernel of any finite-variable
polynomial presentation. -/
theorem finiteMvPolynomial_kerSquareLift_section_relation_of_mem
    {A : Type w} [CommRing A] [Algebra K A]
    (f : MvPolynomial σ K →ₐ[K] A)
    (g : A →ₐ[K] MvPolynomial σ K ⧸ RingHom.ker f.toRingHom ^ 2)
    (hg : f.kerSquareLift.comp g = AlgHom.id K A)
    (p : MvPolynomial σ K)
    (hp : p ∈ RingHom.ker f.toRingHom) :
    Ideal.Quotient.mk (RingHom.ker f.toRingHom ^ 2) p +
      ∑ i : σ,
        (g (f (X i)) -
          Ideal.Quotient.mk (RingHom.ker f.toRingHom ^ 2) (X i)) *
          Ideal.Quotient.mk (RingHom.ker f.toRingHom ^ 2) (pderiv i p) = 0 := by
  let I : Ideal (MvPolynomial σ K) := RingHom.ker f.toRingHom
  let u : MvPolynomial σ K →ₐ[K] MvPolynomial σ K ⧸ I ^ 2 :=
    Ideal.Quotient.mkₐ K (I ^ 2)
  let v : MvPolynomial σ K →ₐ[K] MvPolynomial σ K ⧸ I ^ 2 := g.comp f
  let J : Ideal (MvPolynomial σ K ⧸ I ^ 2) :=
    RingHom.ker f.kerSquareLift.toRingHom
  have hJ : J ^ 2 = ⊥ := by
    change (RingHom.ker f.kerSquareLift.toRingHom) ^ 2 = ⊥
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  have hsec (a : A) : f.kerSquareLift (g a) = a := by
    have h := DFunLike.congr_fun hg a
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using h
  have hu (i : σ) : f.kerSquareLift (u (X i)) = f (X i) := by
    change f.kerSquareLift (Ideal.Quotient.mk (I ^ 2) (X i)) = f (X i)
    exact f.kerSquareLift_mk (X i)
  have hvars : ∀ i : σ, v (X i) - u (X i) ∈ J := by
    intro i
    apply RingHom.mem_ker.mpr
    change f.kerSquareLift (g (f (X i)) - u (X i)) = 0
    rw [map_sub, hsec, hu]
    exact sub_self _
  have h := finiteMvPolynomial_algHom_difference_of_squareZero
    u v J hJ hvars p
  have hzero : f p = 0 := RingHom.mem_ker.mp hp
  simpa only [u, v, Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply,
    hzero, map_zero] using h.symm

private theorem finitePrincipal_cancel_mod_square
    (F z : MvPolynomial σ K) (hF : F ≠ 0)
    (h : F * z ∈ (Ideal.span ({F} : Set (MvPolynomial σ K))) ^ 2) :
    z ∈ Ideal.span ({F} : Set (MvPolynomial σ K)) := by
  rw [Ideal.span_singleton_pow] at h
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp h
  apply Ideal.mem_span_singleton.mpr
  refine ⟨w, ?_⟩
  apply mul_left_cancel₀ hF
  calc
    F * z = F ^ 2 * w := hw
    _ = F * (F * w) := by ring

/-- A formally smooth polynomial algebra quotient by one nonzero equation
has a Jacobian unit-ideal certificate, for any finite variable type. -/
theorem formallySmooth_finitePrincipalPresentation_jacobian_top
    {A : Type w} [CommRing A] [Algebra K A]
    (f : MvPolynomial σ K →ₐ[K] A)
    (hf : Function.Surjective f)
    (F : MvPolynomial σ K) (hF : F ≠ 0)
    (hker : RingHom.ker f.toRingHom =
      Ideal.span ({F} : Set (MvPolynomial σ K)))
    [Algebra.FormallySmooth K A] :
    Ideal.span (Set.range (fun i : σ => f (pderiv i F))) = ⊤ := by
  classical
  let I : Ideal (MvPolynomial σ K) := RingHom.ker f.toRingHom
  let Q : MvPolynomial σ K →+* MvPolynomial σ K ⧸ I ^ 2 :=
    Ideal.Quotient.mk (I ^ 2)
  obtain ⟨g, hg⟩ := (Algebra.FormallySmooth.iff_split_surjection f hf).mp
    (inferInstance : Algebra.FormallySmooth K A)
  have hsec (a : A) : f.kerSquareLift (g a) = a := by
    have h := DFunLike.congr_fun hg a
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using h
  have hrep (i : σ) :
      ∃ c : MvPolynomial σ K,
        g (f (X i)) - Q (X i) = Q (F * c) := by
    have hy : g (f (X i)) - Q (X i) ∈
        RingHom.ker f.kerSquareLift.toRingHom := by
      apply RingHom.mem_ker.mpr
      change f.kerSquareLift (g (f (X i)) - Q (X i)) = 0
      rw [map_sub, hsec]
      have hQ : f.kerSquareLift (Q (X i)) = f (X i) :=
        f.kerSquareLift_mk (X i)
      rw [hQ, sub_self]
    have hy' : g (f (X i)) - Q (X i) ∈ I.cotangentIdeal := by
      simpa only [I, AlgHom.ker_kerSquareLift] using hy
    obtain ⟨a, ha, hae⟩ := hy'
    change a ∈ I at ha
    have haF : a ∈ Ideal.span ({F} : Set (MvPolynomial σ K)) := by
      simpa only [I, hker] using ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp haF
    refine ⟨c, ?_⟩
    change Q a = g (f (X i)) - Q (X i) at hae
    rw [hc] at hae
    exact hae.symm
  choose c hc using hrep
  have hFker : F ∈ RingHom.ker f.toRingHom :=
    hker.symm ▸ Ideal.mem_span_singleton_self F
  have hrel := finiteMvPolynomial_kerSquareLift_section_relation_of_mem
    f g hg F hFker
  have hrel' : Q F + ∑ i : σ,
      Q (F * c i) * Q (pderiv i F) = 0 := by
    change Q F + ∑ i : σ,
      (g (f (X i)) - Q (X i)) * Q (pderiv i F) = 0 at hrel
    simpa only [hc] using hrel
  let z : MvPolynomial σ K := 1 + ∑ i : σ, c i * pderiv i F
  have hQ : Q (F * z) = 0 := by
    calc
      Q (F * z) = Q F + ∑ i : σ,
          Q (F * c i) * Q (pderiv i F) := by
        simp only [z, map_mul, map_add, map_sum,
          mul_add, mul_one, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := hrel'
  have hsq : F * z ∈
      (Ideal.span ({F} : Set (MvPolynomial σ K))) ^ 2 := by
    have hmem : F * z ∈ I ^ 2 := Ideal.Quotient.eq_zero_iff_mem.mp hQ
    simpa only [I, hker] using hmem
  have hz : z ∈ Ideal.span ({F} : Set (MvPolynomial σ K)) :=
    finitePrincipal_cancel_mod_square F z hF hsq
  have hfz : f z = 0 := RingHom.mem_ker.mp (hker.symm ▸ hz)
  let L : Ideal A := Ideal.span (Set.range (fun i : σ => f (pderiv i F)))
  have hsum_mem : (∑ i : σ, f (c i) * f (pderiv i F)) ∈ L := by
    apply Submodule.sum_mem
    intro i _
    exact L.mul_mem_left _ (Ideal.subset_span ⟨i, rfl⟩)
  have hzero : (1 : A) + ∑ i : σ, f (c i) * f (pderiv i F) = 0 := by
    simpa only [z, map_add, map_one, map_sum, map_mul] using hfz
  have h1 : (1 : A) ∈ L := by
    have heq : (1 : A) = -∑ i : σ, f (c i) * f (pderiv i F) := by
      exact eq_neg_of_add_eq_zero_left hzero
    rw [heq]
    exact L.neg_mem hsum_mem
  exact (Ideal.eq_top_iff_one L).mpr h1

end PfaffianDescent
