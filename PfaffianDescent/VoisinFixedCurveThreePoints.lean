import PfaffianDescent.VoisinDegreeEightFixedCurveScheme
import PfaffianDescent.VoisinDegreeEightFixedCurveSections
import PfaffianDescent.VoisinGenericSixteenFixedCurveCubicSections

/-! # Hyperplane sections of projective prime curves -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneousPrime_exists_minimal_linear_section
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCprime : C.toIdeal.IsPrime) (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1) :
    ∃ P : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K),
      P.toIdeal.IsPrime ∧ C ≤ P ∧ ell ∈ P.toIdeal ∧
      P.toIdeal ∈ (C.toIdeal ⊔ Ideal.span ({ell} : Set _)).minimalPrimes := by
  let D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    ⟨Ideal.span ({ell} : Set (MvPolynomial (Fin 4) K)),
      Ideal.homogeneous_span _ _ (by
        intro f hf
        simp only [Set.mem_singleton_iff] at hf
        subst f
        exact SetLike.isHomogeneousElem_coe ⟨ell, hell⟩)⟩
  let J := C ⊔ D
  have hJle : J ≤ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) := by
    apply sup_le
    · exact homogeneousIdeal_le_irrelevant_of_ne_top C hCprime.ne_top
    · intro f hf
      change f ∈ Ideal.span ({ell} : Set (MvPolynomial (Fin 4) K)) at hf
      refine Ideal.span_le.mpr ?_ hf
      rintro _ rfl
      exact HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < 1)
        (hell)
  have hJproper : J.toIdeal ≠ ⊤ := by
    apply ne_top_of_le_ne_top (RingHom.ker_ne_top
      (GradedRing.projZeroRingHom
        (MvPolynomial.homogeneousSubmodule (Fin 4) K)))
    exact (show J.toIdeal ≤
      (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin 4) K)).toIdeal from hJle)
  obtain ⟨P₀, hP₀⟩ := Ideal.nonempty_minimalPrimes hJproper
  let P := P₀.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  have hJP : J ≤ P := by
    exact (Ideal.homogeneousCore.gc _ J P₀).mp hP₀.1.2
  have hPcore : P.toIdeal = P₀ := by
    apply le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
    exact hP₀.2 ⟨hP₀.isPrime.homogeneousCore,
      show J.toIdeal ≤ P.toIdeal from hJP⟩
      (Ideal.toIdeal_homogeneousCore_le _ _)
  refine ⟨P, hP₀.isPrime.homogeneousCore, ?_, ?_, ?_⟩
  · exact le_trans le_sup_left hJP
  · exact (le_trans le_sup_right hJP)
      (Ideal.subset_span (Set.mem_singleton _))
  · simpa [J, D, hPcore] using hP₀


theorem homogeneousPrime_exists_relevant_linear_section
    {K : Type u} [Field K] [Infinite K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCprime : C.toIdeal.IsPrime) (hCheight : C.toIdeal.height = 2)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (j : Fin 4) (x : Fin 4 → K) (hxj : x j = 1)
    (hzero : ∀ f ∈ C.toIdeal, f.eval₂ (algebraMap K K) x = 0) :
    ∃ P : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K),
      P.toIdeal.IsPrime ∧ C ≤ P ∧ ell ∈ P.toIdeal ∧
      (¬ HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ P) ∧
      P.toIdeal ∈ (C.toIdeal ⊔ Ideal.span ({ell} : Set _)).minimalPrimes := by
  obtain ⟨P, hPprime, hCP, hEll, hPminimal⟩ :=
    homogeneousPrime_exists_minimal_linear_section C hCprime ell hell
  refine ⟨P, hPprime, hCP, hEll, ?_, hPminimal⟩
  intro hirrP
  let Q := algebraVectorHomogeneousIdeal (K := K) x
  have hx0 : x ≠ 0 := by
    intro hx
    have := congrFun hx j
    simp [hxj] at this
  have hCQ : C ≤ Q :=
    homogeneousIdeal_le_algebraVectorHomogeneousIdeal_of_forall_eval_zero C x hzero
  have hQheight : (3 : ℕ∞) ≤ Q.toIdeal.height := by
    change (3 : ℕ∞) ≤ (vectorLineIdeal x).toIdeal.height
    exact three_le_height_vectorLineIdeal_of_eq_one x j hxj
  have hCQne : C ≠ Q := by
    intro h
    have hbad : (3 : ℕ∞) ≤ 2 := by
      rw [← hCheight, h]
      exact hQheight
    norm_num at hbad
  have hCQlt : C < Q := lt_of_le_of_ne hCQ hCQne
  have hQirr : Q < HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    algebraVectorHomogeneousIdeal_lt_irrelevant_of_ne_zero x hx0
  have hPirrel : P ≤ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    homogeneousIdeal_le_irrelevant_of_ne_top P hPprime.ne_top
  have hPeq : P = HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    le_antisymm hPirrel hirrP
  have hQP : Q < P := by simpa [hPeq] using hQirr
  let f := Ideal.Quotient.mk C.toIdeal
  have hkerC : RingHom.ker f ≤ C.toIdeal := by
    simpa only [f, Ideal.mk_ker] using (le_refl C.toIdeal)
  have hmapCQ : C.toIdeal.map f < Q.toIdeal.map f :=
    ideal_map_lt_map_of_surjective_of_ker_le f
      Ideal.Quotient.mk_surjective hkerC hCQlt
  have hmapQP : Q.toIdeal.map f < P.toIdeal.map f :=
    ideal_map_lt_map_of_surjective_of_ker_le f
      Ideal.Quotient.mk_surjective (hkerC.trans hCQ) hQP
  letI : C.toIdeal.IsPrime := hCprime
  letI : Q.toIdeal.IsPrime := by
    change (vectorLineIdeal x).toIdeal.IsPrime
    infer_instance
  letI : P.toIdeal.IsPrime := hPprime
  letI : (C.toIdeal.map f).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkerC
  letI : (Q.toIdeal.map f).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hkerC.trans hCQ)
  letI : (P.toIdeal.map f).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hkerC.trans hCP)
  have hQone : (1 : ℕ∞) ≤ (Q.toIdeal.map f).height := by
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hmapCQ
    simpa [f, Ideal.map_quotient_self, Ideal.height_bot] using h
  have hPtwo : (2 : ℕ∞) ≤ (P.toIdeal.map f).height := by
    calc
      (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ (Q.toIdeal.map f).height + 1 := by
        simpa [add_comm] using add_le_add_left hQone 1
      _ ≤ (P.toIdeal.map f).height :=
        Ideal.height_add_one_le_of_lt_of_isPrime hmapQP
  have hPle : (P.toIdeal.map f).height ≤ 1 :=
    Ideal.map_height_le_one_of_mem_minimalPrimes hPminimal
  have hbad : (2 : ℕ∞) ≤ 1 := hPtwo.trans hPle
  norm_num at hbad

/-- A relevant height-two projective prime curve has three pairwise
projectively distinct rational points over an algebraically closed field.
The third point lies in a hyperplane whose defining form is nonzero at each
of the first two points. -/
theorem homogeneousPrime_exists_three_distinct_normalized_coordinates
    {K : Type u} [Field K] [IsAlgClosed K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime)
    (hrelevant : ¬ HomogeneousIdeal.irrelevant
      (homogeneousSubmodule (Fin 4) K) ≤ C)
    (hheight : C.toIdeal.height = 2) :
    ∃ (v : Fin 3 → Fin 4 → K),
      (∀ i, v i ≠ 0) ∧
      (∀ i, ∀ f ∈ C.toIdeal, f.eval₂ (algebraMap K K) (v i) = 0) ∧
      (∀ i j, i ≠ j → ∀ a : K, a • v i ≠ v j) := by
  obtain ⟨j, x, k, y, hxj, hxC, hyk, hyC, hxy⟩ :=
    homogeneousPrime_exists_two_distinct_normalized_coordinates
      C hprime hrelevant hheight
  have hx0 : x ≠ 0 := by
    intro h
    have := congrFun h j
    simp [hxj] at this
  have hy0 : y ≠ 0 := by
    intro h
    have := congrFun h k
    simp [hyk] at this
  have hli : LinearIndependent K ![x, y] :=
    (LinearIndependent.pair_iff' hx0).mpr (fun a => (hxy a).symm)
  obtain ⟨Lx, hLx, hLxx, hLxy⟩ :=
    exists_homogeneousLinearForm_separating_pair x y hli
  obtain ⟨Ly, hLy, hLyy, hLyx⟩ :=
    exists_homogeneousLinearForm_separating_pair y x
      (LinearIndependent.pair_symm_iff.mp hli)
  let ell := Lx + Ly
  have hell : ell.IsHomogeneous 1 := hLx.add hLy
  have hellx : MvPolynomial.aeval x ell = 1 := by
    simp only [ell, map_add, hLxx, hLyx, add_zero]
  have helly : MvPolynomial.aeval y ell = 1 := by
    simp only [ell, map_add, hLxy, hLyy, zero_add]
  obtain ⟨P, hPprime, hCP, hPell, hPrelevant, -⟩ :=
    homogeneousPrime_exists_relevant_linear_section
      C hprime hheight ell hell j x hxj hxC
  obtain ⟨m, z, hzm, -, hzP⟩ :=
    homogeneousPrime_exists_normalized_coordinates P hPprime hPrelevant
  have hzC : ∀ f ∈ C.toIdeal,
      f.eval₂ (algebraMap K K) z = 0 := by
    intro f hf
    exact hzP f (hCP hf)
  have hzEll : MvPolynomial.aeval z ell = 0 := by
    simpa [Algebra.algebraMap_self] using hzP ell hPell
  have hz0 : z ≠ 0 := by
    intro h
    have := congrFun h m
    simp [hzm] at this
  have hzx : ∀ a : K, z ≠ a • x := by
    intro a h
    have heval := congrArg (fun w => MvPolynomial.aeval w ell) h
    rw [hzEll, aeval_smul_of_isHomogeneous ell hell, pow_one, hellx,
      mul_one] at heval
    have ha : a = 0 := heval.symm
    subst a
    exact hz0 (by simpa using h)
  have hzy : ∀ a : K, z ≠ a • y := by
    intro a h
    have heval := congrArg (fun w => MvPolynomial.aeval w ell) h
    rw [hzEll, aeval_smul_of_isHomogeneous ell hell, pow_one, helly,
      mul_one] at heval
    have ha : a = 0 := heval.symm
    subst a
    exact hz0 (by simpa using h)
  have hnoFromZ (w : Fin 4 → K)
      (hw : MvPolynomial.aeval w ell = 1) (a : K) : a • z ≠ w := by
    intro h
    have heval := congrArg (fun t => MvPolynomial.aeval t ell) h
    rw [aeval_smul_of_isHomogeneous ell hell, hzEll, mul_zero, hw] at heval
    exact zero_ne_one heval
  refine ⟨![x, y, z], ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [hx0, hy0, hz0]
  · intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;> assumption
  · intro i j hij a
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact (hxy a).symm
    · exact (hzx a).symm
    · exact ((LinearIndependent.pair_iff' hy0).mp
        (LinearIndependent.pair_symm_iff.mp hli) a)
    · exact (hzy a).symm
    · exact hnoFromZ x hellx a
    · exact hnoFromZ y helly a

/-- The cubic ideal piece of any relevant height-two homogeneous prime
curve over an algebraically closed field has dimension at most seventeen. -/
theorem fixedCurveCubicIdealPiece_finrank_le_seventeen_of_prime_height_two
    {K : Type u} [Field K] [IsAlgClosed K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hprime : C.toIdeal.IsPrime)
    (hrelevant : ¬ HomogeneousIdeal.irrelevant
      (homogeneousSubmodule (Fin 4) K) ≤ C)
    (hheight : C.toIdeal.height = 2) :
    finrank K (homogeneousIdealPiece C 3) ≤ 17 := by
  obtain ⟨v, hv, hvC, hdir⟩ :=
    homogeneousPrime_exists_three_distinct_normalized_coordinates
      C hprime hrelevant hheight
  apply fixedCurveCubicIdealPiece_finrank_le_seventeen C v hv hdir
  intro i f hf
  simpa [MvPolynomial.aeval_def] using hvC i f hf

/-- The cubic equations of such a prime curve, after passage to the cubic
surface it lies on, span at most sixteen independent sections. -/
theorem fixedCurveCubicSurfaceSystem_finrank_le_sixteen_of_prime_height_two
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCp : p ∈ C.toIdeal)
    (hprime : C.toIdeal.IsPrime)
    (hrelevant : ¬ HomogeneousIdeal.irrelevant
      (homogeneousSubmodule (Fin 4) K) ≤ C)
    (hheight : C.toIdeal.height = 2) :
    finrank K (fixedCurveCubicSurfaceSystem p hp C) ≤ 16 := by
  obtain ⟨v, hv, hvC, hdir⟩ :=
    homogeneousPrime_exists_three_distinct_normalized_coordinates
      C hprime hrelevant hheight
  let x : Fin 3 → cubicSurfaceAffinePoints p := fun i => ⟨v i, by
    constructor
    · simpa [MvPolynomial.aeval_def] using hvC i p hCp
    · exact hv i⟩
  apply fixedCurveCubicSurfaceSystem_finrank_le_sixteen p hp hne C x hdir
  intro i f hf
  simpa [MvPolynomial.aeval_def] using hvC i f hf

/-- A height-two homogeneous prime curve over any field has at most
seventeen independent ambient cubic equations. The proof passes to a
geometric prime component over the algebraic closure, applies the three
point bound there, and descends the dimension inequality. -/
theorem fixedCurveCubicIdealPiece_finrank_le_seventeen_of_prime_height_two_arbitrary_field
    {k : Type u} [Field k]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (hprime : C.toIdeal.IsPrime) (hheight : C.toIdeal.height = 2) :
    finrank k (homogeneousIdealPiece C 3) ≤ 17 := by
  let J : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) (AlgebraicClosure k)) :=
    HomogeneousIdeal.map
      (ambientCoefficientGradedRingHom
        (algebraMap k (AlgebraicClosure k))) C
  obtain ⟨P, hPprime, hPrelevant, hPheight, hJP⟩ :=
    exists_algebraicClosure_homogeneousPrime_over_height_two C hprime hheight
  have hJ : C.toIdeal.map
      (MvPolynomial.map (algebraMap k (AlgebraicClosure k))) = J.toIdeal := by
    change C.toIdeal.map
      (MvPolynomial.map (algebraMap k (AlgebraicClosure k))) =
      (HomogeneousIdeal.map
        (ambientCoefficientGradedRingHom
          (algebraMap k (AlgebraicClosure k))) C).toIdeal
    rw [HomogeneousIdeal.toIdeal_map]
    rfl
  have hpiece : homogeneousIdealPiece J 3 ≤ homogeneousIdealPiece P 3 := by
    intro q hq
    apply (mem_homogeneousIdealPiece_iff P 3 q).mpr
    exact hJP ((mem_homogeneousIdealPiece_iff J 3 q).mp hq)
  calc
    finrank k (homogeneousIdealPiece C 3) ≤
        finrank (AlgebraicClosure k) (homogeneousIdealPiece J 3) :=
      homogeneousIdealPiece_finrank_le_coefficientExtension C J hJ 3
    _ ≤ finrank (AlgebraicClosure k) (homogeneousIdealPiece P 3) :=
      Submodule.finrank_mono hpiece
    _ ≤ 17 :=
      fixedCurveCubicIdealPiece_finrank_le_seventeen_of_prime_height_two
        P hPprime hPrelevant hPheight

/-- Over any coefficient field, the defining cubic accounts for one of the
at most seventeen ambient equations of a prime fixed curve. Thus its
intrinsic cubic system on the surface has dimension at most sixteen. -/
theorem fixedCurveCubicSurfaceSystem_finrank_le_sixteen_of_prime_height_two_arbitrary_field
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (hCp : p ∈ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (hheight : C.toIdeal.height = 2) :
    finrank k (fixedCurveCubicSurfaceSystem p hp C) ≤ 16 := by
  letI : FiniteDimensional k (homogeneousSubmodule (Fin 4) k 3) :=
    (Submodule.fg_iff_finiteDimensional _).mp
      (MvPolynomial.homogeneousSubmodule_fg (Fin 4) k 3)
  letI : FiniteDimensional k (homogeneousIdealPiece C 3) := inferInstance
  letI : AddCommGroup (homogeneousIdealPiece C 3) := inferInstance
  letI : AddCommGroup (grading (equationIdeal p hp) 3) := inferInstance
  let f : homogeneousIdealPiece C 3 →ₗ[k] grading (equationIdeal p hp) 3 :=
    (cubicSurfaceHomogeneousCoordinateProjection p hp 3).comp
      (homogeneousIdealPiece C 3).subtype
  have hrange : LinearMap.range f = fixedCurveCubicSurfaceSystem p hp C := by
    simp only [f, fixedCurveCubicSurfaceSystem, LinearMap.range_comp,
      Submodule.range_subtype]
  have hdim := f.finrank_range_add_finrank_ker
  rw [hrange] at hdim
  have hker : 0 < finrank k (LinearMap.ker f) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    let q : homogeneousIdealPiece C 3 := ⟨⟨p, hp⟩, hCp⟩
    refine ⟨⟨q, ?_⟩, ?_⟩
    · apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change Ideal.Quotient.mk (equationIdeal p hp).toIdeal p = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton p))
    · intro hq
      apply hne
      exact congrArg (fun z : homogeneousIdealPiece C 3 => z.1.1)
        (congrArg Subtype.val hq)
  have hC :=
    fixedCurveCubicIdealPiece_finrank_le_seventeen_of_prime_height_two_arbitrary_field
      C hprime hheight
  omega

/-- The same cubic section bound holds for a possibly reducible or
nonreduced fixed subscheme as soon as it has a height-two prime component.
Its equations form a subspace of the equations of that component. -/
theorem fixedCurveCubicSurfaceSystem_finrank_le_sixteen_of_height_two_prime_extension
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (C P : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (hCp : p ∈ C.toIdeal) (hCP : C ≤ P)
    (hPprime : P.toIdeal.IsPrime) (hPheight : P.toIdeal.height = 2) :
    finrank k (fixedCurveCubicSurfaceSystem p hp C) ≤ 16 := by
  letI : FiniteDimensional k (homogeneousSubmodule (Fin 4) k 3) :=
    (Submodule.fg_iff_finiteDimensional _).mp
      (MvPolynomial.homogeneousSubmodule_fg (Fin 4) k 3)
  letI : Module.Finite k (grading (equationIdeal p hp) 3) :=
    Module.Finite.of_surjective
      (cubicSurfaceHomogeneousCoordinateProjection p hp 3)
      (cubicSurfaceHomogeneousCoordinateProjection_surjective p hp 3)
  have hpiece : homogeneousIdealPiece C 3 ≤ homogeneousIdealPiece P 3 := by
    intro q hq
    exact hCP hq
  have hsystem : fixedCurveCubicSurfaceSystem p hp C ≤
      fixedCurveCubicSurfaceSystem p hp P := Submodule.map_mono hpiece
  exact (Submodule.finrank_mono hsystem).trans
    (fixedCurveCubicSurfaceSystem_finrank_le_sixteen_of_prime_height_two_arbitrary_field
      p hp hne P (hCP hCp) hPprime hPheight)

/-- A minimal prime component of a relatively-prime cubic pair has the
height-two property needed for the fixed-curve section bound. This form
applies directly to an associated component extracted from a failed
regular-third-cubic condition. -/
theorem fixedCurveCubicSurfaceSystem_finrank_le_sixteen_of_minimalPrime_span_pair
    {k : Type u} [Field k]
    (p q : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hne : p ≠ 0)
    (hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) k))).IsPrime)
    (hrel : IsRelPrime p q)
    (C P : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (hCp : p ∈ C.toIdeal) (hCP : C ≤ P)
    (hPprime : P.toIdeal.IsPrime)
    (hPmin : P.toIdeal ∈ (Ideal.span ({p, q} : Set
      (MvPolynomial (Fin 4) k))).minimalPrimes) :
    finrank k (fixedCurveCubicSurfaceSystem p hp C) ≤ 16 := by
  have hspan : Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) k)) ≤
      P.toIdeal := hPmin.1.2
  have hheight : P.toIdeal.height = 2 :=
    homogeneousPrime_height_eq_two_of_span_pair_of_isRelPrime
      p q P hpprime hPprime hspan hrel
      (homogeneousIdeal_height_le_two_of_le_minimalPrime_span_pair
        p q P.toIdeal P hPmin le_rfl)
  exact fixedCurveCubicSurfaceSystem_finrank_le_sixteen_of_height_two_prime_extension
    p hp hne C P hCp hCP hPprime hheight


end PfaffianDescent
