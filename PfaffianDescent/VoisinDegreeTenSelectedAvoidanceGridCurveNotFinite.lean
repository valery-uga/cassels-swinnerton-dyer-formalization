import PfaffianDescent.VoisinDegreeEightFixedCurveScheme
import PfaffianDescent.FiniteProjectiveHyperplane

/-! Every positive homogeneous section cuts a height-two projective prime
curve. Thus an actual height-two curve cannot be a finite projective scheme. -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem voisinDegreeTenSelectedAvoidance_prime_exists_minimal_positive_section
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCprime : C.toIdeal.IsPrime)
    (ell : MvPolynomial (Fin 4) K) {d : ℕ}
    (hell : ell.IsHomogeneous d) (hd : 0 < d) :
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
      exact HomogeneousIdeal.mem_irrelevant_of_mem _ hd
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

theorem voisinDegreeTenSelectedAvoidance_prime_exists_relevant_positive_section
    {K : Type u} [Field K] [Infinite K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCprime : C.toIdeal.IsPrime) (hCheight : C.toIdeal.height = 2)
    (ell : MvPolynomial (Fin 4) K) {d : ℕ}
    (hell : ell.IsHomogeneous d) (hd : 0 < d)
    (j : Fin 4) (x : Fin 4 → K) (hxj : x j = 1)
    (hzero : ∀ f ∈ C.toIdeal, f.eval₂ (algebraMap K K) x = 0) :
    ∃ P : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K),
      P.toIdeal.IsPrime ∧ C ≤ P ∧ ell ∈ P.toIdeal ∧
      (¬ HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ P) ∧
      P.toIdeal ∈ (C.toIdeal ⊔ Ideal.span ({ell} : Set _)).minimalPrimes := by
  obtain ⟨P, hPprime, hCP, hXj, hPminimal⟩ :=
    voisinDegreeTenSelectedAvoidance_prime_exists_minimal_positive_section C hCprime ell hell hd
  refine ⟨P, hPprime, hCP, hXj, ?_, hPminimal⟩
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

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_heightTwoPrime_not_finite_algClosed
    {K : Type u} [Field K] [IsAlgClosed K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCprime : C.toIdeal.IsPrime) (hCheight : C.toIdeal.height = 2) :
    ¬ IsFinite (toBase C) := by
  intro hfinite
  letI : IsFinite (toBase C) := hfinite
  have hrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ C :=
    homogeneousIdeal_relevant_of_height_le_two C (by rw [hCheight])
  obtain ⟨j, x, hxj, _, hzero⟩ :=
    homogeneousPrime_exists_normalized_coordinates C hCprime hrel
  obtain ⟨z, hz, havoid⟩ := finite_projective_exists_nowhere_vanishing_linear C
  obtain ⟨ell, hell, hellz⟩ := hz
  obtain ⟨P, hPprime, hCP, hellP, hPrel, _⟩ :=
    voisinDegreeTenSelectedAvoidance_prime_exists_relevant_positive_section
      C hCprime hCheight ell hell (by decide : 0 < 1) j x hxj hzero
  let G := gradedQuotientMap C P hCP
  let ι : scheme P ⟶ scheme C := Proj.map G
    (gradedSurjective_irrelevant_le G (gradedQuotientMap_surjective C P hCP))
  let y := homogeneousPrimeQuotientProjectivePoint P hPprime hPrel
  apply havoid (ι y)
  change G z ∈ y.asHomogeneousIdeal
  change G z = 0
  rw [← hellz]
  change Ideal.Quotient.mk P.toIdeal ell = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hellP

end PfaffianDescent
