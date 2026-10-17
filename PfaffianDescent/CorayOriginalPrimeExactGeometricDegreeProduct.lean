import PfaffianDescent.CoraySelectedComponentHeightAndRelevance
import PfaffianDescent.CorayOriginalPrimeCoefficientReducedUnion
import PfaffianDescent.CorayOriginalEquationsGeometricDegreeBound

/-! Exact degree product for SAME original homogeneous prime and its genuine
geometric components. Literal reduced whole union is constructed internally. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry TopologicalSpace MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Perfect-K original prime coefficient extension equals its actual whole
finite union. Current actual union degree sum and geometric common-degree
produce the exact original-degree product; no degree equality is an input. -/
theorem originalPrime_geometricComponents_card_mul_degree_eq_originalDegree001
    {K Ω : Type u} [Field K] [PerfectField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [IsGalois K Ω]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ I)
    (p q : MvPolynomial (Fin 4) Ω) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) Ω)))
    (hPQI : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤
      (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal)
    (P : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Ω))
    (hP : P.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes) :
    Nat.card (irreducibleComponents (scheme
      (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))))) *
        actualCurveCoordinateHilbertDegree P = actualCurveCoordinateHilbertDegree I ∧
      Nat.card (irreducibleComponents (scheme
        (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))))) *
          actualCurveCoordinateHilbertDegree P ≤ 3 * n := by
  classical
  let J := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
  let T := J.toIdeal.minimalPrimes
  letI : Finite T := (Ideal.finite_minimalPrimes_of_isNoetherianRing
    (MvPolynomial (Fin 4) Ω) J.toIdeal).to_subtype
  letI : Fintype T := Fintype.ofFinite T
  let f : T → HomogeneousIdeal (homogeneousSubmodule (Fin 4) Ω) :=
    fun Q => Q.1.homogeneousCore (homogeneousSubmodule (Fin 4) Ω)
  have hunder (Q : T) : (f Q).toIdeal = Q.1 :=
    homogeneousIdeal_minimalPrime_homogeneousCore_toIdeal J Q.1 Q.2
  have hf : Function.Injective f := by
    intro Q R h
    apply Subtype.ext
    exact (hunder Q).symm.trans ((congrArg HomogeneousIdeal.toIdeal h).trans (hunder R))
  let F := Finset.univ.image f
  have hFmin : ∀ C ∈ F, C.toIdeal ∈ J.toIdeal.minimalPrimes := by
    intro C hC
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hC
    exact (hunder Q).symm ▸ Q.2
  have hFrel : ∀ C ∈ F,
      ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) Ω) ≤ C :=
    fun C hC => homogeneousCoefficientExtension_minimalPrime_relevant I hIrel C (hFmin C hC)
  obtain ⟨hunionDegree, hsumBound, _N, _hN⟩ :=
    selectedProjectiveFiniteActualComponents_degree_sum_bound
      p q hp hp0 n hn hq hnot J hPQI F hFmin hFrel
  have hcommon : ∀ C ∈ F,
      actualCurveCoordinateHilbertDegree C = actualCurveCoordinateHilbertDegree P := by
    intro C hC
    have hvalues : (fun d => finrank Ω (grading C d)) =
        (fun d => finrank Ω (grading P d)) :=
      funext fun d => originalPrime_geometricMinimalComponents_hilbertFunction_eq
        I C P (hFmin C hC) hP d
    exact congrArg (fun h : ℕ → ℕ =>
      if hex : ∃ μ : ℕ, ∃ N : ℕ, ∀ m, N ≤ m → h (m + 1) = h m + μ
      then Nat.find hex else 0) hvalues
  have hsum : (∑ C ∈ F, actualCurveCoordinateHilbertDegree C) =
      F.card * actualCurveCoordinateHilbertDegree P := by
    calc
      _ = ∑ _C ∈ F, actualCurveCoordinateHilbertDegree P := Finset.sum_congr rfl hcommon
      _ = _ := by simp
  have hcardRaw : F.card = Nat.card T := by
    simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using
      Finset.card_image_of_injective (Finset.univ : Finset T) hf
  have hcardProj : Nat.card T = Nat.card (irreducibleComponents (scheme J)) :=
    Nat.card_congr (homogeneousCoefficientExtension_minimalPrimesEquivProjectiveComponents
      (E := Ω) I hIrel)
  have hWholeUnion : F.inf id = J :=
    originalHomogeneousPrime_perfectAlgebraicCoefficientExtension_eq_finiteMinimalComponentIntersection001 I
  have hCoefficient : actualCurveCoordinateHilbertDegree J = actualCurveCoordinateHilbertDegree I :=
    actualCurveCoordinateHilbertDegree_eq_coefficientExtension I J rfl
  rw [hsum, hcardRaw, hcardProj] at hunionDegree hsumBound
  exact ⟨hunionDegree.symm.trans
    ((congrArg actualCurveCoordinateHilbertDegree hWholeUnion).trans hCoefficient), hsumBound⟩


/-- Original smooth cubic/q minimal-prime geometry internally produces all
closure equations/containment/relevance/prime instances. The SAME selected
original I and SAME actual geometric P have exact r*mu_P=mu_I and r*mu_P<=3n.
No reducedness, genus, GI, degree product or divisibility outcome is assumed. -/
theorem originalSelectedMinimalPrime_geometricComponents_card_mul_degree_eq_originalDegree001
    {K Ω : Type u} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [IsGalois K Ω]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Ω))
    (hP : P.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes) :
    Nat.card (irreducibleComponents (scheme
      (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))))) *
        actualCurveCoordinateHilbertDegree P = actualCurveCoordinateHilbertDegree I ∧
      Nat.card (irreducibleComponents (scheme
        (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))))) *
          actualCurveCoordinateHilbertDegree P ≤ 3 * n := by
  classical
  letI : I.toIdeal.IsPrime := hI.isPrime
  have hIrel := selectedProjectiveMinimalComponent_homogeneous_relevant p q hp hp0 n hq hnot I hI
  have hPQI := hI.le
  let f := algebraMap K Ω
  have hmapinj : Function.Injective (MvPolynomial.map f :
      MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) Ω) :=
    MvPolynomial.map_injective f (FaithfulSMul.algebraMap_injective K Ω)
  have hpΩ0 : p.map f ≠ 0 := by
    intro h
    apply hp0
    exact hmapinj (by simpa using h)
  letI : Smooth (hypersurfaceToBase (p.map f) (hp.map f)) :=
    smooth_hypersurfaceToBase_map f p hp
  have hmapSpan : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).map
      (MvPolynomial.map f) = Ideal.span ({p.map f} : Set (MvPolynomial (Fin 4) Ω)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hnotΩ : q.map f ∉ Ideal.span ({p.map f} : Set (MvPolynomial (Fin 4) Ω)) := by
    intro h
    have hm : q ∈ Ideal.comap (MvPolynomial.map f)
        ((Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).map (MvPolynomial.map f)) := by
      change q.map f ∈ (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).map (MvPolynomial.map f)
      rw [hmapSpan]
      exact h
    have hcontract : Ideal.comap (MvPolynomial.map f)
        ((Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).map (MvPolynomial.map f)) =
          Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) :=
      mvPolynomial_comap_map_coefficientExtension (k := K) (K := Ω)
        (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    rw [hcontract] at hm
    exact hnot hm
  have hmapPQ : (projectiveIntersectionIdeal p q hp hq).toIdeal.map (MvPolynomial.map f) =
      (projectiveIntersectionIdeal (p.map f) (q.map f) (hp.map f) (hq.map f)).toIdeal := by
    rw [projectiveIntersectionIdeal_toIdeal, projectiveIntersectionIdeal_toIdeal,
      Ideal.map_span]
    simp only [Set.image_insert_eq, Set.image_singleton]
  have hPQΩ : (projectiveIntersectionIdeal (p.map f) (q.map f)
      (hp.map f) (hq.map f)).toIdeal ≤
        (I.map (componentPolynomialCoefficientMap f)).toIdeal := by
    change _ ≤ I.toIdeal.map (MvPolynomial.map f)
    rw [← hmapPQ]
    exact Ideal.map_mono hPQI
  exact originalPrime_geometricComponents_card_mul_degree_eq_originalDegree001
    I hIrel (p.map f) (q.map f) (hp.map f) hpΩ0 n hn (hq.map f) hnotΩ hPQΩ P hP


end PfaffianDescent.Coray
