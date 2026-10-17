import PfaffianDescent.CorayActualSelectedComponentDegreePositivity
import PfaffianDescent.CorayHomogeneousProjectiveComponentBijection
import AllCharacteristics.ProjectiveBaseChange
import AllCharacteristics.HomogeneousProjectiveAmbient
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! SOURCE ONLY / UNVERIFIED. Original minimal component nonfiniteness.
The WHOLE extended ideal is retained. A geometric minimal prime is used
only in a contradiction to finiteness; it never replaces the original C. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

/-- Going down and actual contraction preserve the height-two lower bound;
original minimality and the two-generator bound give the upper bound. -/
theorem selectedProjectiveMinimalComponent_coefficientMinimalPrime_height_eq_two
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E))
    (hDmin : D.toIdeal ∈
      (C.toIdeal.map (MvPolynomial.map (algebraMap K E))).minimalPrimes) :
    D.toIdeal.height = 2 := by
  letI : C.toIdeal.IsPrime := hCmin.isPrime
  letI : D.toIdeal.IsPrime := hDmin.isPrime
  letI : Algebra.HasGoingDown (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) E) :=
    polynomialCoefficientExtension_hasGoingDown (K := K) (E := E)
  have hcontract := polynomialCoefficientExtension_minimalPrime_comap_eq C.toIdeal D.toIdeal hDmin
  letI : D.toIdeal.LiesOver C.toIdeal := ⟨hcontract.symm⟩
  have hCheight := selectedProjectiveMinimalComponent_homogeneous_height_eq_two
    p q hp hp0 n hq hnot C hCmin
  have hformula := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown C.toIdeal D.toIdeal
  have hlo : (2 : ℕ∞) ≤ D.toIdeal.height := by
    rw [hformula, hCheight]
    exact le_add_of_nonneg_right zero_le
  have hwhole := originalMinimalPrime_coefficientExtension_minimalPrime_over_wholeIdeal
    (projectiveIntersectionIdeal p q hp hq).toIdeal C.toIdeal hCmin D.toIdeal hDmin
  have hpair : D.toIdeal ∈
      (Ideal.span ({p.map (algebraMap K E), q.map (algebraMap K E)} :
        Set (MvPolynomial (Fin 4) E))).minimalPrimes := by
    simpa only [projectiveIntersectionIdeal_toIdeal, Ideal.map_span,
      Set.image_insert_eq, Set.image_singleton] using hwhole
  have hhi := PfaffianDescent.homogeneousPrime_height_le_two_of_mem_minimalPrimes_span_pair
    (p.map (algebraMap K E)) (q.map (algebraMap K E)) D hpair
  exact le_antisymm hhi hlo

/-- SAME original minimal C cannot be finite, including over finite K.
Whole pullback finiteness would force a height-two geometric component finite. -/
theorem selectedProjectiveMinimalComponent_toBase_not_isFinite_anyField
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ¬ IsFinite (toBase C) := by
  classical
  intro hfinite
  letI : C.toIdeal.IsPrime := hCmin.isPrime
  letI : IsFinite (toBase C) := hfinite
  let Ω := AlgebraicClosure K
  let f := MvPolynomial.map (σ := Fin 4) (algebraMap K Ω)
  let J := C.map (ambientCoefficientGradedRingHom (algebraMap K Ω))
  have hCJ : C.toIdeal.map f = J.toIdeal := rfl
  have hf : Function.Injective f := MvPolynomial.map_injective _ (algebraMap K Ω).injective
  have hfint : f.IsIntegral := by
    change (algebraMap (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) Ω)).IsIntegral
    exact algebraMap_isIntegral_iff.mpr inferInstance
  have hJproper : J.toIdeal ≠ ⊤ := by
    rw [← hCJ]
    exact fun h => hCmin.isPrime.ne_top ((Ideal.map_eq_top_iff f hf hfint).mp h)
  let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let e := projectiveBaseChangeIso (algebraMap K Ω) C J hCJ
  letI : IsFinite (toBase J) := by
    have hc : IsFinite (e.hom ≫ pullback.snd (toBase C) b) := inferInstance
    have hbase : e.hom ≫ pullback.snd (toBase C) b = toBase J :=
      projectiveBaseChangeIso_hom_snd (algebraMap K Ω) C J hCJ
    rw [hbase] at hc
    exact hc
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hJproper
  let D := P.homogeneousCore (homogeneousSubmodule (Fin 4) Ω)
  have hDunder : D.toIdeal = P := homogeneousIdeal_minimalPrime_homogeneousCore_toIdeal J P hP
  have hDmin : D.toIdeal ∈ (C.toIdeal.map f).minimalPrimes := by
    rw [hCJ, hDunder]
    exact hP
  have hDprime : D.toIdeal.IsPrime := hDmin.isPrime
  have hDheight := selectedProjectiveMinimalComponent_coefficientMinimalPrime_height_eq_two
    p q hp hp0 n hq hnot C hCmin D hDmin
  have hJD : J.toIdeal ≤ D.toIdeal := by
    rw [hDunder]
    exact hP.le
  let i := PfaffianDescent.schemeQuotientMap J D hJD
  letI : IsClosedImmersion i := PfaffianDescent.schemeQuotientMap_closedImmersion J D hJD
  have hcompose : IsFinite (i ≫ toBase J) := inferInstance
  have hbaseD : i ≫ toBase J = toBase D :=
    PfaffianDescent.schemeQuotientMap_toBase J D hJD
  rw [hbaseD] at hcompose
  exact PfaffianDescent.voisinDegreeTenSelectedAvoidance_heightTwoPrime_not_finite_algClosed
    D hDprime hDheight hcompose

end PfaffianDescent.Coray
