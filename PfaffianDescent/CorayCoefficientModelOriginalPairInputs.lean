import PfaffianDescent.CorayJointSelectedComponentPositiveDegree

/-! Genuine original p/q inputs over SAME coefficient field for SAME model minimal prime. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Original p/q/minimal I and a minimal component D of I_M construct ALL
literal extended p/q hypotheses needed on D/M. No desired smoothness,
nondivisibility, prime-over-p/q, GI, degree or genus outcome is supplied. -/
theorem selectedOriginalMinimalComponent_coefficientMinimalPrime_originalPairInputs001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) M))
    (hD : D.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes) :
    p.map (algebraMap K M) ≠ 0 ∧
      Smooth (hypersurfaceToBase (p.map (algebraMap K M)) (hp.map (algebraMap K M))) ∧
      q.map (algebraMap K M) ∉
        Ideal.span ({p.map (algebraMap K M)} : Set (MvPolynomial (Fin 4) M)) ∧
      D.toIdeal ∈ (projectiveIntersectionIdeal
        (p.map (algebraMap K M)) (q.map (algebraMap K M))
          (hp.map (algebraMap K M)) (hq.map (algebraMap K M))).toIdeal.minimalPrimes := by
  letI : I.toIdeal.IsPrime := hI.isPrime
  let f := algebraMap K M
  have hMapInjective : Function.Injective (MvPolynomial.map f :
      MvPolynomial (Fin 4) K → MvPolynomial (Fin 4) M) :=
    MvPolynomial.map_injective f (FaithfulSMul.algebraMap_injective K M)
  have hpM0 : p.map f ≠ 0 := by
    intro h
    apply hp0
    exact hMapInjective (by simpa using h)
  have hSmooth : Smooth (hypersurfaceToBase (p.map f) (hp.map f)) :=
    smooth_hypersurfaceToBase_map f p hp
  have hMapSpan : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).map
      (MvPolynomial.map f) = Ideal.span ({p.map f} : Set (MvPolynomial (Fin 4) M)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hnotM : q.map f ∉ Ideal.span ({p.map f} : Set (MvPolynomial (Fin 4) M)) := by
    intro h
    have hm : q ∈ Ideal.comap (MvPolynomial.map f)
        ((Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).map (MvPolynomial.map f)) := by
      change q.map f ∈ (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).map
        (MvPolynomial.map f)
      rw [hMapSpan]
      exact h
    have hContract : Ideal.comap (MvPolynomial.map f)
        ((Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).map (MvPolynomial.map f)) =
          Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) :=
      mvPolynomial_comap_map_coefficientExtension (k := K) (K := M)
        (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    rw [hContract] at hm
    exact hnot hm
  have hMapPQ : (projectiveIntersectionIdeal p q hp hq).toIdeal.map (MvPolynomial.map f) =
      (projectiveIntersectionIdeal (p.map f) (q.map f) (hp.map f) (hq.map f)).toIdeal := by
    rw [projectiveIntersectionIdeal_toIdeal, projectiveIntersectionIdeal_toIdeal,
      Ideal.map_span]
    simp only [Set.image_insert_eq, Set.image_singleton]
  have hDWhole : D.toIdeal ∈
      ((projectiveIntersectionIdeal p q hp hq).toIdeal.map (MvPolynomial.map f)).minimalPrimes :=
    originalMinimalPrime_coefficientExtension_minimalPrime_over_wholeIdeal
      (projectiveIntersectionIdeal p q hp hq).toIdeal I.toIdeal hI D.toIdeal hD
  have hDPair : D.toIdeal ∈ (projectiveIntersectionIdeal
      (p.map f) (q.map f) (hp.map f) (hq.map f)).toIdeal.minimalPrimes := by
    rw [← hMapPQ]
    exact hDWhole
  exact ⟨hpM0, hSmooth, hnotM, hDPair⟩

end PfaffianDescent.Coray
