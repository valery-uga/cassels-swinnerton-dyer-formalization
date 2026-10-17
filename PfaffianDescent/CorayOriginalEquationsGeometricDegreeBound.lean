import PfaffianDescent.CorayActualGeometricComponentDegreeProduct
import PfaffianDescent.PolynomialCoefficientFaithfullyFlat
import AllCharacteristics.ProjectiveFiberSmoothness

/-! Literal ORIGINAL-K equations give actual Ω geometry and geometric r*μ≤3n.
Smoothness is transported by native projective coefficient base change;
nonmembership is preserved by faithful coefficient contraction. No geometric
smoothness, regularity, equation containment, count or degree certificate is
supplied. SOURCE ONLY / UNVERIFIED; root owns compiler/audit. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry TopologicalSpace MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- ORIGINAL p/q geometry internally transports to literal IΩ; the selected
actual Ω-minimal component's OWN degree satisfies the actual geometric bound. -/
theorem originalSelectedPrime_geometricComponents_card_mul_degree_bound
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [IsGalois K Ω]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ I)
    (hPQI : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ I.toIdeal)
    (P : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Ω))
    (hP : P.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes) :
    Nat.card (irreducibleComponents (scheme
      (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))))) *
        actualCurveCoordinateHilbertDegree P ≤ 3 * n := by
  classical
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
  exact originalPrime_geometricComponents_card_mul_degree_bound
    I hIrel (p.map f) (q.map f) (hp.map f) hpΩ0 n hn (hq.map f) hnotΩ hPQΩ P hP

end PfaffianDescent.Coray
