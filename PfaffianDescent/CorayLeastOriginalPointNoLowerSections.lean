import PfaffianDescent.CorayAiLowerDegreeOriginalCubicPointPaddedCaller
import PfaffianDescent.CorayOriginalLeastPointNonintegralBClosure

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A genuine strict-degree component through the least original point
is impossible. Both original degree divisibility and geometric component
are constructed internally. -/
theorem leastOriginalCubicPoint_strictComponent_false001
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (P : closedPoints (hypersurface p hp))
    (hPointCoprime : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hLower : 1 + 3 * n.choose 2 ≤ (hypersurfaceToBase p hp).residueDegree P.1)
    (hUpper : (hypersurfaceToBase p hp).residueDegree P.1 < 1 + 3 * (n + 1).choose 2)
    (hPointLarge : 7 ≤ (hypersurfaceToBase p hp).residueDegree P.1)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (Q : closedPoints (scheme C))
    (hDegree : (toBase C).residueDegree Q.1 = (hypersurfaceToBase p hp).residueDegree P.1)
    (hStrict : actualCurveCoordinateHilbertDegree C < 3 * n) : False := by
  classical
  have hThree : 3 ∣ actualCurveCoordinateHilbertDegree C := by
    by_contra hDiv
    have hCoprime : Nat.Coprime (actualCurveCoordinateHilbertDegree C) 3 :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr hDiv).symm
    obtain ⟨R, hRCoprime, hRSmall⟩ :=
      selectedMinimalComponent_primeDegree_exists_smaller_originalCubic_point
        p q hp hp0 n hq hnot C hCmin hCoprime
        ((hypersurfaceToBase p hp).residueDegree P.1) hLower hUpper hPointLarge
    exact (not_lt_of_ge (hleast R hRCoprime)) hRSmall
  letI : C.toIdeal.IsPrime := hCmin.isPrime
  let Ω := AlgebraicClosure K
  letI : IsGalois K Ω := ⟨⟩
  obtain ⟨G, hG⟩ := originalPrime_exists_algebraicClosure_minimalComponent001 C
  obtain ⟨R, hRCoprime, hRSmall⟩ :=
    originalMinimalComponent_strictDegree_threeDivides_exists_smallerOriginalCubicPoint001
      p q hp hp0 n hn hq hnot C hCmin Q G hG
      (hDegree.symm ▸ hPointCoprime) (hDegree.symm ▸ hLower)
      (hDegree.symm ▸ hUpper) (hDegree.symm ▸ hPointLarge) hThree hStrict
  exact (not_lt_of_ge (hleast R hRCoprime)) (hRSmall.trans_eq hDegree)

/-- Leastness forces every genuinely lower-degree original coordinate
section through the SAME point to vanish. No minimum-degree hypothesis,
chosen component, auxiliary point, or integrality certificate is supplied. -/
theorem leastOriginalCubicPoint_lowerCoordinateSections_eq_zero001
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n)
    (P : closedPoints (hypersurface p hp))
    (hPointCoprime : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hLower : 1 + 3 * n.choose 2 ≤ (hypersurfaceToBase p hp).residueDegree P.1)
    (hUpper : (hypersurfaceToBase p hp).residueDegree P.1 < 1 + 3 * (n + 1).choose 2)
    (hPointLarge : 7 ≤ (hypersurfaceToBase p hp).residueDegree P.1) :
    letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    ∀ (j : Fin 4) (g : ChartRing (equationIdeal p hp) j →+* (hypersurface p hp).residueField P.1),
      g.comp (chartBaseMap (equationIdeal p hp) j) =
        algebraMap K ((hypersurface p hp).residueField P.1) →
      Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) j =
        (hypersurface p hp).fromSpecResidueField P.1 →
    ∀ (a : ℕ), a < n →
    ∀ (hpx : p.eval₂ (algebraMap K ((hypersurface p hp).residueField P.1))
        (fun i => g (chartCoordinate (equationIdeal p hp) j i)) = 0)
      (s : cubicThroughCoordinateSections p hp a
        (fun i => g (chartCoordinate (equationIdeal p hp) j i)) hpx), s = 0 := by
  classical
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  intro j g hgbase hgpoint a ha hpx s
  by_contra hs
  obtain ⟨q, hq, hnot, _hqP, C, hCmin, Q, hStrict, _hPoint, _hIso, hDegree, _hPQ⟩ :=
    originalCubic_lowerCoordinateSection_exists_paddedDegreeCurve_sameOriginalPoint_strictComponent001
      p hp hp0 P n j g hgbase hgpoint a ha hpx s hs
  exact leastOriginalCubicPoint_strictComponent_false001 p q hp hp0 n hn hq hnot
    P hPointCoprime hleast hLower hUpper hPointLarge C hCmin Q hDegree hStrict

end PfaffianDescent.Coray
