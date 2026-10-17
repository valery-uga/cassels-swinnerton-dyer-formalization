import PfaffianDescent.CorayStrictOwnComponentOriginalBPoint
import PfaffianDescent.CorayHomogeneousComponentOriginalClosedPoint
import PfaffianDescent.CorayHomogeneousProjectiveComponentBijection
import PfaffianDescent.CoraySelectedCurveOriginalPointIncidenceLift
import PfaffianDescent.CorayOwnMinimalComponentNonfiniteAnyField
import PfaffianDescent.CorayPrimeDegreeComponentOriginalSmallerPoint
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Natural least-original-point B rejection for the SAME nonintegral
whole intersection. Original and geometric components are chosen internally. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

/-- A genuine original prime has an ACTUAL homogeneous minimal component
in the algebraic closure. No component, model, geometric-integrality or
coefficient-degree outcome is supplied. -/
theorem originalPrime_exists_algebraicClosure_minimalComponent001
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime] :
    ∃ G : HomogeneousIdeal (homogeneousSubmodule (Fin 4) (AlgebraicClosure K)),
      G.toIdeal ∈
        (I.map (componentPolynomialCoefficientMap (algebraMap K (AlgebraicClosure K)))).toIdeal.minimalPrimes := by
  classical
  let Ω := AlgebraicClosure K
  let f := MvPolynomial.map (σ := Fin 4) (algebraMap K Ω)
  let J := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
  have hIJ : I.toIdeal.map f = J.toIdeal := rfl
  have hf : Function.Injective f := MvPolynomial.map_injective _ (algebraMap K Ω).injective
  have hfIntegral : f.IsIntegral := by
    change (algebraMap (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) Ω)).IsIntegral
    exact algebraMap_isIntegral_iff.mpr inferInstance
  have hJProper : J.toIdeal ≠ ⊤ := by
    rw [← hIJ]
    exact fun h => (inferInstance : I.toIdeal.IsPrime).ne_top
      ((Ideal.map_eq_top_iff f hf hfIntegral).mp h)
  obtain ⟨Q, hQ⟩ := Ideal.nonempty_minimalPrimes hJProper
  let G := Q.homogeneousCore (homogeneousSubmodule (Fin 4) Ω)
  have hGQ : G.toIdeal = Q := homogeneousIdeal_minimalPrime_homogeneousCore_toIdeal J Q hQ
  refine ⟨G, ?_⟩
  change G.toIdeal ∈ J.toIdeal.minimalPrimes
  rw [hGQ]
  exact hQ

/-- The large natural B branch is impossible through a least original
prime-to-three cubic point. SAME-q nonintegrality includes one nonreduced
component. Neither an original/geometric component nor any cycle, model,
regularity, word, section or smaller-point outcome is an input. -/
theorem coray_case_B_nonintegral_selectedCurve_through_least_originalCubic_point_false001
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (P : closedPoints (hypersurface p hp))
    (hPointCoprime : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hPcurve : P.1 ∈ Set.range (cubicSecondEquationCurveImmersion p q hp n hq))
    (hLower : 1 + 3 * n.choose 2 ≤ (hypersurfaceToBase p hp).residueDegree P.1)
    (hUpper : (hypersurfaceToBase p hp).residueDegree P.1 < 1 + 3 * (n + 1).choose 2)
    (hPointLarge : 7 ≤ (hypersurfaceToBase p hp).residueDegree P.1)
    (hNonIntegral : ¬ IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))) : False := by
  classical
  obtain ⟨PX, hPXpoint, hPXiso, hPXdegree⟩ :=
    selectedCurve_originalClosedPoint_of_originalPoint_mem_image p q hp n hq P hPcurve
  obtain ⟨I, hJI, hI, hIprime, Q, hQpoint, hQiso, hQdegree⟩ :=
    homogeneousProjective_originalClosedPoint_exists_minimalComponent
      (projectiveIntersectionIdeal p q hp hq) PX
  have hGround : (toBase I).residueDegree Q.1 = (hypersurfaceToBase p hp).residueDegree P.1 :=
    hQdegree.trans hPXdegree
  have hThree : 3 ∣ actualCurveCoordinateHilbertDegree I := by
    by_contra hDiv
    have hCoprime : Nat.Coprime (actualCurveCoordinateHilbertDegree I) 3 :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr hDiv).symm
    obtain ⟨R, hRCoprime, hRSmall⟩ :=
      selectedMinimalComponent_primeDegree_exists_smaller_originalCubic_point
        p q hp hp0 n hq hnot I hI hCoprime
        ((hypersurfaceToBase p hp).residueDegree P.1) hLower hUpper hPointLarge
    exact (not_lt_of_ge (hleast R hRCoprime)) hRSmall
  letI : I.toIdeal.IsPrime := hIprime
  let Ω := AlgebraicClosure K
  letI : IsGalois K Ω := ⟨⟩
  obtain ⟨G, hG⟩ := originalPrime_exists_algebraicClosure_minimalComponent001 I
  have hQCoprime : Nat.Coprime ((toBase I).residueDegree Q.1) 3 :=
    hGround.symm ▸ hPointCoprime
  have hQLower : 1 + 3 * n.choose 2 ≤ (toBase I).residueDegree Q.1 := hGround.symm ▸ hLower
  have hQUpper : (toBase I).residueDegree Q.1 < 1 + 3 * (n + 1).choose 2 := hGround.symm ▸ hUpper
  have hQLarge : 7 ≤ (toBase I).residueDegree Q.1 := hGround.symm ▸ hPointLarge
  obtain ⟨R, hRCoprime, hRSmall⟩ :=
    originalNonintegralWholeIntersection_component_threeDivides_exists_smallerOriginalCubicPoint001
      p q hp hp0 n hn hq hnot I hI Q G hG hQCoprime hQLower hQUpper hQLarge hThree hNonIntegral
  have hOriginalSmall : (hypersurfaceToBase p hp).residueDegree R.1 <
      (hypersurfaceToBase p hp).residueDegree P.1 := hRSmall.trans_eq hGround
  exact (not_lt_of_ge (hleast R hRCoprime)) hOriginalSmall

end PfaffianDescent.Coray
