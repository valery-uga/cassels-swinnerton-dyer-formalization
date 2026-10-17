import PfaffianDescent.CorayAiLowerDegreeSameComponentProductTransfer
import PfaffianDescent.CorayBoundedOriginalSectionFamily
import PfaffianDescent.CoraySelectedCurveOriginalClosedPoint
import PfaffianDescent.CorayGenericNormalizationOriginalCubicProperMap
import PfaffianDescent.HomogeneousQuotientMap

/-! Actual original cubic P and its genuine lower-degree coordinate section
construct a padded degree-n q and SAME strict-degree component through P.
Both curve routes are proved to be the SAME original cubic morphism. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Abstract canonical homogeneous quotient routes agree before concrete
original equations or points are substituted. Both routes end at SAME C. -/
private theorem homogeneousComponent_twoOriginalCurveRoutes001
    (I₀ I₁ I₂ C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (h₀₁ : I₀.toIdeal ≤ I₁.toIdeal) (h₁C : I₁.toIdeal ≤ C.toIdeal)
    (h₀₂ : I₀.toIdeal ≤ I₂.toIdeal) (h₂C : I₂.toIdeal ≤ C.toIdeal) :
    schemeQuotientMap I₁ C h₁C ≫ schemeQuotientMap I₀ I₁ h₀₁ =
      schemeQuotientMap I₂ C h₂C ≫ schemeQuotientMap I₀ I₂ h₀₂ := by
  let h₀C := h₀₁.trans h₁C
  exact (schemeQuotientMap_comp I₀ I₁ h₀₁ C h₁C h₀C).trans
    (schemeQuotientMap_comp I₀ I₂ h₀₂ C h₂C h₀C).symm

/-- Actual polynomial representative caller; all original point incidence,
product nonmembership, strict degree and two curve routes are derived. -/
private theorem originalCubic_lowerPolynomial_paddedSameComponent001
    [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (P : closedPoints (hypersurface p hp)) (n : ℕ) :
    letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    ∀ (j : Fin 4) (g : ChartRing (equationIdeal p hp) j →+* (hypersurface p hp).residueField P.1),
      g.comp (chartBaseMap (equationIdeal p hp) j) =
        algebraMap K ((hypersurface p hp).residueField P.1) →
      Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) j =
        (hypersurface p hp).fromSpecResidueField P.1 →
    ∀ (a : ℕ), a < n → ∀ (s : MvPolynomial (Fin 4) K) (hs : s.IsHomogeneous a),
      s ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) →
      s.eval₂ (algebraMap K ((hypersurface p hp).residueField P.1))
        (fun i => g (chartCoordinate (equationIdeal p hp) j i)) = 0 →
    ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      q.eval₂ (algebraMap K ((hypersurface p hp).residueField P.1))
        (fun i => g (chartCoordinate (equationIdeal p hp) j i)) = 0 ∧
      ∃ (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
        (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
        (Q : closedPoints (scheme C)),
        actualCurveCoordinateHilbertDegree C < 3 * n ∧
        let iC := schemeQuotientMap (projectiveIntersectionIdeal p q hp hq) C hCmin.le
        let i := cubicSecondEquationCurveImmersion p q hp n hq
        (iC ≫ i) Q.1 = P.1 ∧ IsIso ((iC ≫ i).residueFieldMap Q.1) ∧
        (toBase C).residueDegree Q.1 = (hypersurfaceToBase p hp).residueDegree P.1 ∧
        ∃ PQ : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)),
          iC Q.1 = PQ.1 ∧ i PQ.1 = P.1 ∧ IsIso (iC.residueFieldMap Q.1) ∧
          (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree PQ.1 =
            (hypersurfaceToBase p hp).residueDegree P.1 := by
  classical
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  dsimp only
  intro j g hgbase hgpoint a ha s hs hsnot hsP
  obtain ⟨b, hb, hDegree⟩ : ∃ b : ℕ, 0 < b ∧ n = a + b :=
    ⟨n - a, by omega, by omega⟩
  subst n
  obtain ⟨PS, hPSpoint, _hPSiso, hPSdegree⟩ :=
    selectedCurve_originalClosedPoint_of_original_chart_q_zero
      p s hp a hs P j g hgbase hgpoint hsP
  obtain ⟨C, hLowC, H, hH, hHnot, hCminLow, hCminProduct, hStrict,
      Q, hQlow, _hQlowIso, hQlowDegree⟩ :=
    lowerDegree_originalClosedPoint_exists_same_paddedProduct_component_strictDegree001
      p s hp hp0 a b hb hs hsnot PS
  let ht : (H ^ b).IsHomogeneous b := by simpa only [Nat.one_mul] using hH.pow b
  let q := s * H ^ b
  let hq : q.IsHomogeneous (a + b) := hs.mul ht
  let J := projectiveIntersectionIdeal p q hp hq
  let iC := schemeQuotientMap J C hCminProduct.le
  let i := cubicSecondEquationCurveImmersion p q hp (a + b) hq
  let iLowC := schemeQuotientMap (projectiveIntersectionIdeal p s hp hs) C hLowC
  let iLow := cubicSecondEquationCurveImmersion p s hp a hs
  have hPowerNot : H ^ b ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
    intro h
    have hpLow : Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ≤
        (projectiveIntersectionIdeal p s hp hs).toIdeal := le_sup_left
    exact hHnot (hCminLow.isPrime.mem_of_pow_mem b (hLowC (hpLow h)))
  have hNot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
    intro h
    rcases (PfaffianDescent.principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0).mem_or_mem h with h | h
    · exact hsnot h
    · exact hPowerNot h
  have hEval : q.eval₂ (algebraMap K ((hypersurface p hp).residueField P.1))
      (fun k => g (chartCoordinate (equationIdeal p hp) j k)) = 0 := by
    rw [show q = s * H ^ b from rfl, eval₂_mul, hsP, zero_mul]
  have hRoutes : iLowC ≫ iLow = iC ≫ i :=
    homogeneousComponent_twoOriginalCurveRoutes001
      (equationIdeal p hp) (projectiveIntersectionIdeal p s hp hs) J C
      le_sup_left hLowC le_sup_left hCminProduct.le
  have hOriginalPoint : (iC ≫ i) Q.1 = P.1 := by
    rw [← hRoutes]
    change iLow (iLowC Q.1) = P.1
    exact (congrArg iLow hQlow).trans hPSpoint
  letI : IsClosedImmersion iC := schemeQuotientMap_closedImmersion J C hCminProduct.le
  letI : IsClosedImmersion (iC ≫ i) := inferInstance
  have hCresidue : IsIso ((iC ≫ i).residueFieldMap Q.1) :=
    isIso_residueFieldMap_of_surjectiveOnStalks (iC ≫ i) Q.1
  have hQdegree : (toBase C).residueDegree Q.1 =
      (hypersurfaceToBase p hp).residueDegree P.1 := hQlowDegree.trans hPSdegree
  let PQ := closedPointMap iC Q
  have hPQpoint : i PQ.1 = P.1 := hOriginalPoint
  letI : IsIso (i.residueFieldMap PQ.1) :=
    isIso_residueFieldMap_of_surjectiveOnStalks i PQ.1
  have hPQdegree := residueDegree_comp_of_residueFieldMap_isIso
    i (hypersurfaceToBase p hp) PQ.1
  have hIbase : i ≫ hypersurfaceToBase p hp = toBase J :=
    cubicSecondEquationCurveImmersion_toBase p q hp (a + b) hq
  rw [hIbase, hPQpoint] at hPQdegree
  refine ⟨q, hq, hNot, hEval, C, hCminProduct, Q, hStrict,
    hOriginalPoint, hCresidue, hQdegree, PQ, rfl, hPQpoint, ?_, hPQdegree⟩
  exact isIso_residueFieldMap_of_surjectiveOnStalks iC Q.1

/-- The actual original cubic P and nonzero LOWER quotient-grade section
through its exact recovered original residue chart produce an original
DEGREE n q and SAME component/Q with strict own degree and full original
point/residue/degree equality along BOTH curve routes. No B outcome input. -/
theorem originalCubic_lowerCoordinateSection_exists_paddedDegreeCurve_sameOriginalPoint_strictComponent001
    [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (P : closedPoints (hypersurface p hp)) (n : ℕ) :
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
        (fun i => g (chartCoordinate (equationIdeal p hp) j i)) hpx), s ≠ 0 →
    ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      q.eval₂ (algebraMap K ((hypersurface p hp).residueField P.1))
        (fun i => g (chartCoordinate (equationIdeal p hp) j i)) = 0 ∧
      ∃ (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
        (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
        (Q : closedPoints (scheme C)),
        actualCurveCoordinateHilbertDegree C < 3 * n ∧
        let iC := schemeQuotientMap (projectiveIntersectionIdeal p q hp hq) C hCmin.le
        let i := cubicSecondEquationCurveImmersion p q hp n hq
        (iC ≫ i) Q.1 = P.1 ∧ IsIso ((iC ≫ i).residueFieldMap Q.1) ∧
        (toBase C).residueDegree Q.1 = (hypersurfaceToBase p hp).residueDegree P.1 ∧
        ∃ PQ : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)),
          iC Q.1 = PQ.1 ∧ i PQ.1 = P.1 ∧ IsIso (iC.residueFieldMap Q.1) ∧
          (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree PQ.1 =
            (hypersurfaceToBase p hp).residueDegree P.1 := by
  classical
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  dsimp only
  intro j g hgbase hgpoint a ha hpx s hsne
  obtain ⟨r, hr, hrP, hrClass⟩ :=
    (cubicThroughCoordinateSections_mem_iff p hp a
      (fun i => g (chartCoordinate (equationIdeal p hp) j i)) hpx s.1).mp s.2
  have hrNot : r ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
    intro h
    apply hsne
    apply Subtype.ext
    apply Subtype.ext
    exact hrClass.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  exact originalCubic_lowerPolynomial_paddedSameComponent001 p hp hp0 P n
    j g hgbase hgpoint a ha r hr hrNot hrP

end PfaffianDescent.Coray
