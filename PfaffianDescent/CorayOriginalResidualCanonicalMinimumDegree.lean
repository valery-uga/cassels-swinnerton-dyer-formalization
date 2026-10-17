import PfaffianDescent.CorayOriginalLeastWindowFinalCaseReduction
import PfaffianDescent.CorayLeastOriginalPointNoLowerSections
import PfaffianDescent.CorayBoundedOriginalSectionFamily

/-! Canonical ORIGINAL point chart and genuine minimum-degree family in
the remaining strict A(i) window. No image/basis/pencil outcome is supplied. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual least-point data and its numerical interpolation window pick
its canonical original residue chart. The actual rank>=5 and all lower
sections zero are derived from prior genuine producers, not assumptions. -/
theorem leastOriginalCubicPoint_largeWindow_exists_canonical_minimumDegree_family001
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hPointCoprime : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (n : ℕ) (hn : 1 ≤ n)
    (hLower : 1 + 3 * n.choose 2 ≤ (hypersurfaceToBase p hp).residueDegree P.1)
    (hUpper : (hypersurfaceToBase p hp).residueDegree P.1 < 1 + 3 * (n + 1).choose 2)
    (hPointLarge : 7 ≤ (hypersurfaceToBase p hp).residueDegree P.1)
    (hSize : (hypersurfaceToBase p hp).residueDegree P.1 + 5 ≤ (n + 3).choose 3 - n.choose 3) :
    letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    ∃ (j : Fin 4)
      (g : ChartRing (equationIdeal p hp) j →+* (hypersurface p hp).residueField P.1),
      g.comp (chartBaseMap (equationIdeal p hp) j) =
        algebraMap K ((hypersurface p hp).residueField P.1) ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) j =
        (hypersurface p hp).fromSpecResidueField P.1 ∧
      ∃ hpx : p.eval₂ (algebraMap K ((hypersurface p hp).residueField P.1))
          (fun i => g (chartCoordinate (equationIdeal p hp) j i)) = 0,
        Nonempty (chartι (equationIdeal p hp) j).opensRange ∧
        g (chartCoordinate (equationIdeal p hp) j j) = 1 ∧
        5 ≤ finrank K (cubicThroughCoordinateSections p hp n
          (fun i => g (chartCoordinate (equationIdeal p hp) j i)) hpx) ∧
        ∀ (a : ℕ), a < n →
          ∀ s : cubicThroughCoordinateSections p hp a
            (fun i => g (chartCoordinate (equationIdeal p hp) j i)) hpx, s = 0 := by
  classical
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  obtain ⟨j, g, hgbase, hgpoint, hpx, hRank⟩ :=
    cubicOriginalClosedPoint_exists_bounded_section_family p hp hp0 n P
  have hW : 5 ≤ finrank K (cubicThroughCoordinateSections p hp n
      (fun i => g (chartCoordinate (equationIdeal p hp) j i)) hpx) := by omega
  have hj : g (chartCoordinate (equationIdeal p hp) j j) = 1 := by
    rw [chartCoordinate_self, map_one]
  have hChart : Nonempty (chartι (equationIdeal p hp) j).opensRange := by
    let b : Spec (.of ((hypersurface p hp).residueField P.1)) :=
      IsLocalRing.closedPoint ((hypersurface p hp).residueField P.1)
    exact ⟨⟨(chartι (equationIdeal p hp) j) ((Spec.map (CommRingCat.ofHom g)) b), ⟨_, rfl⟩⟩⟩
  refine ⟨j, g, hgbase, hgpoint, hpx, hChart, hj, hW, ?_⟩
  intro a ha s
  exact leastOriginalCubicPoint_lowerCoordinateSections_eq_zero001
    p hp hp0 n hn P hPointCoprime hleast hLower hUpper hPointLarge
    j g hgbase hgpoint a ha hpx s

/-- Join the natural remaining-case reduction with its derived genuine
minimum-degree condition on the SAME canonical chart. Existing constructors
may now choose an original basis/image/pencil; none is assumed here. -/
theorem coray_leastOriginalPoint_window_eq_four_or_ten_or_canonical_minimumDegree_family001
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hPointCoprime : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (n : ℕ)
    (hLower : 1 + 3 * n.choose 2 ≤ (hypersurfaceToBase p hp).residueDegree P.1)
    (hUpper : (hypersurfaceToBase p hp).residueDegree P.1 < 1 + 3 * (n + 1).choose 2)
    : letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    ((hypersurfaceToBase p hp).residueDegree P.1 = 4 ∧ n = 2) ∨
      ((hypersurfaceToBase p hp).residueDegree P.1 = 10 ∧ n = 3) ∨
      (3 ≤ n ∧ 7 ≤ (hypersurfaceToBase p hp).residueDegree P.1 ∧
        1 + 3 * n.choose 2 < (hypersurfaceToBase p hp).residueDegree P.1 ∧
        4 ≤ 3 * (n + 1).choose 2 - (hypersurfaceToBase p hp).residueDegree P.1 ∧
        (hypersurfaceToBase p hp).residueDegree P.1 + 5 ≤ (n + 3).choose 3 - n.choose 3 ∧
        (∀ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
          q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) →
          P.1 ∈ Set.range (cubicSecondEquationCurveImmersion p q hp n hq) →
          IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))) ∧
        ∃ (j : Fin 4)
          (g : ChartRing (equationIdeal p hp) j →+* (hypersurface p hp).residueField P.1),
          g.comp (chartBaseMap (equationIdeal p hp) j) =
            algebraMap K ((hypersurface p hp).residueField P.1) ∧
          Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) j =
            (hypersurface p hp).fromSpecResidueField P.1 ∧
          ∃ hpx : p.eval₂ (algebraMap K ((hypersurface p hp).residueField P.1))
              (fun i => g (chartCoordinate (equationIdeal p hp) j i)) = 0,
            Nonempty (chartι (equationIdeal p hp) j).opensRange ∧
            g (chartCoordinate (equationIdeal p hp) j j) = 1 ∧
            5 ≤ finrank K (cubicThroughCoordinateSections p hp n
              (fun i => g (chartCoordinate (equationIdeal p hp) j i)) hpx) ∧
            ∀ (a : ℕ), a < n →
              ∀ s : cubicThroughCoordinateSections p hp a
                (fun i => g (chartCoordinate (equationIdeal p hp) j i)) hpx, s = 0
) := by
  classical
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  rcases coray_leastOriginalPoint_window_eq_four_or_ten_or_strict_integral_family001
      p hp hp0 P hPointCoprime hleast hno n hLower hUpper with hFour | hTen | hResidual
  · exact Or.inl hFour
  · exact Or.inr (Or.inl hTen)
  rcases hResidual with ⟨hn, hPointLarge, hStrict, hFreedom, hSize, hAllIntegral, hMember⟩
  right
  right
  refine ⟨hn, hPointLarge, hStrict, hFreedom, hSize, hAllIntegral, ?_⟩
  exact leastOriginalCubicPoint_largeWindow_exists_canonical_minimumDegree_family001
    p hp hp0 P hPointCoprime hleast n (by omega) hLower hUpper hPointLarge hSize

end PfaffianDescent.Coray
