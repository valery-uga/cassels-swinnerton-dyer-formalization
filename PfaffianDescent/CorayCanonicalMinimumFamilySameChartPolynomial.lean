import PfaffianDescent.CorayOriginalResidualCanonicalMinimumDegree
import PfaffianDescent.CorayHomogeneousCurveChoice

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Original closed-point degree and the Hilbert bound produce a nonzero
homogeneous section through its prescribed original residue-chart coordinates.
The chart map is unchanged and no polynomial outcome is supplied. -/
private theorem originalPoint_prescribedChart_hilbertBound_exists_nonzeroPolynomial001
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (P : closedPoints (hypersurface p hp)) (n : ℕ)
    (hSize : (hypersurfaceToBase p hp).residueDegree P.1 <
      (n + 3).choose 3 - n.choose 3) :
    letI := pointAlgebra (hypersurfaceToBase p hp) P.1
    ∀ (j : Fin 4)
      (g : ChartRing (equationIdeal p hp) j →+* (hypersurface p hp).residueField P.1),
      ∃ q0 : MvPolynomial (Fin 4) K, q0.IsHomogeneous n ∧
        q0 ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
        q0.eval₂ (algebraMap K ((hypersurface p hp).residueField P.1))
          (fun i => g (chartCoordinate (equationIdeal p hp) j i)) = 0 := by
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  intro j g
  letI : Module.Finite K ((hypersurface p hp).residueField P.1) :=
    closedPoint_moduleFinite (hypersurfaceToBase p hp) P
  have hSizeField : finrank K ((hypersurface p hp).residueField P.1) <
      (n + 3).choose 3 - n.choose 3 := by
    rw [closedPoint_finrank_eq_residueDegree (hypersurfaceToBase p hp) P]
    exact hSize
  obtain ⟨q0, hq0, hqP, hnot⟩ := exists_homogeneous_curve_equation p hp hp0 n
    (fun i => g (chartCoordinate (equationIdeal p hp) j i)) hSizeField
  exact ⟨q0, hq0, hnot, hqP⟩

/-- The accepted canonical minimum-degree family now chooses q0 through
that SAME original j/g/hpx. Canonical base/point maps, normalization, rank and
all lower-section vanishing remain attached to that exact chart. -/
theorem leastOriginalCubicPoint_largeWindow_exists_sameCanonicalChart_nonzeroPolynomial001
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
        (∀ (a : ℕ), a < n →
          ∀ s : cubicThroughCoordinateSections p hp a
            (fun i => g (chartCoordinate (equationIdeal p hp) j i)) hpx, s = 0) ∧
        ∃ q0 : MvPolynomial (Fin 4) K, q0.IsHomogeneous n ∧
          q0 ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
          q0.eval₂ (algebraMap K ((hypersurface p hp).residueField P.1))
            (fun i => g (chartCoordinate (equationIdeal p hp) j i)) = 0 := by
  classical
  letI := pointAlgebra (hypersurfaceToBase p hp) P.1
  obtain ⟨j, g, hgBase, hgPoint, hpx, hChart, hOne, hRank, hLowerSections⟩ :=
    leastOriginalCubicPoint_largeWindow_exists_canonical_minimumDegree_family001
      p hp hp0 P hPointCoprime hleast n hn hLower hUpper hPointLarge hSize
  have hSizeStrict : (hypersurfaceToBase p hp).residueDegree P.1 <
      (n + 3).choose 3 - n.choose 3 := by omega
  obtain ⟨q0, hq0, hnot, hqP⟩ :=
    originalPoint_prescribedChart_hilbertBound_exists_nonzeroPolynomial001
      p hp hp0 P n hSizeStrict j g
  exact ⟨j, g, hgBase, hgPoint, hpx, hChart, hOne, hRank, hLowerSections,
    q0, hq0, hnot, hqP⟩

end PfaffianDescent.Coray
