import PfaffianDescent.CorayOriginalThreeGeometricPointKernel
import PfaffianDescent.CorayNativeRankThreePairValueCoefficients

noncomputable section
namespace PfaffianDescent.Coray
open TensorProduct Module TrivSqZeroExt
universe u
set_option autoImplicit false

/-- Actually constructed rank3 in the pair frame and nonzero pair value construct the finite
three-point hyperplane coefficients. The ACTUAL all-geometric-point kernel
then descends nonvanishing to ORIGINAL-K coefficients through the SAME A.
No hyperplane/kernel existence or original-section outcome is supplied. -/
theorem originalFiniteEtale_threeActualGeometricPoints_rankThree_pairSeparation_exists_originalCoefficients001
    {K A M : Type u} [Field K] [CommRing A] [Field M]
    [Algebra K A] [Algebra K M] [Algebra.FiniteType K A]
    [Algebra.FormallyEtale K A] [IsSepClosed M]
    (e : Fin 3 ≃ PrimeSpectrum (M ⊗[K] A)) {m : ℕ}
    (values : Fin m → A) (w : Fin m → SurfacePlaneJet M)
    (hFirst : ∀ t, originalFiniteEtaleGeometricPoint (K := K) (A := A) (M := M) (e 0) (values t) = (w t).fst)
    (hRank : finrank M (nativeSurfaceJetCoordinateSpan w) = 3)
    (ann : Fin m → M) (hJet : (∑ t, ann t • w t) = 0)
    (hPair : (∑ t, ann t * originalFiniteEtaleGeometricPoint
      (K := K) (A := A) (M := M) (e 1) (values t)) ≠ 0) :
    ∃ c : Fin m → K, (∑ t, c t • values t) = 0 ∧
      (∑ t, algebraMap K M (c t) • w t) ≠ 0 := by
  let B : Fin m → M := fun t => originalFiniteEtaleGeometricPoint
    (K := K) (A := A) (M := M) (e 1) (values t)
  let C : Fin m → M := fun t => originalFiniteEtaleGeometricPoint
    (K := K) (A := A) (M := M) (e 2) (values t)
  obtain ⟨d, h0, h1, h2, hNonzero⟩ :=
    nativeSurfaceJetThreePoint_exists_coefficients_of_rankThree_pairValue001 w hRank ann B C hJet hPair
  have hRows : originalFiniteEtaleGeometricCoefficientEvaluation (K := K) (M := M) values d = 0 := by
    apply (originalFiniteEtale_geometricCoefficientKernel_threeActualRows_iff001 e values d).mpr
    exact ⟨by simpa only [hFirst] using h0, h1, h2⟩
  let J := Fintype.linearCombination M w
  have hGeometryNonzero : ∃ c : Fin m → M,
      originalFiniteEtaleGeometricCoefficientEvaluation (K := K) (M := M) values c = 0 ∧ J c ≠ 0 := by
    exact ⟨d, hRows, by simpa only [J, Fintype.linearCombination_apply] using hNonzero⟩
  obtain ⟨c, hc, hJc⟩ :=
    originalFiniteEtaleGeometricRowKernel_nonzeroJet_exists_originalCoefficients001 values J hGeometryNonzero
  exact ⟨c, hc, by simpa only [J, Fintype.linearCombination_apply] using hJc⟩

end PfaffianDescent.Coray
