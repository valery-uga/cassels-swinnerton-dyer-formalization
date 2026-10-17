import PfaffianDescent.CorayOriginalNormalizedMinorClearingHelpers
import PfaffianDescent.CorayOriginalBasisRatioFieldNativeGenericMinor
import PfaffianDescent.CorayNativeSurfaceJetRowWeightedSum
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! The actual native generic minor constructs an explicit ORIGINAL
chart numerator and a genuine dense original principal open. Pointwise
native-jet specialization is a separate remaining cut. SOURCE ONLY. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Exact original polynomial evaluation and the actual native pivot
coordinate directions give the explicit cleared original direction
numerator. The coordinate-sum formula is consumed from its own producer. -/
theorem originalPolynomial_nativeDerivation_eq_clearedDirection001
    {K R F : Type u} [Field K] [CommRing R] [Field F] [Algebra K F]
    (f : K →+* R) (g : R →+* F) (hBase : g.comp f = algebraMap K F)
    (zR : Fin 4 → R) (d : Derivation K F (Fin 2 → F))
    (j : Fin 4) (grad : Fin 3 → R) (pivot : Fin 3) (hG : g (grad pivot) ≠ 0)
    (hd : ∀ i, d (g (zR i)) =
      PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j (fun t => g (grad t)) pivot i)
    (q : MvPolynomial (Fin 4) K) (r : Fin 2) :
    d (g (q.eval₂ f zR)) r =
      g (grad pivot * (pderiv (j.succAbove (pivot.succAbove r)) q).eval₂ f zR -
        grad (pivot.succAbove r) * (pderiv (j.succAbove pivot) q).eval₂ f zR) / g (grad pivot) := by
  have hEval (q' : MvPolynomial (Fin 4) K) :
      g (q'.eval₂ f zR) = q'.eval₂ (algebraMap K F) (fun i => g (zR i)) := by
    rw [hom_eval₂, hBase]
  rw [hEval, derivation_polynomial_eval₂_direction001]
  simp_rw [hd]
  rw [nativeSurfaceJetRow_weighted_sum001]
  rw [← hEval, ← hEval, map_sub, map_mul, map_mul]
  field_simp [hG]
  <;> ring

/-- Natural original data in the SAME Etrdeg2 branch constructs actual
original-K chart polynomials for the basis, a literal cleared normalized
minor numerator and a dense ORIGINAL principal open where pivot,
projection denominator and numerator are all nonzero. The full
pointwise native-jet rank statement is deliberately kept separate. -/
theorem cubicThroughPointBasis_exists_originalNativeMinorNumerator_densePrincipalOpen001
    {K L : Type u} [Field K] [CharZero K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy)) (a : Fin m) :
    let I := equationIdeal p hp
    let R := ChartRing I j
    let F := (hypersurface p hp).functionField
    letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    let g := @affineChartGenericEvaluation R (inferInstance : CommRing R)
      (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
      (chartι I j) (isOpenImmersion_chartι I j)
      (inferInstance : Nonempty (chartι I j).opensRange)
    let x : Fin m → R := fun i => cubicThroughPointChartEvaluation p hp n y hpy j (b i)
    let grad : Fin 3 → R := fun t =>
      (pderiv (j.succAbove t) p).eval₂ (chartBaseMap I j) (chartCoordinate I j)
    Algebra.trdeg K (cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a) = 2 →
    ∃ pivot : Fin 3, g (grad pivot) ≠ 0 ∧
      ∃ q : Fin m → MvPolynomial (Fin 4) K,
        (∀ i, (q i).eval₂ (chartBaseMap I j) (chartCoordinate I j) = x i) ∧
        let N : Fin m → Fin 2 → R := fun i r =>
          grad pivot * (pderiv (j.succAbove (pivot.succAbove r)) (q i)).eval₂
            (chartBaseMap I j) (chartCoordinate I j) -
          grad (pivot.succAbove r) * (pderiv (j.succAbove pivot) (q i)).eval₂
            (chartBaseMap I j) (chartCoordinate I j)
        ∃ i k : Fin m,
          let D := normalizedProjectionMinorNumerator (x i) (x k) (x a) (N i) (N k) (N a)
          let H := grad pivot * x a * D
          g D ≠ 0 ∧ g H ≠ 0 ∧
          (PrimeSpectrum.basicOpen H : TopologicalSpace.Opens (Spec (.of R))) ≠ ⊥ ∧
          Dense ((chartι I j) '' (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum R))) := by
  classical
  let I := equationIdeal p hp
  let R := ChartRing I j
  let F := (hypersurface p hp).functionField
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let g := @affineChartGenericEvaluation R (inferInstance : CommRing R)
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι I j) (isOpenImmersion_chartι I j)
    (inferInstance : Nonempty (chartι I j).opensRange)
  let x : Fin m → R := fun i => cubicThroughPointChartEvaluation p hp n y hpy j (b i)
  let grad : Fin 3 → R := fun t =>
    (pderiv (j.succAbove t) p).eval₂ (chartBaseMap I j) (chartCoordinate I j)
  let z : Fin 4 → F := fun i => g (chartCoordinate I j i)
  have hBase : g.comp (chartBaseMap I j) = algebraMap K F :=
    cubicChartGenericEvaluation_coefficient_eq p hp j
  have hGradMap (t : Fin 3) : g (grad t) =
      MvPolynomial.aeval z (pderiv (j.succAbove t) (p.map (algebraMap K F))) := by
    have h := MvPolynomial.hom_eval₂ (pderiv (j.succAbove t) p)
      (chartBaseMap I j) g (chartCoordinate I j)
    rw [hBase] at h
    simpa only [MvPolynomial.pderiv_map, MvPolynomial.aeval_eq_eval, MvPolynomial.eval_map] using h
  have hGradFamily :
      (fun t => MvPolynomial.aeval z (pderiv (j.succAbove t) (p.map (algebraMap K F)))) =
        (fun t => g (grad t)) := funext fun t => (hGradMap t).symm
  change Algebra.trdeg K (cubicThroughPointOriginalBasisRatioField p hp n y hpy j b a) = 2 → _
  intro hE
  obtain ⟨pivot, hgrad, d, hbij, hd, i, k, hminor⟩ :=
    cubicThroughPointOriginalBasisRatioField_exists_nativeGeneric_minor_of_trdeg_two001
      p hp hp0 n y hpy j b a hE
  rw [hGradFamily] at hd
  have hG : g (grad pivot) ≠ 0 := by rwa [hGradMap pivot]
  choose q hq using fun t : Fin m => eval₂_chartCoordinate_surjective I j (x t)
  have hrep (t : Fin m) : (q t).eval₂ (chartBaseMap I j) (chartCoordinate I j) = x t := hq t
  let N : Fin m → Fin 2 → R := fun t r =>
    grad pivot * (pderiv (j.succAbove (pivot.succAbove r)) (q t)).eval₂
      (chartBaseMap I j) (chartCoordinate I j) -
    grad (pivot.succAbove r) * (pderiv (j.succAbove pivot) (q t)).eval₂
      (chartBaseMap I j) (chartCoordinate I j)
  have hN (t : Fin m) (r : Fin 2) : d (g (x t)) r = g (N t r) / g (grad pivot) := by
    rw [← hrep t]
    exact originalPolynomial_nativeDerivation_eq_clearedDirection001
      (chartBaseMap I j) g hBase (chartCoordinate I j) d j grad pivot hG hd (q t) r
  have ha : g (x a) ≠ 0 := cubicThroughPointBasisGenericCoordinates_ne_zero p hp hp0 n y hpy j b a
  let D := normalizedProjectionMinorNumerator (x i) (x k) (x a) (N i) (N k) (N a)
  have hD : g D ≠ 0 :=
    derivation_normalized_minor_originalNumerator_ne_zero001 g d
      (grad pivot) (x i) (x k) (x a) (N i) (N k) (N a) hG ha (hN i) (hN k) (hN a) hminor
  let H := grad pivot * x a * D
  have hH : g H ≠ 0 := by
    change g (grad pivot * x a * D) ≠ 0
    rw [map_mul, map_mul]
    exact mul_ne_zero (mul_ne_zero hG ha) hD
  have hOpen : (PrimeSpectrum.basicOpen H : TopologicalSpace.Opens (Spec (.of R))) ≠ ⊥ := by
    intro hbot
    have hnil : IsNilpotent H := (PrimeSpectrum.basicOpen_eq_bot_iff H).mp hbot
    exact hH (hnil.map g).eq_zero
  have hNonempty : (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum R)).Nonempty :=
    (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hOpen
  letI : IsIntegral (scheme I) := by
    change IsIntegral (hypersurface p hp)
    infer_instance
  have hDense : Dense ((chartι I j) '' (PrimeSpectrum.basicOpen H : Set (PrimeSpectrum R))) :=
    ((chartι I j).isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen H).isOpen).dense
      (hNonempty.image (chartι I j))
  exact ⟨pivot, hG, q, hrep, i, k, hD, hH, hOpen, hDense⟩

end PfaffianDescent.Coray
end
