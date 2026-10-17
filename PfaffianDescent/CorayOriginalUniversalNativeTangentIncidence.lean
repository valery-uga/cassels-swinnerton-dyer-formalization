import PfaffianDescent.CorayUniversalNativeTangentIncidence
import PfaffianDescent.CorayOriginalJetPairSpecialization
import PfaffianDescent.CorayOriginalPairChartDimension

/-! Natural ORIGINAL whole-pair tangent incidence producer; actual generic
incidence maps are imported from their independently accepted module. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Natural ORIGINAL cubic data constructs a nonzero whole pair equation
and its universal cleared native-tangent span incidence. The map actually
annihilates Q; hence that full incidence maps through the actual T/(Q),
whose dimension<=3 is proved on the SAME whole original tensor ring. -/
theorem cubicThroughPointBasis_exists_originalUniversalNativeTangentIncidence_factorPairEquation001
    {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (hsize : finrank K L + 5 ≤ (n + 3).choose 3 - n.choose 3) :
    let I := equationIdeal p hp
    let R := ChartRing I j
    letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    let x := chartCoordinate I j
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    let a : Fin 3 → R := fun t => (pderiv (j.succAbove t) p).eval₂ (algebraMap K R) x
    ∃ (pivot : Fin 3) (A : Fin m → R) (q : Fin m → MvPolynomial (Fin 4) K)
      (P : MvPolynomial (Fin 4 ⊕ Fin 4) K) (u : R),
      u ≠ 0 ∧ Nonempty {s : PrimeSpectrum R // s ∈ PrimeSpectrum.basicOpen u} ∧
      (∀ i, (q i).IsHomogeneous n ∧ (q i).eval₂ (algebraMap K L) y = 0 ∧
        (q i).eval₂ (algebraMap K R) x = e (b i)) ∧
      let N : Fin 3 → Fin m → R := Fin.cons (fun i => e (b i))
        (fun r i => a pivot * (pderiv (j.succAbove (pivot.succAbove r)) (q i)).eval₂
          (algebraMap K R) x -
          a (pivot.succAbove r) * (pderiv (j.succAbove pivot) (q i)).eval₂ (algebraMap K R) x)
      let Q : R ⊗[K] R := ∑ i, A i ⊗ₜ[K] e (b i)
      P.eval₂ (algebraMap K (R ⊗[K] R))
        (Sum.elim (fun i => x i ⊗ₜ[K] (1 : R)) (fun i => (1 : R) ⊗ₜ[K] x i)) = Q ∧
      Q ≠ 0 ∧ originalPairTangentSpanIncidenceMap (fun i => e (b i)) N Q = 0 ∧
      ringKrullDim ((R ⊗[K] R) ⧸ Ideal.span ({Q} : Set (R ⊗[K] R))) ≤ 3 := by
  classical
  let I := equationIdeal p hp
  let R := ChartRing I j
  letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  let x := chartCoordinate I j
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  let a : Fin 3 → R := fun t => (pderiv (j.succAbove t) p).eval₂ (algebraMap K R) x
  obtain ⟨pivot, d, A, q, P, k, hRep, hP, hQ, hValue, hDirections, hu, hOpen, _hPoints⟩ :=
    cubicThroughPointBasis_exists_originalPairEquation_nativeJet_principalOpen001
      p hp hp0 n y hpy j b hsize
  let u := d * a pivot * A k
  let N : Fin 3 → Fin m → R := Fin.cons (fun i => e (b i))
    (fun r i => a pivot * (pderiv (j.succAbove (pivot.succAbove r)) (q i)).eval₂
      (algebraMap K R) x -
      a (pivot.succAbove r) * (pderiv (j.succAbove pivot) (q i)).eval₂ (algebraMap K R) x)
  let Q : R ⊗[K] R := ∑ i, A i ⊗ₜ[K] e (b i)
  have hRows : ∀ s : Fin 3, (∑ i, A i * N s i) = 0 := by
    intro s
    induction s using Fin.cases with
    | zero =>
      change (∑ i, A i * e (b i)) = 0
      simpa only [fun i => (hRep i).2.2.2] using hValue
    | succ r =>
      change (∑ i, A i *
        (a pivot * (pderiv (j.succAbove (pivot.succAbove r)) (q i)).eval₂ (algebraMap K R) x -
        a (pivot.succAbove r) * (pderiv (j.succAbove pivot) (q i)).eval₂ (algebraMap K R) x)) = 0
      calc
        _ = a pivot * (∑ i, A i * (pderiv (j.succAbove (pivot.succAbove r)) (q i)).eval₂
            (algebraMap K R) x) -
          a (pivot.succAbove r) * (∑ i, A i * (pderiv (j.succAbove pivot) (q i)).eval₂
            (algebraMap K R) x) := by
          simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
          congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
        _ = 0 := hDirections r
  have hQnonzero : Q ≠ 0 := by
    change (∑ i, A i ⊗ₜ[K] e (b i)) ≠ 0
    rw [← hP]
    exact hQ
  have hIncidence := originalPairTangentSpanIncidenceMap_pairEquation_zero001
    (K := K) (R := R) A (fun i => e (b i)) N hRows
  have hDimension := cubicOriginalWholePairChart_nonzeroEquation_ringKrullDim_le_three001
    p hp hp0 j Q hQnonzero
  refine ⟨pivot, A, q, P, u, hu, hOpen, ?_, hP, hQnonzero, hIncidence, hDimension⟩
  intro i
  exact ⟨(hRep i).1, (hRep i).2.1, (hRep i).2.2.2⟩

end PfaffianDescent.Coray
