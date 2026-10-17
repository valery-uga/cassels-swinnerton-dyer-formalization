import PfaffianDescent.CorayOriginalGrassmannWholeSourceKernel
import PfaffianDescent.GrassmannianSubmoduleBaseChange
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.FiniteType

/-! SOURCE ONLY. The full possibly nonreduced divisor point ring, together
with two free original graph entries, constructs a nonzero ORIGINAL-K
polynomial vanishing on every SAME-graph line through that divisor point.
No resultant, generic line avoidance, reducedness or supplied kernel output. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
open scoped BigOperators
universe u
set_option autoImplicit false

/-- Two free first-column entries; the second column is forced by the
actual point whose second pivot coordinate is one. -/
noncomputable def originalDivisorPointGraphIncidenceMap001
    {K C : Type u} [Field K] [CommRing C] [Algebra K C]
    (z : (Fin 2 → C) × (Fin 2 → C)) :
    GrassmannianChartRing K 2 2 →ₐ[K] MvPolynomial (Fin 2) C :=
  aeval (R := K) (fun ij : Fin 2 × Fin 2 =>
    if ij.2 = 0 then X ij.1 else MvPolynomial.C (z.2 ij.1) - X ij.1 * MvPolynomial.C (z.1 0))

private theorem finiteTypeDivisorPolynomialTwo_ringKrullDim_le_three001
    {K C : Type u} [Field K] [CommRing C] [Algebra K C]
    [Algebra.FiniteType K C] (hDim : ringKrullDim C ≤ 1) :
    ringKrullDim (MvPolynomial (Fin 2) C) ≤ 3 := by
  letI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing K C
  calc
    ringKrullDim (MvPolynomial (Fin 2) C) = ringKrullDim C + 2 := by
      simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_fin,
        Nat.cast_ofNat]
    _ ≤ (1 : WithBot ℕ∞) + 2 := _root_.add_le_add hDim le_rfl
    _ = 3 := by norm_num

private theorem normalizedGraphPoint_secondColumn_eq001
    {M : Type u} [CommRing M] (T : Matrix (Fin 2) (Fin 2) M)
    (z : (Fin 2 → M) × (Fin 2 → M))
    (hz : z ∈ (Matrix.toLin' T).graph) (hz1 : z.1 1 = 1) (r : Fin 2) :
    z.2 r - T r 0 * z.1 0 = T r 1 := by
  have h := congrArg (fun v : Fin 2 → M => v r) ((LinearMap.mem_graph_iff _ _).mp hz)
  change z.2 r = ∑ i : Fin 2, T r i * z.1 i at h
  rw [Fin.sum_univ_two, hz1, mul_one] at h
  rw [h]
  ring

private theorem divisorIncidence_actualPointSpecialization_composition001
    {K C M : Type u} [Field K] [CommRing C] [CommRing M]
    [Algebra K C] [Algebra K M]
    (z : (Fin 2 → C) × (Fin 2 → C)) (f : C →ₐ[K] M)
    (T : Matrix (Fin 2) (Fin 2) M)
    (hEq : ∀ r : Fin 2, f (z.2 r) - T r 0 * f (z.1 0) = T r 1) :
    ∃ psi : MvPolynomial (Fin 2) C →ₐ[K] M,
      psi.comp (originalDivisorPointGraphIncidenceMap001 (K := K) z) =
        aeval (R := K) (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2) := by
  let psi : MvPolynomial (Fin 2) C →ₐ[K] M :=
    { eval₂Hom f.toRingHom (fun r : Fin 2 => T r 0) with
      commutes' k := by
        change (eval₂Hom f.toRingHom (fun r : Fin 2 => T r 0))
          (MvPolynomial.C (algebraMap K C k)) = algebraMap K M k
        rw [eval₂Hom_C]
        exact f.commutes k }
  refine ⟨psi, ?_⟩
  apply MvPolynomial.algHom_ext
  intro ij
  rcases ij with ⟨r, i⟩
  fin_cases i
  · simp [originalDivisorPointGraphIncidenceMap001, psi]
  · simpa [originalDivisorPointGraphIncidenceMap001, psi] using hEq r

/-- Full single-divisor-point incidence, with an ACTUAL whole kernel equation.
Every actual scalar-valued point in the SAME fixed graph specializes this
constructed equation to that graph's exact matrix. -/
theorem originalDivisorPointGraphIncidence_exists_nonzeroPolynomial_sameGraph_vanishes001
    {K C : Type u} [Field K] [CommRing C] [Algebra K C]
    [Algebra.FiniteType K C] (hDim : ringKrullDim C ≤ 1)
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2))
    (x : (Fin 2 → C) × (Fin 2 → C))
    (hx1 : (graphCoordinatePermutation C rho x).1 1 = 1) :
    ∃ q : GrassmannianChartRing K 2 2, q ≠ 0 ∧
      originalDivisorPointGraphIncidenceMap001 (K := K)
        (graphCoordinatePermutation C rho x) q = 0 ∧
      ∀ (M : Type u) [CommRing M] [Algebra K M]
        (f : C →ₐ[K] M) (T : Matrix (Fin 2) (Fin 2) M),
        graphCoefficientMap f.toRingHom x ∈ grassmannianChartSubmodule M rho T →
        (aeval (R := K) (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2)) q = 0 := by
  let z := graphCoordinatePermutation C rho x
  let phi := originalDivisorPointGraphIncidenceMap001 (K := K) z
  have hDimPoly := finiteTypeDivisorPolynomialTwo_ringKrullDim_le_three001 (K := K) hDim
  obtain ⟨q, hq0, hq⟩ :=
    grassmannLineChartMap_whole_dimension_le_three_exists_nonzero_kernel001 phi hDimPoly
  refine ⟨q, hq0, hq, ?_⟩
  intro M _ _ f T hx
  let zM := graphCoordinatePermutation M rho (graphCoefficientMap f.toRingHom x)
  have hzGraph : zM ∈ (Matrix.toLin' T).graph := by
    rw [← grassmannianChartSubmodule_own_chart M rho T]
    exact Submodule.mem_map_of_mem hx
  have hzMap : graphCoefficientMap f.toRingHom z = zM :=
    (graphCoordinatePermutation_map f.toRingHom rho x).symm
  have hz1 : zM.1 1 = 1 := by
    rw [← hzMap]
    change f (z.1 1) = 1
    rw [hx1, map_one]
  have hEq (r : Fin 2) : f (z.2 r) - T r 0 * f (z.1 0) = T r 1 := by
    have h := normalizedGraphPoint_secondColumn_eq001 T zM hzGraph hz1 r
    rw [← hzMap] at h
    exact h
  obtain ⟨psi, hComp⟩ := divisorIncidence_actualPointSpecialization_composition001 z f T hEq
  have h := congrArg psi hq
  change psi (phi q) = psi 0 at h
  rw [map_zero] at h
  rw [← AlgHom.comp_apply, hComp] at h
  exact h

end PfaffianDescent.Coray
