import PfaffianDescent.CorayOriginalNativeFullJetHyperplaneDictionary
import Mathlib.RingTheory.TensorProduct.Maps

/-! Whole original pair scheme tangent-span incidence factors through the
actual nonzero pair equation. All polynomial quotient nilpotents remain. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Universal THREE-coordinate span incidence over the WHOLE original
chart product. The first span row is the residue row; two rows are the
cleared actual native tangent directions. -/
def originalPairTangentSpanIncidenceIdeal
    {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    {m : ℕ} (f : Fin m → R) (N : Fin 3 → Fin m → R) :
    Ideal (MvPolynomial (Fin 3) (R ⊗[K] R)) :=
  Ideal.span (Set.range (fun i => C ((1 : R) ⊗ₜ[K] f i) -
    ∑ s : Fin 3, X s * C (N s i ⊗ₜ[K] (1 : R))))

/-- The ACTUAL coordinate homomorphism from the original pair ring into
its whole universal incidence polynomial quotient. -/
def originalPairTangentSpanIncidenceMap
    {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    {m : ℕ} (f : Fin m → R) (N : Fin 3 → Fin m → R) :
    R ⊗[K] R →+* (MvPolynomial (Fin 3) (R ⊗[K] R)) ⧸
      originalPairTangentSpanIncidenceIdeal f N :=
  (Ideal.Quotient.mk (originalPairTangentSpanIncidenceIdeal f N)).comp MvPolynomial.C

/-- A proved first-point residue-and-tangent annihilator makes its pair
polynomial an ACTUAL incidence ideal member, not merely a radical member. -/
theorem originalPairTangentSpanIncidence_pairEquation_mem001
    {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    {m : ℕ} (A f : Fin m → R) (N : Fin 3 → Fin m → R)
    (hRows : ∀ s : Fin 3, (∑ i, A i * N s i) = 0) :
    C (∑ i, A i ⊗ₜ[K] f i) ∈ originalPairTangentSpanIncidenceIdeal f N := by
  classical
  let rel : Fin m → MvPolynomial (Fin 3) (R ⊗[K] R) := fun i =>
    C ((1 : R) ⊗ₜ[K] f i) - ∑ s : Fin 3, X s * C (N s i ⊗ₜ[K] (1 : R))
  have hRowsPoly (s : Fin 3) :
      (∑ i, C (A i ⊗ₜ[K] (1 : R)) * C (N s i ⊗ₜ[K] (1 : R)) :
        MvPolynomial (Fin 3) (R ⊗[K] R)) = 0 := by
    have hTensor : (∑ i, (A i ⊗ₜ[K] (1 : R)) * (N s i ⊗ₜ[K] (1 : R)) : R ⊗[K] R) = 0 := by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [← TensorProduct.sum_tmul, hRows s, TensorProduct.zero_tmul]
    have h := congrArg (MvPolynomial.C : R ⊗[K] R →+* MvPolynomial (Fin 3) (R ⊗[K] R)) hTensor
    simpa only [map_sum, map_mul, map_zero] using h
  have hCancel :
      (∑ i, C (A i ⊗ₜ[K] (1 : R)) *
        (∑ s : Fin 3, X s * C (N s i ⊗ₜ[K] (1 : R))) :
        MvPolynomial (Fin 3) (R ⊗[K] R)) = 0 := by
    calc
      _ = ∑ s : Fin 3, X s *
          (∑ i, C (A i ⊗ₜ[K] (1 : R)) * C (N s i ⊗ₜ[K] (1 : R))) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by simp only [hRowsPoly, mul_zero, Finset.sum_const_zero]
  have hIdentity : C (∑ i, A i ⊗ₜ[K] f i) =
      ∑ i, C (A i ⊗ₜ[K] (1 : R)) * rel i := by
    simp only [rel, mul_sub, Finset.sum_sub_distrib]
    rw [hCancel, sub_zero, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← map_mul]
    congr 1
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hIdentity]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- The literal incidence map sends the whole pair equation to zero. -/
theorem originalPairTangentSpanIncidenceMap_pairEquation_zero001
    {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    {m : ℕ} (A f : Fin m → R) (N : Fin 3 → Fin m → R)
    (hRows : ∀ s : Fin 3, (∑ i, A i * N s i) = 0) :
    originalPairTangentSpanIncidenceMap f N (∑ i, A i ⊗ₜ[K] f i) = 0 := by
  change Ideal.Quotient.mk (originalPairTangentSpanIncidenceIdeal f N)
    (C (∑ i, A i ⊗ₜ[K] f i)) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (originalPairTangentSpanIncidence_pairEquation_mem001 A f N hRows)

/-- The same whole pair equation jointly records either original point
leaving a proved principal open. The diagonal multiplication map proves
the two boundary factors nonzero without a tensor-injection premise. -/
theorem originalPairEquation_withPrincipalOpenBoundary_ne_zero001
    {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    [IsDomain (R ⊗[K] R)] (Q : R ⊗[K] R) (hQ : Q ≠ 0) (u : R) (hu : u ≠ 0) :
    Q * (u ⊗ₜ[K] (1 : R)) * ((1 : R) ⊗ₜ[K] u) ≠ 0 := by
  have hLeft : (u ⊗ₜ[K] (1 : R) : R ⊗[K] R) ≠ 0 := by
    intro hZero
    have h := congrArg (Algebra.TensorProduct.lmul' K (S := R)) hZero
    exact hu (by simpa only [Algebra.TensorProduct.lmul'_apply_tmul, mul_one, map_zero] using h)
  have hRight : ((1 : R) ⊗ₜ[K] u : R ⊗[K] R) ≠ 0 := by
    intro hZero
    have h := congrArg (Algebra.TensorProduct.lmul' K (S := R)) hZero
    exact hu (by simpa only [Algebra.TensorProduct.lmul'_apply_tmul, one_mul, map_zero] using h)
  exact mul_ne_zero (mul_ne_zero hQ hLeft) hRight


end PfaffianDescent.Coray
