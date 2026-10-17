import PfaffianDescent.CorayOriginalDivisorPointGraphIncidenceGuard
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial
open scoped nonZeroDivisors
universe u
set_option autoImplicit false

private theorem nonzeroChartFunction_fullQuotient_ringKrullDim_le_one001
    {R : Type u} [CommRing R] [IsDomain R]
    (hDim : ringKrullDim R ≤ 2) (h : R) (hh : h ≠ 0) :
    ringKrullDim (R ⧸ Ideal.span {h}) ≤ 1 := by
  have hreg : h ∈ R⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hh
  have hs : ringKrullDim (R ⧸ Ideal.span {h}) + 1 ≤ (1 : WithBot ℕ∞) + 1 := by
    have h := (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hreg).trans hDim
    convert h using 1 <;> norm_num
  exact ENat.WithBot.add_le_add_one_right_iff.mp hs

/-- A nonzero actual chart function constructs a nonzero ORIGINAL-K graph
polynomial. Its nonvanishing excludes every scalar-valued divisor point in
that SAME graph, preserving the literal full quotient by that function. -/
theorem chartFunction_exists_nonzeroOriginalGraphPolynomial_forcing_sameGraph_nonzero001
    {K R : Type u} [Field K] [CommRing R] [IsDomain R]
    [Algebra K R] [Algebra.FiniteType K R]
    (hDim : ringKrullDim R ≤ 2) (h : R) (hh : h ≠ 0)
    (rho : Equiv.Perm (Fin 2 ⊕ Fin 2)) (x : (Fin 2 → R) × (Fin 2 → R))
    (hx1 : (graphCoordinatePermutation R rho x).1 1 = 1) :
    ∃ q : GrassmannianChartRing K 2 2, q ≠ 0 ∧
      ∀ (M : Type u) [CommRing M] [Algebra K M]
        (f : R →ₐ[K] M) (T : Matrix (Fin 2) (Fin 2) M),
        graphCoefficientMap f.toRingHom x ∈ grassmannianChartSubmodule M rho T →
        (aeval (R := K) (fun ij : Fin 2 × Fin 2 => T ij.1 ij.2)) q ≠ 0 → f h ≠ 0 := by
  let J : Ideal R := Ideal.span {h}
  let C := R ⧸ J
  let π : R →ₐ[K] C := Ideal.Quotient.mkₐ K J
  let xC := graphCoefficientMap π.toRingHom x
  have hDimC : ringKrullDim C ≤ 1 :=
    nonzeroChartFunction_fullQuotient_ringKrullDim_le_one001 hDim h hh
  have hxC1 : (graphCoordinatePermutation C rho xC).1 1 = 1 := by
    have hMap : graphCoordinatePermutation C rho xC =
        graphCoefficientMap π.toRingHom (graphCoordinatePermutation R rho x) :=
      graphCoordinatePermutation_map π.toRingHom rho x
    have hCoordinate := congrArg (fun v : (Fin 2 → C) × (Fin 2 → C) => v.1 1) hMap
    change (graphCoordinatePermutation C rho xC).1 1 =
      π ((graphCoordinatePermutation R rho x).1 1) at hCoordinate
    rw [hx1, map_one] at hCoordinate
    exact hCoordinate
  obtain ⟨q, hq0, _, hqPoints⟩ :=
    originalDivisorPointGraphIncidence_exists_nonzeroPolynomial_sameGraph_vanishes001
      (K := K) hDimC rho xC hxC1
  refine ⟨q, hq0, ?_⟩
  intro M _ _ f T hx hqNonzero hfZero
  have hJ : ∀ r ∈ J, f r = 0 := by
    have hle : J ≤ RingHom.ker f.toRingHom := by
      apply Ideal.span_le.mpr
      intro r hr
      obtain rfl := Set.mem_singleton_iff.mp hr
      exact hfZero
    intro r hr
    exact hle hr
  let fC : C →ₐ[K] M := Ideal.Quotient.liftₐ J f hJ
  have hxMap : graphCoefficientMap fC.toRingHom xC = graphCoefficientMap f.toRingHom x := by
    apply Prod.ext <;> funext i <;> rfl
  apply hqNonzero
  apply hqPoints M fC T
  rw [hxMap]
  exact hx

end PfaffianDescent.Coray
