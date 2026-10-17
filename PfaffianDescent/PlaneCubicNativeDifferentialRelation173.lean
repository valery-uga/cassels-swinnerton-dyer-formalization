import PfaffianDescent.CorayPlaneCubicJacobianSmooth
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.Tactic.FinCases

/-! SOURCE ONLY173. Actual native Kähler relation of the SAME normalized
plane-cubic chart. The equation and normalization produce the relation;
no cotangent presentation or residue compatibility is supplied. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
variable {K : Type u} [CommRing K]

/-- Polynomial chain rule for an actual derivation after coefficient
evaluation. This is an ordinary finite polynomial identity, not a
derivative-relation input to a geometric caller. -/
theorem derivation_eval₂_eq_sum_pderiv_smul173
    {R M : Type u} [CommRing R] [Algebra K R]
    [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower K R M]
    (D : Derivation K R M) (y : Fin 3 → R) (p : MvPolynomial (Fin 3) K) :
    D (p.eval₂ (algebraMap K R) y) =
      ∑ i : Fin 3, (pderiv i p).eval₂ (algebraMap K R) y • D (y i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [pderiv_C]
  | add p q hp hq =>
      simp only [eval₂_add, map_add, hp, hq, add_smul, Finset.sum_add_distrib]
  | mul_X p k hp =>
      simp only [eval₂_mul, eval₂_X, D.leibniz, hp, pderiv_mul, eval₂_add, add_smul]
      rw [Finset.sum_add_distrib]
      have hfirst :
          (∑ i : Fin 3, ((pderiv i p).eval₂ (algebraMap K R) y * y k) • D (y i)) =
            y k • ∑ i : Fin 3, (pderiv i p).eval₂ (algebraMap K R) y • D (y i) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_comm, mul_smul]
      have hsecond :
          (∑ i : Fin 3, (p.eval₂ (algebraMap K R) y *
            (pderiv i (X k)).eval₂ (algebraMap K R) y) • D (y i)) =
              p.eval₂ (algebraMap K R) y • D (y k) := by
        rw [Finset.sum_eq_single k]
        · simp
        · intro i hi hik
          rw [pderiv_X_of_ne (Ne.symm hik)]
          simp
        · intro hk
          exact (hk (Finset.mem_univ k)).elim
      rw [hfirst, hsecond]
      exact add_comm _ _

/-- The finite combinatorial reduction is separated from all chart and
Kähler terms, so its proof never splits their dependent coordinate data. -/
theorem finThree_sum_two_terms_of_distinguished_zero173
    {M : Type u} [AddCommMonoid M] (g : Fin 3 → M)
    (j i k : Fin 3) (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k)
    (hj : g j = 0) (hsum : ∑ a : Fin 3, g a = 0) : g i + g k = 0 := by
  fin_cases j <;> fin_cases i <;> fin_cases k <;>
    simp_all [Fin.sum_univ_three, add_comm] <;>
    exact (add_comm _ _).trans hsum

section ActualChart
attribute [local instance] MvPolynomial.gradedAlgebra
variable (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (j : Fin 3)
noncomputable local instance nativePlaneChartAlgebra173 :
    Algebra K (ChartRing (equationIdeal p hp) j) :=
  (chartBaseMap (equationIdeal p hp) j).toAlgebra

/-- In every genuine chart algebra extension, the actual polynomial
equation differentiates to zero in the actual native Kähler module. -/
theorem planeChart_nativeKaehler_sum_relation173
    {R : Type u} [CommRing R] [Algebra K R]
    (f : ChartRing (equationIdeal p hp) j →ₐ[K] R) :
    (∑ i : Fin 3,
      f ((pderiv i p).eval₂ (chartBaseMap (equationIdeal p hp) j)
        (chartCoordinate (equationIdeal p hp) j)) •
      KaehlerDifferential.D K R (f (chartCoordinate (equationIdeal p hp) j i))) = 0 := by
  let I := equationIdeal p hp
  let y : Fin 3 → R := fun i => f (chartCoordinate I j i)
  have hcoeff : f.toRingHom.comp (chartBaseMap I j) = algebraMap K R := by
    ext c
    exact f.commutes c
  have hzero : p.eval₂ (algebraMap K R) y = 0 := by
    have h := congrArg f (eval₂_chartCoordinate_eq_zero_of_mem I j p
      (Ideal.subset_span (Set.mem_singleton p)))
    change f.toRingHom (p.eval₂ (chartBaseMap I j) (chartCoordinate I j)) =
      f.toRingHom 0 at h
    rw [MvPolynomial.hom_eval₂, map_zero, hcoeff] at h
    exact h
  have hchain := derivation_eval₂_eq_sum_pderiv_smul173
    (KaehlerDifferential.D K R) y p
  rw [hzero, map_zero] at hchain
  have hpartial (i : Fin 3) :
      (pderiv i p).eval₂ (algebraMap K R) y =
        f ((pderiv i p).eval₂ (chartBaseMap I j) (chartCoordinate I j)) := by
    change (pderiv i p).eval₂ (algebraMap K R) y =
      f.toRingHom ((pderiv i p).eval₂ (chartBaseMap I j) (chartCoordinate I j))
    rw [MvPolynomial.hom_eval₂, hcoeff]
    rfl
  simp_rw [hpartial] at hchain
  exact hchain.symm

/-- The two non-normalizing coordinate differentials obey the literal
two-partial relation. The distinguished coordinate is exactly1 in the
SAME chart, so its differential is zero. -/
theorem planeChart_nativeKaehler_two_partial_relation173
    {R : Type u} [CommRing R] [Algebra K R]
    (f : ChartRing (equationIdeal p hp) j →ₐ[K] R)
    (i k : Fin 3) (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k) :
    f (plane_chartPDeriv p hp j ⟨i, hij⟩) •
        KaehlerDifferential.D K R (f (chartCoordinate (equationIdeal p hp) j i)) +
      f (plane_chartPDeriv p hp j ⟨k, hkj⟩) •
        KaehlerDifferential.D K R (f (chartCoordinate (equationIdeal p hp) j k)) = 0 := by
  let g : Fin 3 → KaehlerDifferential K R := fun a =>
    f ((pderiv a p).eval₂ (chartBaseMap (equationIdeal p hp) j)
      (chartCoordinate (equationIdeal p hp) j)) •
      KaehlerDifferential.D K R (f (chartCoordinate (equationIdeal p hp) j a))
  have hsum : ∑ a : Fin 3, g a = 0 :=
    planeChart_nativeKaehler_sum_relation173 p hp j f
  have hj : g j = 0 := by
    dsimp only [g]
    rw [chartCoordinate_self, map_one,
      (KaehlerDifferential.D K R).map_one_eq_zero, smul_zero]
  change g i + g k = 0
  exact finThree_sum_two_terms_of_distinguished_zero173 g j i k hij hkj hik hj hsum

end ActualChart
end PfaffianDescent.Coray
