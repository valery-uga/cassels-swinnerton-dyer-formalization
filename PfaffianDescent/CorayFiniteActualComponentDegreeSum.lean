import PfaffianDescent.CorayRelevantPrimeComponentHyperplaneDegree
import PfaffianDescent.CorayFiniteUnionNewProjectiveComponentIntersectionFinite
import PfaffianDescent.CorayHomogeneousHilbertFunctionAdditivity
import Mathlib.Tactic.Linarith

/-!
# Degree additivity for the actual finite component union

Each actual relevant minimal component over the SAME ideal I has a constructed
hyperplane cut and actual Hilbert increment. At every induction step, genuine
component geometry constructs finiteness of the WHOLE intersection scheme.
Every-grade exact additivity and actual finite stabilization then construct
the union increment. The original cubic/q Hilbert bound controls its sum.
No finite intersection, degree, common slope or additivity premise is supplied.
SOURCE ONLY / UNVERIFIED; root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem actualCoordinateDegree_eq_derived_increment
    {K : Type u} [Field K]
    (U : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (μ N : ℕ)
    (hN : ∀ m, N ≤ m →
      finrank K (grading U (m + 1)) = finrank K (grading U m) + μ) :
    actualCurveCoordinateHilbertDegree U = μ := by
  classical
  have hex : ∃ ν : ℕ, ∃ M : ℕ, ∀ m, M ≤ m →
      finrank K (grading U (m + 1)) = finrank K (grading U m) + ν := ⟨μ, N, hN⟩
  change (if h : ∃ ν : ℕ, ∃ M : ℕ, ∀ m, M ≤ m →
    finrank K (grading U (m + 1)) = finrank K (grading U m) + ν
    then Nat.find h else 0) = μ
  rw [dif_pos hex]
  obtain ⟨M, hM⟩ := Nat.find_spec hex
  have hfirst := hN (max N M) (le_max_left _ _)
  have hsecond := hM (max N M) (le_max_right _ _)
  omega

/-- The ACTUAL finite scheme-theoretic union of distinct relevant minimal
components of I has degree equal to the SUM of their OWN degrees, bounded by
the original 3n. Actual Hilbert increments are constructed internally. I may
be the coefficient extension of the original selected prime, and no component
is required to be minimal over the WHOLE cubic/q intersection. The empty
family is allowed and has the literal top ideal and degree zero. -/
theorem selectedProjectiveFiniteActualComponents_degree_sum_bound
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hPQI : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ I.toIdeal)
    (F : Finset (HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    (hFmin : ∀ C ∈ F, C.toIdeal ∈ I.toIdeal.minimalPrimes)
    (hFrel : ∀ C ∈ F,
      ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ C) :
    actualCurveCoordinateHilbertDegree (F.inf id) =
        ∑ C ∈ F, actualCurveCoordinateHilbertDegree C ∧
      (∑ C ∈ F, actualCurveCoordinateHilbertDegree C) ≤ 3 * n ∧
      ∃ N : ℕ, ∀ m, N ≤ m →
        finrank K (grading (F.inf id) (m + 1)) = finrank K (grading (F.inf id) m) +
          ∑ C ∈ F, actualCurveCoordinateHilbertDegree C := by
  classical
  have hinc : ∀ G : Finset (HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)),
      (∀ C ∈ G, C.toIdeal ∈ I.toIdeal.minimalPrimes) →
      (∀ C ∈ G,
        ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ C) →
      ∃ N : ℕ, ∀ m, N ≤ m →
        finrank K (grading (G.inf id) (m + 1)) = finrank K (grading (G.inf id) m) +
          ∑ C ∈ G, actualCurveCoordinateHilbertDegree C := by
    intro G
    induction G using Finset.induction_on with
    | empty =>
      intro _ _
      let T : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) := ⊤
      letI : Subsingleton (CoordinateRing T) :=
        Ideal.Quotient.subsingleton_iff.mpr (HomogeneousIdeal.toIdeal_top)
      have hzero (m : ℕ) : finrank K (grading T m) = 0 :=
        Module.finrank_zero_of_subsingleton
      have hempty : (∅ : Finset (HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))).inf id = T :=
        Finset.inf_empty
      have hemptyZero (m : ℕ) :
          finrank K (grading ((∅ : Finset (HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))).inf id) m) = 0 :=
        (congrArg (fun J => finrank K (grading J m)) hempty).trans (hzero m)
      refine ⟨0, fun m _ => ?_⟩
      simpa only [Finset.sum_empty, Nat.add_zero] using
        (hemptyZero (m + 1)).trans (hemptyZero m).symm
    | @insert C G hnew ih =>
      intro hGmin hGrel
      have hC : C.toIdeal ∈ I.toIdeal.minimalPrimes := hGmin C (Finset.mem_insert_self _ _)
      have hCrel := hGrel C (Finset.mem_insert_self _ _)
      have hmin : ∀ D ∈ G, D.toIdeal ∈ I.toIdeal.minimalPrimes :=
        fun D hD => hGmin D (Finset.mem_insert_of_mem hD)
      have hrel : ∀ D ∈ G,
          ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ D :=
        fun D hD => hGrel D (Finset.mem_insert_of_mem hD)
      obtain ⟨NU, hNU⟩ := ih hmin hrel
      letI : C.toIdeal.IsPrime := hC.isPrime
      obtain ⟨_H, _hH, _hnotH, _hfiniteH, _hdegreeH, _hboundH, NC, hNC⟩ :=
        selectedProjectiveRelevantPrime_exists_hyperplane_degree_bound
          p q hp hp0 n hq hnot C hCrel (hPQI.trans hC.le)
      letI : IsFinite (toBase (G.inf id ⊔ C)) :=
        selectedProjectiveFiniteUnion_newComponent_sup_isFinite
          p q hp hp0 n hq hnot I C hPQI G hC hCrel hmin hrel hnew
      obtain ⟨NS, hNS⟩ :=
        finiteProjectiveHomogeneousIdeal_hilbertFunction_eventually_eq_rank (G.inf id ⊔ C)
      have hUeq : (insert C G).inf id = G.inf id ⊓ C := by
        rw [Finset.inf_insert]
        exact inf_comm _ _
      let N := max NU (max NC NS)
      refine ⟨N, fun m hm => ?_⟩
      have hNUm : NU ≤ m := (le_max_left NU (max NC NS)).trans hm
      have hNCm : NC ≤ m := (le_max_left NC NS).trans ((le_max_right NU (max NC NS)).trans hm)
      have hNSm : NS ≤ m := (le_max_right NC NS).trans ((le_max_right NU (max NC NS)).trans hm)
      have hsum0 := homogeneousCoordinateGrade_union_intersection_finrank_additivity (G.inf id) C m
      have hsum1 := homogeneousCoordinateGrade_union_intersection_finrank_additivity (G.inf id) C (m + 1)
      rw [hNS m hNSm] at hsum0
      rw [hNS (m + 1) (by omega), hNU m hNUm, hNC m hNCm] at hsum1
      have hdim1 := congrArg (fun J => finrank K (grading J (m + 1))) hUeq
      have hdim0 := congrArg (fun J => finrank K (grading J m)) hUeq
      rw [hdim1, hdim0, Finset.sum_insert hnew]
      omega
  obtain ⟨N, hN⟩ := hinc F hFmin hFrel
  let U := F.inf id
  let μ := ∑ C ∈ F, actualCurveCoordinateHilbertDegree C
  have hdegree : actualCurveCoordinateHilbertDegree U = μ :=
    actualCoordinateDegree_eq_derived_increment U μ N hN
  have htoIdeal : U.toIdeal = F.inf (fun C => C.toIdeal) := by
    simp only [U, Finset.inf_eq_iInf, HomogeneousIdeal.toIdeal_iInf, id_eq]
  have hPQU : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ U.toIdeal := by
    rw [htoIdeal]
    exact Finset.le_inf (fun C hC => hPQI.trans (hFmin C hC).le)
  let B := max N (n + 3)
  have hB : N ≤ B := le_max_left _ _
  have hAffine : ∀ t : ℕ, finrank K (grading U (B + t)) =
      finrank K (grading U B) + t * μ := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hstep := hN (B + t) (by omega)
      change finrank K (grading U (B + t + 1)) = finrank K (grading U (B + t)) + μ at hstep
      rw [ih] at hstep
      have hindex : finrank K (grading U (B + Nat.succ t)) =
          finrank K (grading U (B + t + 1)) :=
        (congrArg (fun d => finrank K (grading U d)) (Nat.add_assoc B t 1)).symm
      simpa only [Nat.succ_mul, Nat.add_assoc] using hindex.trans hstep
  have hbound : μ ≤ 3 * n := by
    by_contra hle
    have hgap : 3 * n + 1 ≤ μ := by omega
    let t := 3 * n * B + 1
    let d := B + t - (n + 3)
    have hidx : d + n + 3 = B + t := by dsimp only [d, B]; omega
    have hdim : finrank K (grading U (d + n + 3)) = finrank K (grading U (B + t)) :=
      congrArg (fun m => finrank K (grading U m)) hidx
    have hwhole := selectedProjectiveComponent_hilbertFunction_linearBound
      p q hp hp0 n hn hq hnot U hPQU d
    rw [hdim, hidx, hAffine t] at hwhole
    have hproduct := Nat.mul_le_mul_left t hgap
    dsimp only [t] at hwhole hproduct
    nlinarith only [hwhole, hproduct, Nat.zero_le (finrank K (grading U B)),
      Nat.zero_le (3 * n * (n - 1))]
  exact ⟨hdegree, hbound, N, hN⟩

end PfaffianDescent.Coray
