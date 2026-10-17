import PfaffianDescent.CorayActualWeightedThirdSyzygies
import PfaffianDescent.CorayActualDegreeZeroChartPresentation

/-! The literal third polynomial syzygies remain exact in the ACTUAL
normalized projective chart. Source only, UNVERIFIED. This does not
identify the resulting chart complex with the global positive sheaf maps. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "A" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Unlike a general quotient module, the image of the first relation
matrix is a kernel into the polynomial domain. Cancellation therefore
constructs the needed correction at every nonzero scalar z. -/
theorem actualPolynomialRelationPair_scalar_correction
    {ι κ ι₂ : Type u} [Fintype ι] [Fintype κ] [Fintype ι₂]
    (g : ι → A) (r : κ → ι → A) (s : ι₂ → κ → A)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (hs : Submodule.span A (Set.range s) = (actualPolynomialRelationMap r).ker)
    (z : A) (hz : z ≠ 0) (c : κ → A) (b : ι → A)
    (hRc : actualPolynomialRelationMap r c = z • b) :
    ∃ (t : κ → A) (w : ι₂ → A),
      actualPolynomialRelationMap s w = c - z • t := by
  let G := actualPolynomialGeneratorMap g
  let R := actualPolynomialRelationMap r
  have hGR : G (R c) = 0 :=
    (actualPolynomialRelationMap_generatorMap_exact g r hr (R c)).mpr ⟨c, rfl⟩
  have hproduct : z * G b = 0 := by
    calc
      z * G b = G (z • b) := (map_smul G z b).symm
      _ = G (R c) := congrArg G hRc.symm
      _ = 0 := hGR
  have hb : b ∈ G.ker := LinearMap.mem_ker.mpr ((mul_eq_zero.mp hproduct).resolve_left hz)
  have hbR : b ∈ R.range := by
    rw [actualPolynomialRelationMap_range r, hr]
    exact hb
  obtain ⟨t, ht⟩ := hbR
  have hcorrected : c - z • t ∈ R.ker := by
    apply LinearMap.mem_ker.mpr
    rw [map_sub, map_smul, ht, hRc, sub_self]
  have hcorrectedS : c - z • t ∈ Submodule.span A (Set.range s) := hs.symm ▸ hcorrected
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hcorrectedS
  exact ⟨t, w, hw⟩

private theorem actualCoordinateSubOne_ne_zero (j : Fin 4) : (X j : A) - 1 ≠ 0 := by
  intro h
  have hf := congrArg (MvPolynomial.eval (fun _ : Fin 4 => (0 : K))) h
  simpa using hf

private theorem actualCoordinateSubOne_evaluation_zero (j : Fin 4) :
    ambientChartEvaluation (R := K) (σ := Fin 4) j ((X j : A) - 1) = 0 := by
  change (X j : A) - 1 ∈ RingHom.ker (ambientChartEvaluation (R := K) (σ := Fin 4) j)
  rw [ambientChartEvaluation_ker]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Genuine next normalized-chart exactness. No flatness of the
specialization A/(X_j-1), desired chart exactness or third resolution is
assumed. The original polynomial span equalities are natural generic
inputs, internally constructed at the whole-ideal boundary. -/
theorem actualDegreeZeroChartRelationPair_exact
    {ι κ ι₂ : Type u} [Fintype ι] [Fintype κ] [Fintype ι₂]
    (g : ι → A) (r : κ → ι → A) (s : ι₂ → κ → A)
    (hr : Submodule.span A (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (hs : Submodule.span A (Set.range s) = (actualPolynomialRelationMap r).ker)
    (j : Fin 4) :
    Function.Exact (actualDegreeZeroChartRelationMap j s) (actualDegreeZeroChartRelationMap j r) := by
  classical
  let f : A →+* HomogeneousLocalization.Away PS (X j) := ambientChartEvaluation j
  have hf : Function.Surjective f := ambientChartEvaluation_surjective j
  intro x
  constructor
  · intro hx
    have hpre : ∀ a, ∃ c : A, f c = x a := fun a => hf (x a)
    choose c hc using hpre
    have hzero : (fun i => f (actualPolynomialRelationMap r c i)) = 0 :=
      (actualDegreeZeroChartRelationMap_evaluate j r c).symm.trans
        ((congrArg (actualDegreeZeroChartRelationMap j r) (funext hc)).trans hx)
    have hmem : ∀ i, actualPolynomialRelationMap r c i ∈
        Ideal.span ({(X j : A) - 1} : Set A) := by
      intro i
      have hi : f (actualPolynomialRelationMap r c i) = 0 := congrFun hzero i
      change actualPolynomialRelationMap r c i ∈ RingHom.ker f at hi
      simpa only [f, ambientChartEvaluation_ker, ambientChartPresentationIdeal] using hi
    have hb : ∀ i, ∃ b : A, actualPolynomialRelationMap r c i = ((X j : A) - 1) * b := by
      intro i
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (hmem i)
      exact ⟨b, hb⟩
    choose b hb using hb
    have hRc : actualPolynomialRelationMap r c = ((X j : A) - 1) • b := funext hb
    obtain ⟨t, w, hw⟩ := actualPolynomialRelationPair_scalar_correction
      g r s hr hs ((X j : A) - 1) (actualCoordinateSubOne_ne_zero j) c b hRc
    have heval : (fun a => f ((c - ((X j : A) - 1) • t) a)) = x := by
      funext a
      change f (c a - ((X j : A) - 1) * t a) = x a
      rw [map_sub, map_mul, actualCoordinateSubOne_evaluation_zero j, zero_mul, sub_zero]
      exact hc a
    exact ⟨fun l => f (w l), (actualDegreeZeroChartRelationMap_evaluate j s w).trans
      ((congrArg (fun v : κ → A => fun a => f (v a)) hw).trans heval)⟩
  · rintro ⟨y, rfl⟩
    have hpre : ∀ l, ∃ w : A, f w = y l := fun l => hf (y l)
    choose w hw using hpre
    have hS : actualDegreeZeroChartRelationMap j s y =
        fun a => f (actualPolynomialRelationMap s w a) :=
      (congrArg (actualDegreeZeroChartRelationMap j s) (funext hw)).symm.trans
        (actualDegreeZeroChartRelationMap_evaluate j s w)
    have hSw : actualPolynomialRelationMap s w ∈ (actualPolynomialRelationMap r).ker := by
      rw [← hs, ← actualPolynomialRelationMap_range s]
      exact ⟨w, rfl⟩
    have hRS : actualPolynomialRelationMap r (actualPolynomialRelationMap s w) = 0 :=
      LinearMap.mem_ker.mp hSw
    rw [hS, actualDegreeZeroChartRelationMap_evaluate j r (actualPolynomialRelationMap s w), hRS]
    funext i
    exact map_zero f

end PfaffianDescent.Coray
