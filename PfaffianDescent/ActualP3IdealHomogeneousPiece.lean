import PfaffianDescent.ActualP3QuadraticRestrictionChartComparison
import PfaffianDescent.IntrinsicQuadraticIdealPiece

/-! SOURCE ONLY / UNVERIFIED. Genuine sheaf H0(I_Z(m)) identified with the
homogeneous ideal piece of its SAME original quotient embedding in any
positive degree. Nilpotents are retained; absence of irrelevant socle is
used only in this intermediate quotient lemma, not assumed by the finite
complete-intersection caller. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual restriction kernel uses the same nilpotent-sensitive chart
ideals in every positive degree, not just degree two. -/
theorem p3ActualHomogeneousRestriction_zero_iff_chart_ideal_membership
    {Z : Scheme.{u}} (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    (m : ℕ) (hm : 0 < m) (p : PS m) :
    p3ClosedImmersionHomogeneousRestrictionLinearMap i m p = 0 ↔
      ∀ j : Fin 4, p.val ∈ intrinsicQuadraticChartIdeal i j := by
  -- Both accepted map comparisons are specialized without an expected
  -- restricted-map target, before the purely ring-theoretic step.
  have hzero := p3ActualUnitSourceMorphism_zero_iff_standard_restrictions
    (K := K) (p3ClosedImmersionHomogeneousRestrictionLinearMap i m p)
  have hcharts := forall_congr' fun j : Fin 4 =>
    p3ActualHomogeneousRestriction_standard_chart_zero_iff i m hm p j
  -- Normalize just the named structure-module source on both proofs;
  -- do not simplify a functor.map together with a chart kernel.
  dsimp only [schemeModuleUnit] at hzero hcharts
  refine (hzero.trans hcharts).trans ?_
  apply forall_congr'
  intro j
  let U := intrinsicQuadraticAmbientOpen (K := K) j
  change i.app U.1
      ((Proj.awayToSection PS (X j)).hom (ambientChartEvaluation j p.val)) = 0 ↔
    (Proj.awayToSection PS (X j)).hom (ambientChartEvaluation j p.val)
      ∈ i.ker.ideal U
  rw [i.ker_apply U]
  rfl

/-- An actual source Iso preserves the genuine polynomial restriction
kernel; this follows from the actual ideal-sheaf kernel, not point supports. -/
theorem p3ActualHomogeneousRestriction_zero_iff_source_iso
    {Z Y : Scheme.{u}} (l : Z ⟶ Y) [IsIso l]
    (i : Y ⟶ Proj PS) [IsClosedImmersion i]
    (m : ℕ) (hm : 0 < m) (p : PS m) :
    p3ClosedImmersionHomogeneousRestrictionLinearMap (l ≫ i) m p = 0 ↔
      p3ClosedImmersionHomogeneousRestrictionLinearMap i m p = 0 := by
  rw [p3ActualHomogeneousRestriction_zero_iff_chart_ideal_membership (l ≫ i) m hm p,
    p3ActualHomogeneousRestriction_zero_iff_chart_ideal_membership i m hm p]
  unfold intrinsicQuadraticChartIdeal
  rw [Scheme.Hom.ker_comp_of_isIso l i]

/-- The actual original composed quotient embedding has polynomial kernel
exactly the homogeneous ideal piece, provided its irrelevant socle is zero. -/
def p3ActualHomogeneousKernelIdealPieceEquiv
    (I : HomogeneousIdeal PS)
    (hsocle : ∀ x : CoordinateRing I,
      (∀ j : Fin 4, coordinate I j * x = 0) → x = 0)
    {Z : Scheme.{u}} (l : Z ⟶ scheme I) [IsIso l]
    (m : ℕ) (hm : 0 < m) :
    (p3ClosedImmersionHomogeneousRestrictionLinearMap (l ≫ quotientProjMap I) m).ker ≃ₗ[K]
      homogeneousIdealPiece I m := by
  have hiff (p : PS m) :
      p3ClosedImmersionHomogeneousRestrictionLinearMap (l ≫ quotientProjMap I) m p = 0 ↔
        p.val ∈ I.toIdeal := by
    rw [p3ActualHomogeneousRestriction_zero_iff_source_iso l (quotientProjMap I) m hm p,
      p3ActualHomogeneousRestriction_zero_iff_chart_ideal_membership (quotientProjMap I) m hm p]
    constructor
    · intro hp
      apply homogeneous_mem_of_hypersurface_ker_le_of_no_irrelevant_annihilator
        I p.val p.property _ hsocle
      apply quotientProjMap_ker_le_of_intrinsic_chart_ideal (equationIdeal p.val p.property)
      intro j
      apply Ideal.span_le.mpr
      intro q hq
      obtain rfl := Set.mem_singleton_iff.mp hq
      exact hp j
    · intro hp j
      exact quotientProjMap_mem_intrinsicQuadraticChartIdeal I j p.val hp
  let f : (p3ClosedImmersionHomogeneousRestrictionLinearMap
      (l ≫ quotientProjMap I) m).ker →ₗ[K] homogeneousIdealPiece I m :=
    { toFun p := ⟨p.val, (hiff p.val).mp p.property⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  apply LinearEquiv.ofBijective f
  constructor
  · intro p q hpq
    apply Subtype.ext
    exact congrArg (fun z : homogeneousIdealPiece I m => z.val) hpq
  · intro p
    exact ⟨⟨p.val, (hiff p.val).mpr p.property⟩, Subtype.ext rfl⟩

/-- Genuine H0 of the actual original ideal tensor O(m), with actual ambient
K action, equals the homogeneous ideal piece; neither direction is supplied. -/
def p3ActualIdealHomogeneousPieceLinearEquiv
    (I : HomogeneousIdeal PS)
    (hsocle : ∀ x : CoordinateRing I,
      (∀ j : Fin 4, coordinate I j * x = 0) → x = 0)
    {Z : Scheme.{u}} (l : Z ⟶ scheme I) [IsIso l]
    (m : ℕ) (hm : 0 < m) :
    SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist (l ≫ quotientProjMap I) (positiveSheafOfModules PS m)) ≃ₗ[K]
      homogeneousIdealPiece I m :=
  (p3ClosedImmersionIdealHomogeneousKernelEquiv (l ≫ quotientProjMap I) m hm).trans
    (p3ActualHomogeneousKernelIdealPieceEquiv I hsocle l m hm)

end PfaffianDescent
