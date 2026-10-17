import PfaffianDescent.OriginalThreeQuadricCohomologicalHZero

/-! SOURCE ONLY / UNVERIFIED. Actual containment in the cubic produces an
actual ideal-global section, then the cohomological augmentation isomorphism
produces the literal three-linear-form decomposition. No ideal section,
polynomial ideal membership or decomposition is supplied as a certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K
local notation "base" => ambientToBase (R := K) (σ := Fin 4)

/-- Scheme-theoretic cubic containment kills the actual homogeneous
restriction. The original structure sheaf, including nilpotents, is used. -/
theorem p3OriginalContainedCubic_restriction_zero
    {Z : Scheme.{u}} (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    (F : PS 3)
    (hF : (hypersurfaceToAmbient F.val F.property).ker ≤ i.ker) :
    p3ClosedImmersionHomogeneousRestrictionLinearMap i 3 F = 0 := by
  apply (p3ActualHomogeneousRestriction_zero_iff_chart_ideal_membership
    i 3 (by decide) F).mpr
  intro j
  let U := intrinsicQuadraticAmbientOpen (K := K) j
  have hown := quotientProjMap_mem_intrinsicQuadraticChartIdeal
    (equationIdeal F.val F.property) j F.val
    (by
      change F.val ∈ Ideal.span ({F.val} : Set (MvPolynomial (Fin 4) K))
      exact Ideal.subset_span (Set.mem_singleton F.val))
  change (Proj.awayToSection PS (X j)).hom
    (ambientChartEvaluation j F.val) ∈ i.ker.ideal U
  apply (Scheme.IdealSheafData.ideal_mono hF) U
  exact hown

/-- The cubic gives a genuine H0(I_originalZ(3)) section. Its ambient
image and polynomial are proved below, rather than assumed in a caller. -/
def p3OriginalContainedCubic_idealGlobalSection
    {Z : Scheme.{u}} (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    (F : PS 3)
    (hF : (hypersurfaceToAmbient F.val F.property).ker ≤ i.ker) :
    SchemeModuleGlobalSectionsOver base
      (closedImmersionIdealTwist i (positiveSheafOfModules PS 3)) :=
  (p3ClosedImmersionIdealHomogeneousKernelEquiv i 3 (by decide)).symm
    ⟨F, p3OriginalContainedCubic_restriction_zero i F hF⟩

theorem p3OriginalContainedCubic_idealGlobalSection_polynomial
    {Z : Scheme.{u}} (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    (F : PS 3)
    (hF : (hypersurfaceToAmbient F.val F.property).ker ≤ i.ker) :
    (p3ClosedImmersionIdealHomogeneousKernelEquiv i 3 (by decide)
      (p3OriginalContainedCubic_idealGlobalSection i F hF)).val = F := by
  exact congrArg Subtype.val
    ((p3ClosedImmersionIdealHomogeneousKernelEquiv i 3 (by decide)).apply_symm_apply
      ⟨F, p3OriginalContainedCubic_restriction_zero i F hF⟩)

/-- Its actual sheaf inclusion is the actual original cubic global section. -/
theorem p3OriginalContainedCubic_idealGlobalSection_ambient
    {Z : Scheme.{u}} (i : Z ⟶ Proj PS) [IsClosedImmersion i]
    (F : PS 3)
    (hF : (hypersurfaceToAmbient F.val F.property).ker ≤ i.ker) :
    p3OriginalContainedCubic_idealGlobalSection i F hF ≫
      (closedImmersionIdealTwistSequence i (positiveSheafOfModules PS 3)).f ≫
      (schemeModuleTensorUnitLeftIso (positiveSheafOfModules PS 3)).hom =
      p3HomogeneousGlobalSectionLinearMap K 3 F := by
  rw [← p3ClosedImmersionIdealHomogeneousKernelEquiv_embedding i 3 (by decide)
    (p3OriginalContainedCubic_idealGlobalSection i F hF),
    p3OriginalContainedCubic_idealGlobalSection_polynomial]

/-- The manuscript's final F step, through the SAME actual induced H0
augmentation and its independently proved long-exact-cohomology bijection. -/
theorem p3OriginalThreeQuadricContainedCubic_decomposition_by_cohomology
    (f g h : PS 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property))]
    {Z : Scheme.{u}}
    (l : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property)) [IsClosedImmersion l]
    (hZ : AllCharacteristics.finiteSchemeRank (l ≫ toBase
      (tripleCompleteIntersectionHomogeneousIdeal f.val g.val h.val
        f.property g.property h.property)) = 8)
    (F : PS 3)
    (hF : (hypersurfaceToAmbient F.val F.property).ker ≤
      (l ≫ quotientProjMap (tripleCompleteIntersectionHomogeneousIdeal
        f.val g.val h.val f.property g.property h.property)).ker) :
    ∃ H : PS 1 × PS 1 × PS 1,
      F.val = f.val * H.1.val + g.val * H.2.1.val + h.val * H.2.2.val := by
  let T := tripleCompleteIntersectionHomogeneousIdeal f.val g.val h.val
    f.property g.property h.property
  let i := l ≫ quotientProjMap T
  let sF := p3OriginalContainedCubic_idealGlobalSection i F hF
  obtain ⟨s, hs⟩ :=
    (p3OriginalThreeQuadricOThreeGlobalAugmentation_cohomological_bijective
      f g h l hZ).2 sF
  let H := p3ActualPositiveOneTripleHomogeneousEquiv s
  have hp := p3OriginalThreeQuadricOThreeGlobalAugmentation_polynomial f g h l hZ s
  rw [hs, p3OriginalContainedCubic_idealGlobalSection_polynomial] at hp
  refine ⟨H, ?_⟩
  exact congrArg (fun p : PS 3 => p.val) hp

end PfaffianDescent
