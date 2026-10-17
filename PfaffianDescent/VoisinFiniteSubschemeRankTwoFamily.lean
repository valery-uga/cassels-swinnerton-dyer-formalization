import AllCharacteristics.DisjointFiniteSubschemeUnionCycle
import AllCharacteristics.FiniteSubschemeRationalCycleFamily
import PfaffianDescent.VoisinCycleArithmetic
import PfaffianDescent.FiniteSubschemeResidualDisjoint
import PfaffianDescent.VoisinDegreeTenClosedPointStart
import PfaffianDescent.SerreExtensionPencilProjectiveLine

/-!
# The rank-two family in Voisin's degree-ten reduction

Voisin's rank-two construction has an eleven-point fiber and a special fiber
which is the disjoint union of the chosen degree-three line section and an
eight-point residual scheme.  A finite-flat pencil with those scheme-level
fibers gives the required rational-cycle family, with the endpoint equalities
derived from the scheme data.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

/-- The special fiber of the rank-two family: a disjoint degree-eight datum
together with the degree-three line-section datum. -/
noncomputable def degreeEightAndDegreeThreeDatum
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (D₈ : FiniteSubschemeDatum f 8) (D₃ : FiniteSubschemeDatum f 3)
    (hdisjoint : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₃))) :
    FiniteSubschemeDatum f 11 := by
  simpa using finiteSubschemeDatumOfTwoDisjointData f D₈ D₃ hdisjoint

/-- The canonical cycle of the rank-two special fiber is the reference
degree-three cycle plus the degree-eight residual cycle. -/
theorem degreeEightAndDegreeThreeDatum_cycle
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (D₈ : FiniteSubschemeDatum f 8) (D₃ : FiniteSubschemeDatum f 3)
    (hdisjoint : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₃))) :
    finiteSubschemeDatumCycle f (degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint) =
      finiteSubschemeDatumCycle f D₃ + finiteSubschemeDatumCycle f D₈ := by
  rw [show degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint =
      finiteSubschemeDatumOfTwoDisjointData f D₈ D₃ hdisjoint by rfl]
  rw [finiteSubschemeDatumCycleOfTwoDisjointData f D₈ D₃ hdisjoint]
  exact add_comm _ _

/-- A finite-flat pencil from the disjoint degree-eight-plus-degree-three
fiber to the degree-eleven datum supplies the rational-cycle family required
by the rank-two step. -/
noncomputable def rankTwoResidualFamilyOfPencil
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (D₈ : FiniteSubschemeDatum f 8) (D₃ : FiniteSubschemeDatum f 3)
    (D₁₁ : FiniteSubschemeDatum f 11)
    (hdisjoint : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (P : FiniteSubschemeDatumPencil f 11
      (degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint) D₁₁) :
    RationalCycleFamily f :=
  FiniteSubschemeDatumPencil.toRationalCycleFamily f P

/-- The zero fiber of the rank-two pencil is the degree-three reference
cycle plus the degree-eight residual cycle. -/
theorem rankTwoResidualFamilyOfPencil_zero
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (D₈ : FiniteSubschemeDatum f 8) (D₃ : FiniteSubschemeDatum f 3)
    (D₁₁ : FiniteSubschemeDatum f 11)
    (hdisjoint : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (P : FiniteSubschemeDatumPencil f 11
      (degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint) D₁₁) :
    (rankTwoResidualFamilyOfPencil f D₈ D₃ D₁₁ hdisjoint P).fiberCycle false =
      finiteSubschemeDatumCycle f D₃ + finiteSubschemeDatumCycle f D₈ := by
  rw [show rankTwoResidualFamilyOfPencil f D₈ D₃ D₁₁ hdisjoint P =
      FiniteSubschemeDatumPencil.toRationalCycleFamily f P by rfl]
  rw [FiniteSubschemeDatumPencil.fiberCycle_zero f P]
  exact degreeEightAndDegreeThreeDatum_cycle f D₈ D₃ hdisjoint

/-- The infinity fiber of the rank-two pencil is the degree-eleven datum. -/
theorem rankTwoResidualFamilyOfPencil_infinity
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (D₈ : FiniteSubschemeDatum f 8) (D₃ : FiniteSubschemeDatum f 3)
    (D₁₁ : FiniteSubschemeDatum f 11)
    (hdisjoint : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (P : FiniteSubschemeDatumPencil f 11
      (degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint) D₁₁) :
    (rankTwoResidualFamilyOfPencil f D₈ D₃ D₁₁ hdisjoint P).fiberCycle true =
      finiteSubschemeDatumCycle f D₁₁ := by
  rw [show rankTwoResidualFamilyOfPencil f D₈ D₃ D₁₁ hdisjoint P =
      FiniteSubschemeDatumPencil.toRationalCycleFamily f P by rfl]
  exact FiniteSubschemeDatumPencil.fiberCycle_infinity f P

/-- The rank-two pencil has exactly the endpoint form used by Voisin's
degree-ten cycle calculation. -/
theorem exists_rankTwoResidualFamily_of_pencil
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (D₈ : FiniteSubschemeDatum f 8) (D₃ : FiniteSubschemeDatum f 3)
    (D₁₁ : FiniteSubschemeDatum f 11)
    (hdisjoint : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (P : FiniteSubschemeDatumPencil f 11
      (degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint) D₁₁) :
    ∃ F : RationalCycleFamily f,
      F.fiberCycle false = finiteSubschemeDatumCycle f D₃ + finiteSubschemeDatumCycle f D₈ ∧
      F.fiberCycle true = finiteSubschemeDatumCycle f D₁₁ := by
  refine ⟨rankTwoResidualFamilyOfPencil f D₈ D₃ D₁₁ hdisjoint P, ?_, ?_⟩
  · exact rankTwoResidualFamilyOfPencil_zero f D₈ D₃ D₁₁ hdisjoint P
  · exact rankTwoResidualFamilyOfPencil_infinity f D₈ D₃ D₁₁ hdisjoint P

/-- A global normalized Serre pencil on the projective-line parameter space
provides the middle rational-cycle family in Voisin's construction.  This
connects the affine-chart zero-locus construction to the pre-existing
finite-subscheme endpoint calculation. -/
theorem exists_rankTwoResidualFamily_of_projectiveLinePencilData
    {K : Type u} [Field K] {X : Scheme.{u}}
    {M : SheafOfModules.{u} X.ringCatSheaf}
    {e : SerreExtensionData X M}
    (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionData.SerreExtensionPencilSeed e)
    (D₈ : FiniteSubschemeDatum f 8) (D₃ : FiniteSubschemeDatum f 3)
    (D₁₁ : FiniteSubschemeDatum f 11)
    (hdisjoint : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (P : SerreExtensionData.SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
      f C seed 11 (degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint) D₁₁) :
    ∃ F : RationalCycleFamily f,
      F.fiberCycle false = finiteSubschemeDatumCycle f D₃ + finiteSubschemeDatumCycle f D₈ ∧
      F.fiberCycle true = finiteSubschemeDatumCycle f D₁₁ := by
  exact exists_rankTwoResidualFamily_of_pencil f D₈ D₃ D₁₁ hdisjoint
    (SerreExtensionData.SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData.toFiniteSubschemeDatumPencil
      f C seed P)

/-- The normalized Serre-pencil construction can be used for Voisin's
rank-two residual step as soon as its literal endpoint zero schemes have
been identified with the intended degree-eight-plus-degree-three and
degree-eleven subschemes.  The endpoint identifications are isomorphisms over
the cubic surface, as supplied by the geometric complete-intersection
construction. -/
theorem exists_rankTwoResidualFamily_of_projectiveLinePencilData_of_endpointIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    {M : SheafOfModules.{u} X.ringCatSheaf}
    {e : SerreExtensionData X M}
    (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionData.SerreExtensionPencilSeed e)
    (D₈ : FiniteSubschemeDatum f 8) (D₃ : FiniteSubschemeDatum f 3)
    (D₁₁ Z₀ Zinf : FiniteSubschemeDatum f 11)
    (hdisjoint : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (P : SerreExtensionData.SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
      f C seed 11 Z₀ Zinf)
    (zeroIso : Z₀.val.subscheme ≅
      (degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint).val.subscheme)
    (zero_over : zeroIso.hom ≫
      (degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint).val.subschemeι =
      Z₀.val.subschemeι)
    (infinityIso : Zinf.val.subscheme ≅ D₁₁.val.subscheme)
    (infinity_over : infinityIso.hom ≫ D₁₁.val.subschemeι = Zinf.val.subschemeι) :
    ∃ F : RationalCycleFamily f,
      F.fiberCycle false = finiteSubschemeDatumCycle f D₃ + finiteSubschemeDatumCycle f D₈ ∧
      F.fiberCycle true = finiteSubschemeDatumCycle f D₁₁ := by
  exact exists_rankTwoResidualFamily_of_projectiveLinePencilData f C seed D₈ D₃ D₁₁
    hdisjoint
    (SerreExtensionData.SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData.retarget
      f C seed P (degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint) D₁₁
      zeroIso zero_over infinityIso infinity_over)

/-- In the finite étale residual setting, the rank-eight residual datum and
the rank-three component have the required disjointness automatically.  A
pencil between their union and a rank-eleven datum therefore supplies the
rank-two cycle family without a separate support hypothesis. -/
theorem exists_rankTwoResidualFamily_of_etaleResidualPencil
    {K : Type u} [Field K] [CharZero K] {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (c : X ⟶ Y) [IsClosedImmersion c]
    (f : Y ⟶ Spec (.of K)) [IsFinite (c ≫ f)] [Etale (c ≫ f)] [IsSeparated f]
    (hX : finiteSchemeRank (c ≫ f) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ f) = 3)
    (D₁₁ : FiniteSubschemeDatum f 11)
    (P : let hdisjoint :=
      disjoint_rankEightResidual_rankThreeComponent_of_etale i c f hX hZ
      FiniteSubschemeDatumPencil f 11
        (degreeEightAndDegreeThreeDatum f
          (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c f hX hZ)
          (finiteSubschemeDatumRankThreeOfClosedComponent i c f hZ) hdisjoint) D₁₁) :
    ∃ F : RationalCycleFamily f,
      F.fiberCycle false =
        finiteSubschemeDatumCycle f (finiteSubschemeDatumRankThreeOfClosedComponent i c f hZ) +
          finiteSubschemeDatumCycle f
            (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c f hX hZ) ∧
      F.fiberCycle true = finiteSubschemeDatumCycle f D₁₁ := by
  let hdisjoint :=
    disjoint_rankEightResidual_rankThreeComponent_of_etale i c f hX hZ
  exact exists_rankTwoResidualFamily_of_pencil f
    (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c f hX hZ)
    (finiteSubschemeDatumRankThreeOfClosedComponent i c f hZ) D₁₁ hdisjoint P


/-- A scheme-level rank-two pencil supplies the middle family in the exact
point-specific chain used after Coray's degree-ten alternative.  The first
and last families remain the two complete-intersection moving constructions;
the middle endpoint equations are derived from the actual finite-subscheme
data and pencil. -/
noncomputable def voisinDegreeTenPointFamilySteps_of_rankTwoPencil
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (h z₁₀ : EffectiveZeroCycle X)
    (D₃ : FiniteSubschemeDatum f 3) (D₈ : FiniteSubschemeDatum f 8)
    (D₁₁ : FiniteSubschemeDatum f 11)
    (hD₃ : finiteSubschemeDatumCycle f D₃ = h)
    (hdisjoint : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (P : FiniteSubschemeDatumPencil f 11
      (degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint) D₁₁)
    (cubicFamily : RationalCycleFamily f)
    (cubic_zero : cubicFamily.fiberCycle false =
      z₁₀ + 2 • h + finiteSubschemeDatumCycle f D₁₁)
    (cubic_infinity : cubicFamily.fiberCycle true = 9 • h)
    (quadricFamily : RationalCycleFamily f) (z₄ : EffectiveZeroCycle X)
    (quadric_zero : quadricFamily.fiberCycle false =
      finiteSubschemeDatumCycle f D₈ + z₄)
    (quadric_infinity : quadricFamily.fiberCycle true = 4 • h) :
    VoisinDegreeTenPointFamilySteps f h z₁₀ := by
  refine
    { cubicResidualFamily := cubicFamily
      residualEleven := finiteSubschemeDatumCycle f D₁₁
      cubicResidual_zero := cubic_zero
      cubicResidual_infinity := cubic_infinity
      rankTwoResidualFamily := rankTwoResidualFamilyOfPencil f D₈ D₃ D₁₁ hdisjoint P
      residualEight := finiteSubschemeDatumCycle f D₈
      rankTwoResidual_zero := ?_
      rankTwoResidual_infinity := rankTwoResidualFamilyOfPencil_infinity
        f D₈ D₃ D₁₁ hdisjoint P
      quadricResidualFamily := quadricFamily
      residualFour := z₄
      quadricResidual_zero := quadric_zero
      quadricResidual_infinity := quadric_infinity }
  rw [rankTwoResidualFamilyOfPencil_zero f D₈ D₃ D₁₁ hdisjoint P, hD₃]

/-- The normalized projective-line Serre-pencil datum supplies the middle
family of Voisin's degree-ten chain directly.  Its local equation field is
retained in `P`, while this construction uses its resulting finite-flat
finite-subscheme pencil to assemble the three family steps. -/
noncomputable def voisinDegreeTenPointFamilySteps_of_projectiveLinePencilData
    {K : Type u} [Field K] {X : Scheme.{u}}
    {M : SheafOfModules.{u} X.ringCatSheaf}
    {e : SerreExtensionData X M}
    (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (h z₁₀ : EffectiveZeroCycle X)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionData.SerreExtensionPencilSeed e)
    (D₃ : FiniteSubschemeDatum f 3) (D₈ : FiniteSubschemeDatum f 8)
    (D₁₁ : FiniteSubschemeDatum f 11)
    (hD₃ : finiteSubschemeDatumCycle f D₃ = h)
    (hdisjoint : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (P : SerreExtensionData.SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
      f C seed 11 (degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint) D₁₁)
    (cubicFamily : RationalCycleFamily f)
    (cubic_zero : cubicFamily.fiberCycle false =
      z₁₀ + 2 • h + finiteSubschemeDatumCycle f D₁₁)
    (cubic_infinity : cubicFamily.fiberCycle true = 9 • h)
    (quadricFamily : RationalCycleFamily f) (z₄ : EffectiveZeroCycle X)
    (quadric_zero : quadricFamily.fiberCycle false =
      finiteSubschemeDatumCycle f D₈ + z₄)
    (quadric_infinity : quadricFamily.fiberCycle true = 4 • h) :
    VoisinDegreeTenPointFamilySteps f h z₁₀ :=
  voisinDegreeTenPointFamilySteps_of_rankTwoPencil f h z₁₀
    D₃ D₈ D₁₁ hD₃ hdisjoint
    (SerreExtensionData.SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData.toFiniteSubschemeDatumPencil
      f C seed P)
    cubicFamily cubic_zero cubic_infinity quadricFamily z₄ quadric_zero quadric_infinity


/-- The finite étale residual form of the middle step feeds directly into
Voisin's point-specific degree-ten family data.  Its disjointness condition is
derived from the residual construction rather than supplied separately. -/
noncomputable def voisinDegreeTenPointFamilySteps_of_etaleResidualPencil
    {K : Type u} [Field K] [CharZero K] {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (c : X ⟶ Y) [IsClosedImmersion c]
    (f : Y ⟶ Spec (.of K)) [IsFinite (c ≫ f)] [Etale (c ≫ f)] [IsSeparated f]
    (hX : finiteSchemeRank (c ≫ f) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ f) = 3)
    (h z₁₀ : EffectiveZeroCycle Y)
    (D₁₁ : FiniteSubschemeDatum f 11)
    (hD₃ : finiteSubschemeDatumCycle f
      (finiteSubschemeDatumRankThreeOfClosedComponent i c f hZ) = h)
    (P : let hdisjoint :=
      disjoint_rankEightResidual_rankThreeComponent_of_etale i c f hX hZ
      FiniteSubschemeDatumPencil f 11
        (degreeEightAndDegreeThreeDatum f
          (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c f hX hZ)
          (finiteSubschemeDatumRankThreeOfClosedComponent i c f hZ) hdisjoint) D₁₁)
    (cubicFamily : RationalCycleFamily f)
    (cubic_zero : cubicFamily.fiberCycle false =
      z₁₀ + 2 • h + finiteSubschemeDatumCycle f D₁₁)
    (cubic_infinity : cubicFamily.fiberCycle true = 9 • h)
    (quadricFamily : RationalCycleFamily f) (z₄ : EffectiveZeroCycle Y)
    (quadric_zero : quadricFamily.fiberCycle false =
      finiteSubschemeDatumCycle f
        (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c f hX hZ) + z₄)
    (quadric_infinity : quadricFamily.fiberCycle true = 4 • h) :
    VoisinDegreeTenPointFamilySteps f h z₁₀ := by
  let hdisjoint :=
    disjoint_rankEightResidual_rankThreeComponent_of_etale i c f hX hZ
  exact voisinDegreeTenPointFamilySteps_of_rankTwoPencil f h z₁₀
    (finiteSubschemeDatumRankThreeOfClosedComponent i c f hZ)
    (finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c f hX hZ)
    D₁₁ hD₃ hdisjoint P cubicFamily cubic_zero cubic_infinity quadricFamily z₄
    quadric_zero quadric_infinity

/-- The three finite-flat pencils occurring in Voisin's degree-ten argument
give the point-specific family chain directly.  The first and last pencils
are the two complete-intersection moving constructions, while the middle
pencil is the rank-two construction.  Their endpoint equations are derived
from the actual finite-subscheme data, so this theorem leaves no separate
cycle-level compatibility assumption. -/
noncomputable def voisinDegreeTenPointFamilySteps_of_threePencils
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (h z₁₀ : EffectiveZeroCycle X)
    (D₁₆ : FiniteSubschemeDatum f 16) (D₁₁ : FiniteSubschemeDatum f 11)
    (h₁₆₁₁ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁₆))
      (Set.range (finiteSubschemeDatumSpecMap f D₁₁)))
    (D₂₇ : FiniteSubschemeDatum f 27)
    (hD₁₆ : finiteSubschemeDatumCycle f D₁₆ = z₁₀ + 2 • h)
    (hD₂₇ : finiteSubschemeDatumCycle f D₂₇ = 9 • h)
    (P₁₆ : FiniteSubschemeDatumPencil f 27
      (finiteSubschemeDatumOfTwoDisjointData f D₁₆ D₁₁ h₁₆₁₁) D₂₇)
    (D₃ : FiniteSubschemeDatum f 3) (D₈ : FiniteSubschemeDatum f 8)
    (hD₃ : finiteSubschemeDatumCycle f D₃ = h)
    (h₈₃ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (P₁₁ : FiniteSubschemeDatumPencil f 11
      (degreeEightAndDegreeThreeDatum f D₈ D₃ h₈₃) D₁₁)
    (D₄ : FiniteSubschemeDatum f 4)
    (h₈₄ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₄)))
    (D₁₂ : FiniteSubschemeDatum f 12)
    (hD₁₂ : finiteSubschemeDatumCycle f D₁₂ = 4 • h)
    (P₈ : FiniteSubschemeDatumPencil f 12
      (finiteSubschemeDatumOfTwoDisjointData f D₈ D₄ h₈₄) D₁₂) :
    VoisinDegreeTenPointFamilySteps f h z₁₀ := by
  refine voisinDegreeTenPointFamilySteps_of_rankTwoPencil f h z₁₀
    D₃ D₈ D₁₁ hD₃ h₈₃ P₁₁
    (FiniteSubschemeDatumPencil.toRationalCycleFamily f P₁₆) ?_ ?_
    (FiniteSubschemeDatumPencil.toRationalCycleFamily f P₈)
    (finiteSubschemeDatumCycle f D₄) ?_ ?_
  · calc
      (FiniteSubschemeDatumPencil.toRationalCycleFamily f P₁₆).fiberCycle false =
          finiteSubschemeDatumCycle f
            (finiteSubschemeDatumOfTwoDisjointData f D₁₆ D₁₁ h₁₆₁₁) :=
        FiniteSubschemeDatumPencil.fiberCycle_zero f P₁₆
      _ = finiteSubschemeDatumCycle f D₁₆ + finiteSubschemeDatumCycle f D₁₁ :=
        finiteSubschemeDatumCycleOfTwoDisjointData f D₁₆ D₁₁ h₁₆₁₁
      _ = z₁₀ + 2 • h + finiteSubschemeDatumCycle f D₁₁ := by rw [hD₁₆]
  · calc
      (FiniteSubschemeDatumPencil.toRationalCycleFamily f P₁₆).fiberCycle true =
          finiteSubschemeDatumCycle f D₂₇ :=
        FiniteSubschemeDatumPencil.fiberCycle_infinity f P₁₆
      _ = 9 • h := hD₂₇
  · calc
      (FiniteSubschemeDatumPencil.toRationalCycleFamily f P₈).fiberCycle false =
          finiteSubschemeDatumCycle f
            (finiteSubschemeDatumOfTwoDisjointData f D₈ D₄ h₈₄) :=
        FiniteSubschemeDatumPencil.fiberCycle_zero f P₈
      _ = finiteSubschemeDatumCycle f D₈ + finiteSubschemeDatumCycle f D₄ :=
        finiteSubschemeDatumCycleOfTwoDisjointData f D₈ D₄ h₈₄
  · calc
      (FiniteSubschemeDatumPencil.toRationalCycleFamily f P₈).fiberCycle true =
          finiteSubschemeDatumCycle f D₁₂ :=
        FiniteSubschemeDatumPencil.fiberCycle_infinity f P₈
      _ = 4 • h := hD₁₂

/-- The scheme-level input for the point-specific degree-ten argument.  It
retains every residual scheme and each of the three finite-flat pencils.  In
particular, this is a concrete replacement for supplying only the resulting
equalities of zero-cycles. -/
structure VoisinDegreeTenPointPencilSteps
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (h z₁₀ : EffectiveZeroCycle X) where
  D₁₆ : FiniteSubschemeDatum f 16
  D₁₁ : FiniteSubschemeDatum f 11
  disjoint₁₆₁₁ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁₆))
    (Set.range (finiteSubschemeDatumSpecMap f D₁₁))
  D₂₇ : FiniteSubschemeDatum f 27
  cycle₁₆ : finiteSubschemeDatumCycle f D₁₆ = z₁₀ + 2 • h
  cycle₂₇ : finiteSubschemeDatumCycle f D₂₇ = 9 • h
  cubicPencil : FiniteSubschemeDatumPencil f 27
    (finiteSubschemeDatumOfTwoDisjointData f D₁₆ D₁₁ disjoint₁₆₁₁) D₂₇
  D₃ : FiniteSubschemeDatum f 3
  D₈ : FiniteSubschemeDatum f 8
  cycle₃ : finiteSubschemeDatumCycle f D₃ = h
  disjoint₈₃ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
    (Set.range (finiteSubschemeDatumSpecMap f D₃))
  rankTwoPencil : FiniteSubschemeDatumPencil f 11
    (degreeEightAndDegreeThreeDatum f D₈ D₃ disjoint₈₃) D₁₁
  D₄ : FiniteSubschemeDatum f 4
  disjoint₈₄ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
    (Set.range (finiteSubschemeDatumSpecMap f D₄))
  D₁₂ : FiniteSubschemeDatum f 12
  cycle₁₂ : finiteSubschemeDatumCycle f D₁₂ = 4 • h
  quadricPencil : FiniteSubschemeDatumPencil f 12
    (finiteSubschemeDatumOfTwoDisjointData f D₈ D₄ disjoint₈₄) D₁₂

/-- The geometric subschemes and finite-flat pencils in the point-specific
degree-ten argument, before their rational-cycle classes have been
identified. -/
structure VoisinDegreeTenPointPencilData
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f] where
  D₁₆ : FiniteSubschemeDatum f 16
  D₁₁ : FiniteSubschemeDatum f 11
  disjoint₁₆₁₁ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁₆))
    (Set.range (finiteSubschemeDatumSpecMap f D₁₁))
  D₂₇ : FiniteSubschemeDatum f 27
  cubicPencil : FiniteSubschemeDatumPencil f 27
    (finiteSubschemeDatumOfTwoDisjointData f D₁₆ D₁₁ disjoint₁₆₁₁) D₂₇
  D₃ : FiniteSubschemeDatum f 3
  D₈ : FiniteSubschemeDatum f 8
  disjoint₈₃ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
    (Set.range (finiteSubschemeDatumSpecMap f D₃))
  rankTwoPencil : FiniteSubschemeDatumPencil f 11
    (degreeEightAndDegreeThreeDatum f D₈ D₃ disjoint₈₃) D₁₁
  D₄ : FiniteSubschemeDatum f 4
  disjoint₈₄ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
    (Set.range (finiteSubschemeDatumSpecMap f D₄))
  D₁₂ : FiniteSubschemeDatum f 12
  quadricPencil : FiniteSubschemeDatumPencil f 12
    (finiteSubschemeDatumOfTwoDisjointData f D₈ D₄ disjoint₈₄) D₁₂

/-- A projective-line Serre pencil whose literal endpoint zero schemes have
been identified with Voisin's rank-eight-plus-rank-three and rank-eleven
subschemes supplies the middle pencil in the complete degree-ten package.
The other two pencils remain the complete-intersection pencils.  This is the
scheme-level bridge from the gluing construction to the three-pencil datum
used by the final cycle calculation. -/
noncomputable def VoisinDegreeTenPointPencilData.of_projectiveLineRankTwoPencilData
    {K : Type u} [Field K] {X : Scheme.{u}}
    {M : SheafOfModules.{u} X.ringCatSheaf} {e : SerreExtensionData X M}
    (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionData.SerreExtensionPencilSeed e)
    (D₁₆ : FiniteSubschemeDatum f 16) (D₁₁ : FiniteSubschemeDatum f 11)
    (h₁₆₁₁ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁₆))
      (Set.range (finiteSubschemeDatumSpecMap f D₁₁)))
    (D₂₇ : FiniteSubschemeDatum f 27)
    (P₁₆ : FiniteSubschemeDatumPencil f 27
      (finiteSubschemeDatumOfTwoDisjointData f D₁₆ D₁₁ h₁₆₁₁) D₂₇)
    (D₃ : FiniteSubschemeDatum f 3) (D₈ : FiniteSubschemeDatum f 8)
    (h₈₃ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (Z₀ Zinf : FiniteSubschemeDatum f 11)
    (P₁₁ : SerreExtensionData.SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
      f C seed 11 Z₀ Zinf)
    (zeroIso : Z₀.val.subscheme ≅
      (degreeEightAndDegreeThreeDatum f D₈ D₃ h₈₃).val.subscheme)
    (zero_over : zeroIso.hom ≫
      (degreeEightAndDegreeThreeDatum f D₈ D₃ h₈₃).val.subschemeι =
      Z₀.val.subschemeι)
    (infinityIso : Zinf.val.subscheme ≅ D₁₁.val.subscheme)
    (infinity_over : infinityIso.hom ≫ D₁₁.val.subschemeι = Zinf.val.subschemeι)
    (D₄ : FiniteSubschemeDatum f 4)
    (h₈₄ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₄)))
    (D₁₂ : FiniteSubschemeDatum f 12)
    (P₈ : FiniteSubschemeDatumPencil f 12
      (finiteSubschemeDatumOfTwoDisjointData f D₈ D₄ h₈₄) D₁₂) :
    VoisinDegreeTenPointPencilData f := by
  let Q := SerreExtensionData.SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData.retarget
    f C seed P₁₁ (degreeEightAndDegreeThreeDatum f D₈ D₃ h₈₃) D₁₁
      zeroIso zero_over infinityIso infinity_over
  exact
    { D₁₆ := D₁₆
      D₁₁ := D₁₁
      disjoint₁₆₁₁ := h₁₆₁₁
      D₂₇ := D₂₇
      cubicPencil := P₁₆
      D₃ := D₃
      D₈ := D₈
      disjoint₈₃ := h₈₃
      rankTwoPencil :=
        SerreExtensionData.SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData.toFiniteSubschemeDatumPencil
          f C seed Q
      D₄ := D₄
      disjoint₈₄ := h₈₄
      D₁₂ := D₁₂
      quadricPencil := P₈ }

/- The normalized rank-two pencil retains the quotient-level endpoint
   relation after its endpoint schemes have been retargeted to Voisin's
   residual data.  This is the class calculation supplied by the projective
   line itself; it is useful when the middle family is constructed from the
   Serre gluing rather than from an abstract finite-subscheme pencil. -/
theorem VoisinDegreeTenPointPencilData.rankTwoEndpoint_cycleClass_eq
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (S : VoisinDegreeTenPointPencilData f) :
    curveFamilyCycleClass f
        (finiteSubschemeDatumCycle f
          (degreeEightAndDegreeThreeDatum f S.D₈ S.D₃ S.disjoint₈₃)).toZeroCycle =
      curveFamilyCycleClass f
        (finiteSubschemeDatumCycle f S.D₁₁).toZeroCycle := by
  have hP := FiniteSubschemeDatumPencil.cycleClass_eq f S.rankTwoPencil
  simpa only [degreeEightAndDegreeThreeDatum_cycle,
    effectiveCycleToSigned_add, map_add] using hP

/-- The projective-line Serre pencil gives the middle Voisin endpoint class
relation directly, even when its two literal endpoint schemes are only
identified with the intended residual schemes by isomorphisms over the
cubic surface. -/
theorem rankTwoEndpoint_cycleClass_eq_of_projectiveLinePencil
    {K : Type u} [Field K] {X : Scheme.{u}}
    {M : SheafOfModules.{u} X.ringCatSheaf}
    {e : SerreExtensionData X M}
    (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (seed : SerreExtensionData.SerreExtensionPencilSeed e)
    (D₃ : FiniteSubschemeDatum f 3) (D₈ : FiniteSubschemeDatum f 8)
    (hdisjoint : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₈))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (Z₀ Zinf D₁₁ : FiniteSubschemeDatum f 11)
    (P : SerreExtensionData.SerreExtensionRankTwoAffineCover.ProjectiveLinePencilData
      f C seed 11 Z₀ Zinf)
    (zeroIso : Z₀.val.subscheme ≅
      (degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint).val.subscheme)
    (zero_over : zeroIso.hom ≫
      (degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint).val.subschemeι =
      Z₀.val.subschemeι)
    (infinityIso : Zinf.val.subscheme ≅ D₁₁.val.subscheme)
    (infinity_over : infinityIso.hom ≫ D₁₁.val.subschemeι = Zinf.val.subschemeι) :
    curveFamilyCycleClass f
        (finiteSubschemeDatumCycle f
          (degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint)).toZeroCycle =
      curveFamilyCycleClass f (finiteSubschemeDatumCycle f D₁₁).toZeroCycle := by
  exact P.retarget_cycleClass_eq f C seed
    (degreeEightAndDegreeThreeDatum f D₈ D₃ hdisjoint) D₁₁
    zeroIso zero_over infinityIso infinity_over

/-- Adding the four endpoint cycle identities turns the bare pencil data into
the full point-specific three-pencil package. -/
def VoisinDegreeTenPointPencilData.toSteps
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    {h z₁₀ : EffectiveZeroCycle X} (S : VoisinDegreeTenPointPencilData f)
    (cycle₁₆ : finiteSubschemeDatumCycle f S.D₁₆ = z₁₀ + 2 • h)
    (cycle₂₇ : finiteSubschemeDatumCycle f S.D₂₇ = 9 • h)
    (cycle₃ : finiteSubschemeDatumCycle f S.D₃ = h)
    (cycle₁₂ : finiteSubschemeDatumCycle f S.D₁₂ = 4 • h) :
    VoisinDegreeTenPointPencilSteps f h z₁₀ :=
  { D₁₆ := S.D₁₆
    D₁₁ := S.D₁₁
    disjoint₁₆₁₁ := S.disjoint₁₆₁₁
    D₂₇ := S.D₂₇
    cycle₁₆ := cycle₁₆
    cycle₂₇ := cycle₂₇
    cubicPencil := S.cubicPencil
    D₃ := S.D₃
    D₈ := S.D₈
    cycle₃ := cycle₃
    disjoint₈₃ := S.disjoint₈₃
    rankTwoPencil := S.rankTwoPencil
    D₄ := S.D₄
    disjoint₈₄ := S.disjoint₈₄
    D₁₂ := S.D₁₂
    cycle₁₂ := cycle₁₂
    quadricPencil := S.quadricPencil }

/-- Concrete finite-subscheme pencil data imply Voisin's point-specific
family steps. -/
noncomputable def VoisinDegreeTenPointPencilSteps.toFamilySteps
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    {h z₁₀ : EffectiveZeroCycle X}
    (S : VoisinDegreeTenPointPencilSteps f h z₁₀) :
    VoisinDegreeTenPointFamilySteps f h z₁₀ :=
  voisinDegreeTenPointFamilySteps_of_threePencils f h z₁₀
    S.D₁₆ S.D₁₁ S.disjoint₁₆₁₁ S.D₂₇ S.cycle₁₆ S.cycle₂₇ S.cubicPencil
    S.D₃ S.D₈ S.cycle₃ S.disjoint₈₃ S.rankTwoPencil
    S.D₄ S.disjoint₈₄ S.D₁₂ S.cycle₁₂ S.quadricPencil

/-- The three finite-flat pencils give Voisin's point-specific cycle classes
once their complete-intersection and line-section endpoint classes have been
identified.  This is the form used by the geometric argument: line sections
need only be rationally equivalent to the reference cycle, not equal as
literal effective cycles. -/
theorem voisinDegreeTenPointSteps_of_threePencils_of_cycleClasses
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (h z₁₀ : EffectiveZeroCycle X) (S : VoisinDegreeTenPointPencilData f)
    (cycle₁₆ : curveFamilyCycleClass f (finiteSubschemeDatumCycle f S.D₁₆).toZeroCycle =
      curveFamilyCycleClass f (z₁₀ + 2 • h).toZeroCycle)
    (cycle₂₇ : curveFamilyCycleClass f (finiteSubschemeDatumCycle f S.D₂₇).toZeroCycle =
      9 • curveFamilyCycleClass f h.toZeroCycle)
    (cycle₃ : curveFamilyCycleClass f (finiteSubschemeDatumCycle f S.D₃).toZeroCycle =
      curveFamilyCycleClass f h.toZeroCycle)
    (cycle₁₂ : curveFamilyCycleClass f (finiteSubschemeDatumCycle f S.D₁₂).toZeroCycle =
      4 • curveFamilyCycleClass f h.toZeroCycle) :
    VoisinDegreeTenPointSteps f h z₁₀ := by
  refine ⟨finiteSubschemeDatumCycle f S.D₁₁, finiteSubschemeDatumCycle f S.D₈,
    finiteSubschemeDatumCycle f S.D₄, ?_, ?_, ?_⟩
  · have hcubic := curveFamilyCycleClass_fibers f
      (FiniteSubschemeDatumPencil.toRationalCycleFamily f S.cubicPencil)
    rw [FiniteSubschemeDatumPencil.fiberCycle_zero f S.cubicPencil,
      FiniteSubschemeDatumPencil.fiberCycle_infinity f S.cubicPencil,
      finiteSubschemeDatumCycleOfTwoDisjointData,
      effectiveCycleToSigned_add, map_add, cycle₁₆, cycle₂₇] at hcubic
    apply (eq_sub_iff_add_eq).2
    calc
      curveFamilyCycleClass f (finiteSubschemeDatumCycle f S.D₁₁).toZeroCycle +
          curveFamilyCycleClass f (z₁₀ + 2 • h).toZeroCycle =
        curveFamilyCycleClass f (z₁₀ + 2 • h).toZeroCycle +
          curveFamilyCycleClass f (finiteSubschemeDatumCycle f S.D₁₁).toZeroCycle := add_comm _ _
      _ = 9 • curveFamilyCycleClass f h.toZeroCycle := hcubic
  · have hmiddle := S.rankTwoEndpoint_cycleClass_eq f
    rw [degreeEightAndDegreeThreeDatum_cycle, effectiveCycleToSigned_add,
      map_add, cycle₃] at hmiddle
    apply (eq_sub_iff_add_eq).2
    calc
      curveFamilyCycleClass f (finiteSubschemeDatumCycle f S.D₈).toZeroCycle +
          curveFamilyCycleClass f h.toZeroCycle =
        curveFamilyCycleClass f h.toZeroCycle +
          curveFamilyCycleClass f (finiteSubschemeDatumCycle f S.D₈).toZeroCycle := add_comm _ _
      _ = curveFamilyCycleClass f (finiteSubschemeDatumCycle f S.D₁₁).toZeroCycle := hmiddle
  · have hquadric := curveFamilyCycleClass_fibers f
      (FiniteSubschemeDatumPencil.toRationalCycleFamily f S.quadricPencil)
    rw [FiniteSubschemeDatumPencil.fiberCycle_zero f S.quadricPencil,
      FiniteSubschemeDatumPencil.fiberCycle_infinity f S.quadricPencil,
      finiteSubschemeDatumCycleOfTwoDisjointData,
      effectiveCycleToSigned_add, map_add, cycle₁₂] at hquadric
    apply (eq_sub_iff_add_eq).2
    calc
      curveFamilyCycleClass f (finiteSubschemeDatumCycle f S.D₄).toZeroCycle +
          curveFamilyCycleClass f (finiteSubschemeDatumCycle f S.D₈).toZeroCycle =
        curveFamilyCycleClass f (finiteSubschemeDatumCycle f S.D₈).toZeroCycle +
          curveFamilyCycleClass f (finiteSubschemeDatumCycle f S.D₄).toZeroCycle := add_comm _ _
      _ = 4 • curveFamilyCycleClass f h.toZeroCycle := hquadric

/-- The three finite-flat pencils and their endpoint cycle classes directly
produce the effective degree-four cycle used to eliminate the degree-ten
case.  This is the paper-facing effectivity interface: callers need not
unpack the intermediate degree-eleven and degree-eight representatives. -/
theorem effective_degree_four_of_voisinDegreeTenPointPencilData_of_cycleClasses
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (h z₁₀ : EffectiveZeroCycle X)
    (hh : EffectiveZeroCycle.degree f h = 3)
    (hz₁₀ : EffectiveZeroCycle.degree f z₁₀ = 10)
    (S : VoisinDegreeTenPointPencilData f)
    (cycle₁₆ : curveFamilyCycleClass f
      (finiteSubschemeDatumCycle f S.D₁₆).toZeroCycle =
        curveFamilyCycleClass f (z₁₀ + 2 • h).toZeroCycle)
    (cycle₂₇ : curveFamilyCycleClass f
      (finiteSubschemeDatumCycle f S.D₂₇).toZeroCycle =
        9 • curveFamilyCycleClass f h.toZeroCycle)
    (cycle₃ : curveFamilyCycleClass f
      (finiteSubschemeDatumCycle f S.D₃).toZeroCycle =
        curveFamilyCycleClass f h.toZeroCycle)
    (cycle₁₂ : curveFamilyCycleClass f
      (finiteSubschemeDatumCycle f S.D₁₂).toZeroCycle =
        4 • curveFamilyCycleClass f h.toZeroCycle) :
    ∃ z₄ : EffectiveZeroCycle X, EffectiveZeroCycle.degree f z₄ = 4 := by
  exact effective_degree_four_of_voisin_degree_ten_point_steps f h z₁₀ hh hz₁₀
    (voisinDegreeTenPointSteps_of_threePencils_of_cycleClasses f h z₁₀ S
      cycle₁₆ cycle₂₇ cycle₃ cycle₁₂)

/-- The rank-sixteen completion of Coray's degree-ten point has the expected
class `z₁₀ + 2h` as soon as each avoiding line section has class `h`. -/
theorem degreeTenClosedPoint_rankSixteenCompletion_cycle_class
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (C : DegreeTenRankSixteenCompletion p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx))
    [IsSeparated (hypersurfaceToBase p hp)]
    (h : EffectiveZeroCycle (hypersurface p hp))
    (hfirst : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.first).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (hsecond : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.second).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle) :
    curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.datum).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp)
          ((Finsupp.single x 1 + 2 • h : EffectiveZeroCycle (hypersurface p hp)).toZeroCycle) := by
  rw [degreeTenClosedPoint_rankSixteenCompletion_cycle p hp x hx C,
    effectiveCycleToSigned_add, map_add, effectiveCycleToSigned_add, map_add,
    hfirst, hsecond, two_nsmul, effectiveCycleToSigned_add, map_add,
    effectiveCycleToSigned_add, map_add, add_assoc]

/-- Coray's degree-ten completion, the three geometric pencils, and their
endpoint class calculations yield the exact quotient-level steps in Voisin's
argument. -/
theorem voisinDegreeTenPointSteps_of_completion_and_cycleClasses
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (C : DegreeTenRankSixteenCompletion p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx))
    [IsSeparated (hypersurfaceToBase p hp)]
    (h : EffectiveZeroCycle (hypersurface p hp))
    (hfirst : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.first).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (hsecond : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.second).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (S : VoisinDegreeTenPointPencilData (hypersurfaceToBase p hp))
    (hD₁₆ : S.D₁₆ = C.datum)
    (cycle₂₇ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) S.D₂₇).toZeroCycle =
        9 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₃ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) S.D₃).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₁₂ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) S.D₁₂).toZeroCycle =
        4 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle) :
    VoisinDegreeTenPointSteps (hypersurfaceToBase p hp) h (Finsupp.single x 1) := by
  apply voisinDegreeTenPointSteps_of_threePencils_of_cycleClasses
    (hypersurfaceToBase p hp) h (Finsupp.single x 1) S
  · rw [hD₁₆]
    exact degreeTenClosedPoint_rankSixteenCompletion_cycle_class
      p hp x hx C h hfirst hsecond
  · exact cycle₂₇
  · exact cycle₃
  · exact cycle₁₂

/-- The degree-sixteen member of the first pencil need only be identified
with Coray's completed subscheme by an isomorphism over the cubic surface.
The canonical finite-subscheme cycle is invariant under that identification,
so the endpoint calculation does not require literal equality of the two
ideal presentations. -/
theorem voisinDegreeTenPointSteps_of_completion_and_cycleClasses_of_iso
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (C : DegreeTenRankSixteenCompletion p hp
      (finiteSubschemeDatumOfClosedPointOfResidueDegree
        (hypersurfaceToBase p hp) x 10 hx))
    [IsSeparated (hypersurfaceToBase p hp)]
    (h : EffectiveZeroCycle (hypersurface p hp))
    (hfirst : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.first).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (hsecond : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) C.second).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (S : VoisinDegreeTenPointPencilData (hypersurfaceToBase p hp))
    (e₁₆ : S.D₁₆.val.subscheme ≅ C.datum.val.subscheme)
    (he₁₆ : e₁₆.hom ≫ C.datum.val.subschemeι = S.D₁₆.val.subschemeι)
    (cycle₂₇ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) S.D₂₇).toZeroCycle =
        9 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₃ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) S.D₃).toZeroCycle =
        curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle)
    (cycle₁₂ : curveFamilyCycleClass (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) S.D₁₂).toZeroCycle =
        4 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle) :
    VoisinDegreeTenPointSteps (hypersurfaceToBase p hp) h (Finsupp.single x 1) := by
  apply voisinDegreeTenPointSteps_of_threePencils_of_cycleClasses
    (hypersurfaceToBase p hp) h (Finsupp.single x 1) S
  · rw [finiteSubschemeDatumCycle_eq_of_iso (hypersurfaceToBase p hp)
      S.D₁₆ C.datum e₁₆ he₁₆]
    exact degreeTenClosedPoint_rankSixteenCompletion_cycle_class
      p hp x hx C h hfirst hsecond
  · exact cycle₂₇
  · exact cycle₃
  · exact cycle₁₂

end PfaffianDescent
