import PfaffianDescent.ProjectiveFiniteFamilyHomogeneousWholeOpenCover
import PfaffianDescent.NativeWholeFiniteFamilyOpenLocusCartesianBaseChange
import PfaffianDescent.RelativeProjectiveAffineOpenTestIdentification
import PfaffianDescent.RelativeOpenContainedPointEquiv315

/-! The literal197 family on every original test constructs its actual6305
open cover and a chart point on every cover member. Native315 pushes that
point back to EXACTLY the literal197 restriction, including its whole ideal.
No cover, containment, lift, chart point or quasi-compactness is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v
set_option autoImplicit false

/-- The constructed6329 iso identifies the actual original chart embedding
range on every scheme test. This uses no pending transition theorem. -/
private theorem actualOriginalChartTestEmbedding_range001
    {X B : Scheme.{u}} (F : X ⟶ B) (U : X.Opens) (T : Over B) :
    Set.range (relativeClosedAmbientTestMap313 U.ι F T) =
      (pullback.snd T.hom F ⁻¹ᵁ U : (pullback T.hom F).Opens) := by
  have h := AlgebraicGeometry.range_eq_range_of_surjective
    (relativeOriginalOpenTestPreimage001 U F T).ι
    (relativeClosedAmbientTestMap313 U.ι F T)
    (relativeOriginalOpenTestPreimageIso001 U F T).hom
    (relativeOriginalOpenTestPreimageIso_toAmbient001 U F T)
  exact h.symm.trans (relativeOriginalOpenTestPreimage001 U F T).range_ι

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {B : Scheme.{u}} (F : Proj 𝒜 ⟶ B) (n : ℕ) (T : Over B)
variable (P : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n)

/-- The actual6305 whole-family cover of an arbitrary original test base. -/
def projectiveFiniteFamilyAllTestLocalCover001 : T.left.OpenCover :=
  finiteFamilyProjectiveHomogeneousWholeChartOpenCover001 𝒜
    (pullback.snd T.hom F) (relativeHilbertFamily197 F T) n P

/-- Each actual cover member retains the original test-to-base map. -/
def projectiveFiniteFamilyAllTestLocalCoverTest001
    (a : projectivePositiveHomogeneousChartIndex001 𝒜) : Over B :=
  Over.mk ((projectiveFiniteFamilyAllTestLocalCover001 𝒜 F n T P).f a ≫ T.hom)

/-- The literal inclusion of that cover member into the SAME original test. -/
def projectiveFiniteFamilyAllTestLocalCoverInclusion001
    (a : projectivePositiveHomogeneousChartIndex001 𝒜) :
    projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a ⟶ T :=
  Over.homMk ((projectiveFiniteFamilyAllTestLocalCover001 𝒜 F n T P).f a) rfl

/-- The original whole-family restriction is the actual197 functor map. -/
def projectiveFiniteFamilyAllTestLocalRestriction001
    (a : projectivePositiveHomogeneousChartIndex001 𝒜) :
    FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F
      (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a)) n :=
  (relativeFiniteFlatHilbertFunctor197 F n).map
    (projectiveFiniteFamilyAllTestLocalCoverInclusion001 𝒜 F n T P a).op P

/-- Arbitrary Cartesian basechange6352 turns the constructed good-open
inclusion into whole-chart containment. No support reduction is performed. -/
private theorem projectiveFiniteFamilyAllTestLocalRestriction_good_eq_top001
    (a : projectivePositiveHomogeneousChartIndex001 𝒜) :
    finiteFamilyWholeOpenLocus314 (relativeHilbertFamily197 F
      (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a)) n
      (projectiveFiniteFamilyAllTestLocalRestriction001 𝒜 F n T P a)
      (pullback.snd (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a).hom F
        ⁻¹ᵁ Proj.basicOpen 𝒜 a.val) = ⊤ := by
  rw [projectiveFiniteFamilyAllTestLocalRestriction001,
    relativeFiniteFlatHilbertWholeOpenLocus_baseChange001]
  change (finiteFamilyProjectiveHomogeneousChartLocus001 𝒜
    (pullback.snd T.hom F) (relativeHilbertFamily197 F T) n P a).ι ⁻¹ᵁ
      finiteFamilyProjectiveHomogeneousChartLocus001 𝒜
        (pullback.snd T.hom F) (relativeHilbertFamily197 F T) n P a = ⊤
  exact Scheme.Opens.ι_preimage_self _

/-- The ENTIRE literal restricted family lies in the actual chart embedding
range, derived from the actual cover and original Cartesian basechange. -/
theorem projectiveFiniteFamilyAllTestLocalRestriction_in_chart001
    (a : projectivePositiveHomogeneousChartIndex001 𝒜) :
    Set.range (projectiveFiniteFamilyAllTestLocalRestriction001 𝒜 F n T P a).val.subschemeι ⊆
      Set.range (relativeClosedAmbientTestMap313 (Proj.basicOpen 𝒜 a.val).ι F
        (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a)) := by
  rw [actualOriginalChartTestEmbedding_range001]
  exact (finiteFamilyWholeOpenLocus_eq_top_iff_entireSource_in_open001 _ n
    (projectiveFiniteFamilyAllTestLocalRestriction001 𝒜 F n T P a) _).mp
      (projectiveFiniteFamilyAllTestLocalRestriction_good_eq_top001 𝒜 F n T P a)

variable [IsSeparated F]

/-- Native315 constructs the SAME whole finite-flat point inside the
original homogeneous chart over the actual cover member. -/
def projectiveFiniteFamilyAllTestLocalChartPoint001
    (a : projectivePositiveHomogeneousChartIndex001 𝒜) :
    FiniteFlatHilbertPoint195 (relativeHilbertFamily197
      ((Proj.basicOpen 𝒜 a.val).ι ≫ F)
      (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a)) n :=
  (relativeOpenContainedPointEquiv315 (Proj.basicOpen 𝒜 a.val) F n
    (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a)).symm
      ⟨projectiveFiniteFamilyAllTestLocalRestriction001 𝒜 F n T P a,
        projectiveFiniteFamilyAllTestLocalRestriction_in_chart001 𝒜 F n T P a⟩

/-- Pushing the constructed local chart point gives EXACTLY the original
family's literal197 restriction, as points and not merely their supports. -/
theorem projectiveFiniteFamilyAllTestLocalChartPoint_push_eq_restriction001
    (a : projectivePositiveHomogeneousChartIndex001 𝒜) :
    relativeOpenFiniteFlatPointPush315 (Proj.basicOpen 𝒜 a.val) F n
      (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a)
      (projectiveFiniteFamilyAllTestLocalChartPoint001 𝒜 F n T P a) =
        projectiveFiniteFamilyAllTestLocalRestriction001 𝒜 F n T P a := by
  let e := relativeOpenContainedPointEquiv315 (Proj.basicOpen 𝒜 a.val) F n
    (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a)
  let PP : relativeOpenContainedPoint315 (Proj.basicOpen 𝒜 a.val) F n
      (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a) :=
    ⟨projectiveFiniteFamilyAllTestLocalRestriction001 𝒜 F n T P a,
      projectiveFiniteFamilyAllTestLocalRestriction_in_chart001 𝒜 F n T P a⟩
  exact (relativeOpenContainedPointEquiv_push315 (Proj.basicOpen 𝒜 a.val) F n
    (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a) (e.symm PP)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply PP))

/-- The full original ambient ideal is preserved, including nilpotents. -/
theorem projectiveFiniteFamilyAllTestLocalChartPoint_wholeAmbientIdeal001
    (a : projectivePositiveHomogeneousChartIndex001 𝒜) :
    (projectiveFiniteFamilyAllTestLocalChartPoint001 𝒜 F n T P a).val.map
      (relativeClosedAmbientTestMap313 (Proj.basicOpen 𝒜 a.val).ι F
        (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a)) =
      (projectiveFiniteFamilyAllTestLocalRestriction001 𝒜 F n T P a).val :=
  relativeOpenContainedPointEquiv_inv_ambientIdeal315 (Proj.basicOpen 𝒜 a.val) F n
    (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a)
    ⟨projectiveFiniteFamilyAllTestLocalRestriction001 𝒜 F n T P a,
      projectiveFiniteFamilyAllTestLocalRestriction_in_chart001 𝒜 F n T P a⟩

/-- On the actual6305 cover, every original test family has a CONSTRUCTED
local chart point with exact push identity and whole-ideal equality.
There is no quasi-compactness requirement on T and no supplied local lift. -/
theorem projectiveFiniteFamilyAllTest_exists_localChartDictionary001 :
    ∀ a : projectivePositiveHomogeneousChartIndex001 𝒜,
    ∃ Q : FiniteFlatHilbertPoint195 (relativeHilbertFamily197
      ((Proj.basicOpen 𝒜 a.val).ι ≫ F)
      (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a)) n,
      relativeOpenFiniteFlatPointPush315 (Proj.basicOpen 𝒜 a.val) F n
        (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a) Q =
          (relativeFiniteFlatHilbertFunctor197 F n).map
            (projectiveFiniteFamilyAllTestLocalCoverInclusion001 𝒜 F n T P a).op P ∧
      Q.val.map (relativeClosedAmbientTestMap313 (Proj.basicOpen 𝒜 a.val).ι F
        (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a)) =
          ((relativeFiniteFlatHilbertFunctor197 F n).map
            (projectiveFiniteFamilyAllTestLocalCoverInclusion001 𝒜 F n T P a).op P).val := by
  intro a
  exact ⟨projectiveFiniteFamilyAllTestLocalChartPoint001 𝒜 F n T P a,
    projectiveFiniteFamilyAllTestLocalChartPoint_push_eq_restriction001 𝒜 F n T P a,
    projectiveFiniteFamilyAllTestLocalChartPoint_wholeAmbientIdeal001 𝒜 F n T P a⟩

end PfaffianDescent
end
