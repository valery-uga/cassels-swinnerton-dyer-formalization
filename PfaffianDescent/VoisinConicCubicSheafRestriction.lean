import PfaffianDescent.VoisinConicCubicRestrictionKernel
import PfaffianDescent.VoisinCubicThreeGlobalSections
import PfaffianDescent.VoisinPlaneConicNonempty
import PfaffianDescent.ProjectivePositiveGlobalSectionsLinear
import PfaffianDescent.HomogeneousChartPointwiseVanishing
import PfaffianDescent.VoisinPlaneConicGeneralSaturation

/-!
# Comparing coordinate and sheaf restriction to a plane conic

The map on actual positive-twist sections along a homogeneous closed
immersion sends the section represented by a homogeneous element to the
section represented by its quotient-coordinate class. Projective-point
localization, chartwise localization, and plane-conic saturation make this
comparison faithful for reducible and nonreduced conics as well.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent.ProjectiveNegativeTwist

open CategoryTheory AlgebraicGeometry MvPolynomial
open AllCharacteristics HomogeneousProjective

universe u

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- Restriction of literal positive-twist global sections along the
projective closed immersion induced by `I ⊆ J`. -/
noncomputable def positiveQuotientRestrictionSections
    (I J : HomogeneousIdeal PS) (hIJ : I.toIdeal ≤ J.toIdeal) (m : ℕ) :
    (positiveSheafOfModules (grading I) m).sections →
      (positiveSheafOfModules (grading J) m).sections :=
  fun s => pushforwardModuleSectionsEquiv (schemeQuotientMap I J hIJ)
    (positiveSheafOfModules (grading J) m)
    (SheafOfModules.sectionsMap
      (gradedRingHomPositiveTwistToPushforward (grading I) (grading J)
        (gradedQuotientMap I J hIJ)
        (gradedSurjective_irrelevant_le (gradedQuotientMap I J hIJ)
          (gradedQuotientMap_surjective I J hIJ)) m) s)

/-- Restriction of a fraction `z/1` is the fraction of its image in the
quotient coordinate ring. -/
theorem positiveQuotientRestrictionSections_homogeneous
    (I J : HomogeneousIdeal PS) (hIJ : I.toIdeal ≤ J.toIdeal)
    (m : ℕ) (z : grading I m) :
    positiveQuotientRestrictionSections I J hIJ m
      (positiveGlobalSectionOfHomogeneous (grading I) m z) =
    positiveGlobalSectionOfHomogeneous (grading J) m
      (gradedQuotientPieceLinearMap I J hIJ m z) := by
  apply PresheafOfModules.sections_ext
  intro U
  apply Subtype.ext
  funext y
  change Localization.localRingHom _ _
      (gradedQuotientMap I J hIJ).toRingHom rfl
      (Localization.mk (z : CoordinateRing I)
        ⟨1, Submonoid.one_mem _⟩) =
    Localization.mk
      (coordinateQuotientMap I J hIJ (z : CoordinateRing I))
      ⟨1, Submonoid.one_mem _⟩
  exact localRingHom_mk_one _ _
    (gradedQuotientMap I J hIJ).toRingHom rfl
    (z : CoordinateRing I)

/-- Every cubic coordinate class in the conic ideal restricts to zero as
an actual sheaf section on that conic. -/
theorem positiveQuotientRestrictionSections_homogeneousZero_of_gradedKer
    (I J : HomogeneousIdeal PS) (hIJ : I.toIdeal ≤ J.toIdeal)
    (m : ℕ) (z : grading I m)
    (hz : z ∈ LinearMap.ker (gradedQuotientPieceLinearMap I J hIJ m)) :
    positiveQuotientRestrictionSections I J hIJ m
      (positiveGlobalSectionOfHomogeneous (grading I) m z) =
      positiveGlobalSectionOfHomogeneous (grading J) m 0 := by
  rw [positiveQuotientRestrictionSections_homogeneous,
    (LinearMap.mem_ker.mp hz)]

/-- Literal zero restriction is exactly pointwise vanishing of the quotient
coordinate class in the projective localizations. This criterion does not
assume that the quotient coordinate ring is a domain. -/
theorem positiveQuotientRestrictionSections_zero_iff_pointwise_localization_zero
    (I J : HomogeneousIdeal PS) (hIJ : I.toIdeal ≤ J.toIdeal)
    (m : ℕ) (z : grading I m) :
    positiveQuotientRestrictionSections I J hIJ m
        (positiveGlobalSectionOfHomogeneous (grading I) m z) =
      positiveGlobalSectionOfHomogeneous (grading J) m 0 ↔
      ∀ x : ProjectiveSpectrum.top (grading J),
        (Localization.mk
            ((gradedQuotientPieceLinearMap I J hIJ m z : grading J m) :
              CoordinateRing J) 1 : PositiveFiber (grading J) x) = 0 := by
  rw [positiveQuotientRestrictionSections_homogeneous]
  rw [positiveGlobalSectionOfHomogeneous_eq_iff_pointwise_localization_eq]
  have hzero (x : ProjectiveSpectrum.top (grading J)) :
      (Localization.mk ((0 : grading J m) : CoordinateRing J) 1 :
        PositiveFiber (grading J) x) = 0 := by
    simp only [Submodule.coe_zero, Localization.mk_one_eq_algebraMap, map_zero]
  constructor
  · intro h x
    simpa only [hzero x] using h x
  · intro h x
    simpa only [hzero x] using h x

/-- Homogeneous sections on any plane conic inject into actual positive-twist
global sections, including for reducible and nonreduced conics. -/
theorem planeConic_positiveGlobalSectionOfHomogeneous_injective
    (ell q : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (hq : q.IsHomogeneous 2) (m : ℕ) :
    Function.Injective
      (positiveGlobalSectionOfHomogeneous
        (grading (planeConicHomogeneousIdeal ell q hell hq)) m) := by
  let J := planeConicHomogeneousIdeal ell q hell hq
  intro z w hzw
  have hp := positiveGlobalSectionOfHomogeneous_eq_imp_pointwise_localization_eq
    J m z w hzw
  let t : grading J m := z - w
  have htpoint (x : ProjectiveSpectrum.top (grading J)) :
      (Localization.mk (t : CoordinateRing J) 1 : PositiveFiber (grading J) x) = 0 := by
    change (Localization.mk ((z : CoordinateRing J) - (w : CoordinateRing J)) 1 :
      PositiveFiber (grading J) x) = 0
    simp only [Localization.mk_one_eq_algebraMap, map_sub]
    exact sub_eq_zero.mpr (hp x)
  have htchart (i : Fin 4) :
      algebraMap (CoordinateRing J)
        (Localization (Submonoid.powers (coordinate J i)))
        (t : CoordinateRing J) = 0 :=
    localization_eq_zero_of_projective_pointwise_zero
      (grading J) (coordinate_mem J i) m (t : CoordinateRing J) t.property
      htpoint
  have htzero : (t : CoordinateRing J) = 0 := by
    exact plane_conic_pair_quotient_eq_zero_of_all_coordinate_localizations_zero
      ell q hell hell0 hq (t : CoordinateRing J) htchart
  apply Subtype.ext
  exact sub_eq_zero.mp htzero

/-- The converse to zero restriction is precisely faithfulness of the
homogeneous-to-section map on the quotient. -/
theorem positiveQuotientRestrictionSections_zero_iff_gradedKer_of_injective
    (I J : HomogeneousIdeal PS) (hIJ : I.toIdeal ≤ J.toIdeal)
    (m : ℕ) (z : grading I m)
    (hfaithful : Function.Injective
      (positiveGlobalSectionOfHomogeneous (grading J) m)) :
    positiveQuotientRestrictionSections I J hIJ m
        (positiveGlobalSectionOfHomogeneous (grading I) m z) =
          positiveGlobalSectionOfHomogeneous (grading J) m 0 ↔
      z ∈ LinearMap.ker (gradedQuotientPieceLinearMap I J hIJ m) := by
  constructor
  · intro hz
    apply LinearMap.mem_ker.mpr
    apply hfaithful
    exact (positiveQuotientRestrictionSections_homogeneous I J hIJ m z).symm.trans hz
  · exact positiveQuotientRestrictionSections_homogeneousZero_of_gradedKer
      I J hIJ m z

/-- For the actual conic immersion, faithfulness of its homogeneous section
map identifies literal zero restriction with the twelve-dimensional cubic
coordinate system containing the conic. -/
theorem cubicToPlaneConic_sectionRestriction_zero_iff_cubicSystem_of_faithful
    (p ell q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hell : ell.IsHomogeneous 1)
    (hq : q.IsHomogeneous 2)
    (hpc : p ∈ Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K)))
    (hfaithful : Function.Injective
      (positiveGlobalSectionOfHomogeneous
        (grading (planeConicHomogeneousIdeal ell q hell hq)) 3))
    (z : grading (equationIdeal p hp) 3) :
    positiveQuotientRestrictionSections
        (equationIdeal p hp) (planeConicHomogeneousIdeal ell q hell hq)
        (equationIdeal_le_planeConicHomogeneousIdeal p ell q hp hell hq hpc) 3
        (positiveGlobalSectionOfHomogeneous (grading (equationIdeal p hp)) 3 z) =
      positiveGlobalSectionOfHomogeneous
        (grading (planeConicHomogeneousIdeal ell q hell hq)) 3 0 ↔
      z ∈ fixedCurveCubicSurfaceSystem p hp
        (planeConicHomogeneousIdeal ell q hell hq) := by
  rw [← cubicToPlaneConic_gradedRestriction_ker p ell q hp hell hq hpc]
  exact positiveQuotientRestrictionSections_zero_iff_gradedKer_of_injective
    (equationIdeal p hp) (planeConicHomogeneousIdeal ell q hell hq)
    (equationIdeal_le_planeConicHomogeneousIdeal p ell q hp hell hq hpc)
    3 z hfaithful

/-- Literal cubic restriction to any genuine plane conic has exactly the
fixed-conic cubic system as its kernel. The conic may be reducible or
nonreduced. -/
theorem cubicToPlaneConic_sectionRestriction_zero_iff_cubicSystem
    (p ell q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hell : ell.IsHomogeneous 1)
    (hell0 : ell ≠ 0) (hq : q.IsHomogeneous 2)
    (hpc : p ∈ Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K)))
    (z : grading (equationIdeal p hp) 3) :
    positiveQuotientRestrictionSections
        (equationIdeal p hp) (planeConicHomogeneousIdeal ell q hell hq)
        (equationIdeal_le_planeConicHomogeneousIdeal p ell q hp hell hq hpc) 3
        (positiveGlobalSectionOfHomogeneous (grading (equationIdeal p hp)) 3 z) =
      positiveGlobalSectionOfHomogeneous
        (grading (planeConicHomogeneousIdeal ell q hell hq)) 3 0 ↔
      z ∈ fixedCurveCubicSurfaceSystem p hp
        (planeConicHomogeneousIdeal ell q hell hq) := by
  exact cubicToPlaneConic_sectionRestriction_zero_iff_cubicSystem_of_faithful
    p ell q hp hell hq hpc
    (planeConic_positiveGlobalSectionOfHomogeneous_injective
      ell q hell hell0 hq 3) z

/-- The cubic restriction map as a ground-field-linear map into actual
positive-twist global sections on the plane conic. -/
noncomputable def cubicToPlaneConicPositiveGlobalSectionLinearMap
    (p ell q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hell : ell.IsHomogeneous 1)
    (hq : q.IsHomogeneous 2)
    (hpc : p ∈ Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K))) :=
  (positiveHomogeneousGlobalSectionLinearMap
    (planeConicHomogeneousIdeal ell q hell hq) 3).comp
      (gradedQuotientPieceLinearMap
        (equationIdeal p hp) (planeConicHomogeneousIdeal ell q hell hq)
        (equationIdeal_le_planeConicHomogeneousIdeal p ell q hp hell hq hpc) 3)

/-- The actual conic restriction has a kernel of dimension at most twelve,
without an integrality assumption on the conic. -/
theorem cubicToPlaneConicPositiveGlobalSectionLinearMap_ker_finrank_le_twelve
    (p ell q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0)
    (hpc : p ∈ Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K))) :
    Module.finrank K
      (LinearMap.ker (cubicToPlaneConicPositiveGlobalSectionLinearMap
        p ell q hp hell hq hpc)) ≤ 12 := by
  let J := planeConicHomogeneousIdeal ell q hell hq
  have hinj : Function.Injective
      (positiveHomogeneousGlobalSectionLinearMap J 3) :=
    positiveHomogeneousGlobalSectionLinearMap_injective_of_sections_injective
      J 3 (planeConic_positiveGlobalSectionOfHomogeneous_injective
        ell q hell hell0 hq 3)
  have hker : LinearMap.ker
      (cubicToPlaneConicPositiveGlobalSectionLinearMap
        p ell q hp hell hq hpc) =
      LinearMap.ker (gradedQuotientPieceLinearMap
        (equationIdeal p hp) J
        (equationIdeal_le_planeConicHomogeneousIdeal p ell q hp hell hq hpc) 3) := by
    ext z
    simp only [LinearMap.mem_ker]
    change positiveHomogeneousGlobalSectionLinearMap J 3
      (gradedQuotientPieceLinearMap
        (equationIdeal p hp) J
        (equationIdeal_le_planeConicHomogeneousIdeal p ell q hp hell hq hpc) 3 z) = 0 ↔
      gradedQuotientPieceLinearMap
        (equationIdeal p hp) J
        (equationIdeal_le_planeConicHomogeneousIdeal p ell q hp hell hq hpc) 3 z = 0
    exact hinj.eq_iff' (by simp)
  rw [hker]
  exact cubicToPlaneConic_gradedRestriction_ker_finrank_le_twelve
    p ell q hp hell hq hp0 hell0 hq0 hpc

/-- A plane conic on a nonzero cubic imposes at least seven independent
conditions on its cubic coordinate sections, measured in the actual sheaf
section space of the conic. Reducible and nonreduced conics are included. -/
theorem cubicToPlaneConicPositiveGlobalSectionLinearMap_range_finrank_ge_seven
    (p ell q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0)
    (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0)
    (hpc : p ∈ Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K))) :
    7 ≤ Module.finrank K
      (LinearMap.range (cubicToPlaneConicPositiveGlobalSectionLinearMap
        p ell q hp hell hq hpc)) := by
  let f := cubicToPlaneConicPositiveGlobalSectionLinearMap
    p ell q hp hell hq hpc
  letI : Module.Finite K (grading (equationIdeal p hp) 3) :=
    polynomialQuotientGrade_finite (equationIdeal p hp) 3
  have hker : Module.finrank K (LinearMap.ker f) ≤ 12 :=
    cubicToPlaneConicPositiveGlobalSectionLinearMap_ker_finrank_le_twelve
      p ell q hp hp0 hell hell0 hq hq0 hpc
  have hdim : Module.finrank K (grading (equationIdeal p hp) 3) = 19 :=
    cubicSurface_grade_three_finrank p hp hp0
  have hrank := f.finrank_range_add_finrank_ker
  change 7 ≤ Module.finrank K (LinearMap.range f)
  omega

/-- The same literal conic restriction statement for an integral conic.
This compatibility theorem retains the older domain-based interface. -/
theorem cubicToPlaneConic_sectionRestriction_zero_iff_cubicSystem_of_domain
    (p ell q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hell : ell.IsHomogeneous 1)
    (hq : q.IsHomogeneous 2)
    (hpc : p ∈ Ideal.span ({ell, q} : Set (MvPolynomial (Fin 4) K)))
    [IsDomain (CoordinateRing (planeConicHomogeneousIdeal ell q hell hq))]
    (z : grading (equationIdeal p hp) 3) :
    positiveQuotientRestrictionSections
        (equationIdeal p hp) (planeConicHomogeneousIdeal ell q hell hq)
        (equationIdeal_le_planeConicHomogeneousIdeal p ell q hp hell hq hpc) 3
        (positiveGlobalSectionOfHomogeneous (grading (equationIdeal p hp)) 3 z) =
      positiveGlobalSectionOfHomogeneous
        (grading (planeConicHomogeneousIdeal ell q hell hq)) 3 0 ↔
      z ∈ fixedCurveCubicSurfaceSystem p hp
        (planeConicHomogeneousIdeal ell q hell hq) := by
  haveI : Nonempty (scheme (planeConicHomogeneousIdeal ell q hell hq)) :=
    planeConicScheme_nonempty ell q hell hq
  exact cubicToPlaneConic_sectionRestriction_zero_iff_cubicSystem_of_faithful
    p ell q hp hell hq hpc
    (positiveGlobalSectionOfHomogeneous_injective
      (planeConicHomogeneousIdeal ell q hell hq) 3) z

end PfaffianDescent.ProjectiveNegativeTwist
