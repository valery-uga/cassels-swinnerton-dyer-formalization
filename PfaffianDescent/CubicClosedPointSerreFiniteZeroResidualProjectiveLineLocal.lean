import PfaffianDescent.ProjectiveLineSmooth
import AllCharacteristics.SmoothSchemeRegularity
import AllCharacteristics.RegularLocalLowDimension
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.KrullDimension.Polynomial

/-! # Native local rings of the actual parameter line -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_projectiveLine_stalk_regular
    (K : Type u) [Field K] (x : projectiveLineProj K) :
    IsRegularLocalRing ((projectiveLineProj K).presheaf.stalk x) := by
  letI : IsRegularRing Γ(Spec (.of K), ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  exact AllCharacteristics.isRegularLocalRing_stalk_of_smooth_over_affine
    (projectiveLineProjToBase K) x

theorem cubicClosedPointSerreFiniteZeroResidual_projectiveLine_stalk_dim_le_one
    (K : Type u) [Field K] (x : projectiveLineProj K) :
    ringKrullDim ((projectiveLineProj K).presheaf.stalk x) ≤ 1 := by
  let e := lineGrassmannianProjIso K
  obtain ⟨b, y, hy⟩ := (projectiveLineOpenCover K).exists_eq (e.inv x)
  rw [ringKrullDim_stalk_eq_coheight,
    ← coheight_eq_of_isOpenImmersion e.inv,
    ← hy, coheight_eq_of_isOpenImmersion ((projectiveLineOpenCover K).f b)]
  change (↑(Order.coheight (y : Spec (.of (GrassmannianChartRing K 1 1)))) : WithBot ENat) ≤ 1
  rw [← idealHeight_eq_coheight]
  refine Ideal.height_le_ringKrullDim_of_isPrime.trans ?_
  simp [GrassmannianChartRing, MvPolynomial.ringKrullDim_of_isNoetherianRing]

theorem cubicClosedPointSerreFiniteZeroResidual_regularLocal_field_or_parameter_of_dim_le_one
    (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (hd : ringKrullDim R ≤ 1) :
    IsField R ∨ ∃ t : R, IsLocalRing.maximalIdeal R = Ideal.span {t} ∧
      ringKrullDim R = 1 := by
  have he := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  have hn : (IsLocalRing.maximalIdeal R).spanFinrank ≤ 1 := by
    exact_mod_cast he.trans_le hd
  have hcases : (IsLocalRing.maximalIdeal R).spanFinrank = 0 ∨
      (IsLocalRing.maximalIdeal R).spanFinrank = 1 := by omega
  rcases hcases with hzero | hone
  · left
    apply AllCharacteristics.isField_of_regularLocal_dim_zero
    rw [← he, hzero]
    rfl
  · right
    have hd₁ : ringKrullDim R = 1 := by rw [← he, hone]; rfl
    obtain ⟨t, ht⟩ := AllCharacteristics.maximalIdeal_isPrincipal_of_regularLocal_dim_one hd₁
    exact ⟨t, ht, hd₁⟩

/-- Every actual parameter stalk is a field or a one-dimensional regular
local ring with an actual principal maximal-ideal generator. -/
theorem cubicClosedPointSerreFiniteZeroResidual_projectiveLine_stalk_field_or_parameter
    (K : Type u) [Field K] (x : projectiveLineProj K) :
    IsField ((projectiveLineProj K).presheaf.stalk x) ∨
      ∃ t : (projectiveLineProj K).presheaf.stalk x,
        IsLocalRing.maximalIdeal ((projectiveLineProj K).presheaf.stalk x) = Ideal.span {t} ∧
        ringKrullDim ((projectiveLineProj K).presheaf.stalk x) = 1 := by
  letI := cubicClosedPointSerreFiniteZeroResidual_projectiveLine_stalk_regular K x
  exact cubicClosedPointSerreFiniteZeroResidual_regularLocal_field_or_parameter_of_dim_le_one
    _ (cubicClosedPointSerreFiniteZeroResidual_projectiveLine_stalk_dim_le_one K x)

theorem cubicClosedPointSerreFiniteZeroResidual_projectiveLine_open_stalk_regular
    (K : Type u) [Field K] (U : (projectiveLineProj K).Opens) (x : (U : Scheme.{u})) :
    IsRegularLocalRing ((U : Scheme.{u}).presheaf.stalk x) := by
  letI : IsRegularRing Γ(Spec (.of K), ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  exact AllCharacteristics.isRegularLocalRing_stalk_of_smooth_over_affine
    (U.ι ≫ projectiveLineProjToBase K) x

theorem cubicClosedPointSerreFiniteZeroResidual_projectiveLine_open_stalk_dim_le_one
    (K : Type u) [Field K] (U : (projectiveLineProj K).Opens) (x : (U : Scheme.{u})) :
    ringKrullDim ((U : Scheme.{u}).presheaf.stalk x) ≤ 1 := by
  rw [← ringKrullDim_eq_of_ringEquiv
    (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv]
  exact cubicClosedPointSerreFiniteZeroResidual_projectiveLine_stalk_dim_le_one K (U.ι x)

/-- The actual good open of the parameter line inherits the same native
field-or-parameter alternative at every stalk. -/
theorem cubicClosedPointSerreFiniteZeroResidual_projectiveLine_open_stalk_field_or_parameter
    (K : Type u) [Field K] (U : (projectiveLineProj K).Opens) (x : (U : Scheme.{u})) :
    IsField ((U : Scheme.{u}).presheaf.stalk x) ∨
      ∃ t : (U : Scheme.{u}).presheaf.stalk x,
        IsLocalRing.maximalIdeal ((U : Scheme.{u}).presheaf.stalk x) = Ideal.span {t} ∧
        ringKrullDim ((U : Scheme.{u}).presheaf.stalk x) = 1 := by
  letI := cubicClosedPointSerreFiniteZeroResidual_projectiveLine_open_stalk_regular K U x
  exact cubicClosedPointSerreFiniteZeroResidual_regularLocal_field_or_parameter_of_dim_le_one
    _ (cubicClosedPointSerreFiniteZeroResidual_projectiveLine_open_stalk_dim_le_one K U x)

end PfaffianDescent
