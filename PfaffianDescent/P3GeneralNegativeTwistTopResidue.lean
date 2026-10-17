import PfaffianDescent.P3CanonicalLaurentTrace
import PfaffianDescent.VoisinP3TopCechExtComparison
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.Finiteness.Basic

/-! Actual top residues for EVERY negative twist on the original P³.
Finite coordinates and an intrinsic additive injection are constructed.
No transported scalar action or original-K cohomology finiteness is asserted.
STATUS: SOURCE ONLY / UNVERIFIED. Root owns all compiler checks.
-/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentLocalization LaurentCechCore LaurentCechExact
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Exactly the polynomial exponents dual to full-negative degree -m.
The equation degree+4=m makes the index empty for m<4 without truncated
subtraction introducing spurious canonical-degree coordinates. -/
def P3TopResidueExponent (m : ℕ) : Type :=
  {b : Fin 4 →₀ ℕ // b.degree + 4 = m}

instance p3TopResidueExponent_finite (m : ℕ) : Finite (P3TopResidueExponent m) := by
  have hf : ({b : Fin 4 →₀ ℕ | b.degree + 4 = m} : Set (Fin 4 →₀ ℕ)).Finite :=
    (Finsupp.finite_of_degree_le m).subset (by
      intro b hb
      change b.degree + 4 = m at hb
      change b.degree ≤ m
      omega)
  exact hf.to_subtype

/-- The residue target has its ordinary ORIGINAL K action and is finite.
This does not assert finiteness or redefine any action on intrinsic H³. -/
theorem p3NegativeTwistResidueCoordinateModule_finite (m : ℕ) :
    Module.Finite K (P3TopResidueExponent m → K) := by
  infer_instance

/-- Actual Laurent coefficients of an actual raw top cocycle, in the finite
set of all possible full-negative degree -m exponents. -/
def p3NegativeTwistRawTopResidueCoordinates (m : ℕ) :
    P3RawTopCocycle K m →+ (P3TopResidueExponent m → K) where
  toFun w b := (p3NegativeTwistCechTermToLaurent K m 3 w.1 id).coeff
    (p3SerreDualExponent b.1)
  map_zero' := by
    funext b
    simp
  map_add' x y := by
    funext b
    simp

/-- A raw top cocycle has all actual residues zero EXACTLY when it is an
actual degree-two boundary. All representative/differential/support
compatibility is proved by the existing actual Laurent maps. -/
theorem p3NegativeTwistRawTopResidueCoordinates_zero_iff_boundary
    (m : ℕ) (w : P3RawTopCocycle K m) :
    p3NegativeTwistRawTopResidueCoordinates K m w = 0 ↔
      ∃ z : (p3NegativeTwistCechComplex (K := K) m).X 2,
        (p3NegativeTwistCechComplex (K := K) m).d 2 3 z = w.1 := by
  constructor
  · intro hzero
    let wL := p3NegativeTwistCechTermToLaurent K m 3 w.1
    have hs : ∀ f (a : LaurentLocalization.LaurentExponent), a ∈ (wL f).coeff.support →
        totalDegree a = -(m : ℤ) ∧ negativeSupport a ⊆ Set.range f := by
      intro f a ha
      exact p3NegativeTwistCechTermToLaurent_support_properties K m 3 w.1 f a ha
    have hc : ∀ f, tupleD3 wL f = 0 := by
      intro f
      rw [← congrFun (p3NegativeTwistCechTermToLaurent_d_three K m w.1) f, w.2]
      simp
    have hr : ∀ a : LaurentLocalization.LaurentExponent, totalDegree a = -(m : ℤ) →
        negativeSupport a = Set.univ → (wL id).coeff a = 0 := by
      intro a hdegree hfull
      have hrecover := p3SerreDualExponent_polynomialExponent_of_negativeSupport a hfull
      have htotal := congrArg totalDegree hrecover
      rw [p3SerreDualExponent_totalDegree, hdegree] at htotal
      have hb : (p3SerrePolynomialExponent a).degree + 4 = m := by omega
      have h := congrFun hzero (⟨p3SerrePolynomialExponent a, hb⟩ : P3TopResidueExponent m)
      change (wL id).coeff (p3SerreDualExponent (p3SerrePolynomialExponent a)) = 0 at h
      rw [hrecover] at h
      exact h
    obtain ⟨zL, hzL, hdiff⟩ :=
      laurent_tuple_exact_three_of_full_support_coefficients_zero K (-(m : ℤ)) wL hs hc hr
    obtain ⟨z, hz⟩ := exists_p3NegativeTwistCechTermToLaurent_eq_of_support K m 2 zL hzL
    refine ⟨z, ?_⟩
    apply p3NegativeTwistCechTermToLaurent_injective K m 3
    rw [p3NegativeTwistCechTermToLaurent_d_two, hz]
    funext f
    exact hdiff f
  · rintro ⟨z, hz⟩
    funext b
    change (p3NegativeTwistCechTermToLaurent K m 3 w.1 id).coeff
      (p3SerreDualExponent b.1) = 0
    rw [← hz, p3NegativeTwistCechTermToLaurent_d_two]
    apply p3SerreDualExponent_coefficient_tupleD2_eq_zero
    intro f a ha
    exact (p3NegativeTwistCechTermToLaurent_support_properties K m 2 z f a ha).2

/-- The SAME actual raw-to-Ext comparison and the general residue map have
literally equal kernels: both are the actual Cech boundaries. -/
theorem p3NegativeTwist_augmentedExt_ker_eq_residue_ker
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    (p3RawTopCocycleToAugmentedExtHom K m).ker =
      (p3NegativeTwistRawTopResidueCoordinates K m).ker := by
  ext w
  change p3RawTopCocycleToAugmentedExt K m w = 0 ↔
    p3NegativeTwistRawTopResidueCoordinates K m w = 0
  rw [p3RawTopCocycleToAugmentedExt_eq_zero_iff,
    p3NegativeTwistRawTopResidueCoordinates_zero_iff_boundary]

/-- Actual residues descend through the INTERNALLY proved raw-to-Ext
surjection and kernel equality. No comparison/descent certificate is input. -/
def p3NegativeTwistAugmentedExtResidueHom
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    Ext.{u} (p3SectionRepresenterCechTarget K) (sheafOfModules PS m) 3 →+
      (P3TopResidueExponent m → K) :=
  (p3RawTopCocycleToAugmentedExtHom K m).liftOfSurjective
    (p3RawTopCocycleToAugmentedExt_surjective K m)
    ⟨p3NegativeTwistRawTopResidueCoordinates K m,
      le_of_eq (p3NegativeTwist_augmentedExt_ker_eq_residue_ker K m)⟩

/-- Evaluation on the original raw representative is the literal original
Laurent coefficient map, after actual Ext descent. -/
theorem p3NegativeTwistAugmentedExtResidueHom_raw
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) (w : P3RawTopCocycle K m) :
    p3NegativeTwistAugmentedExtResidueHom K m
      (p3RawTopCocycleToAugmentedExt K m w) =
        p3NegativeTwistRawTopResidueCoordinates K m w := by
  exact AddMonoidHom.liftOfRightInverse_comp_apply
    (p3RawTopCocycleToAugmentedExtHom K m)
    (Function.surjInv (p3RawTopCocycleToAugmentedExt_surjective K m))
    (Function.rightInverse_surjInv (p3RawTopCocycleToAugmentedExt_surjective K m))
    ⟨p3NegativeTwistRawTopResidueCoordinates K m,
      le_of_eq (p3NegativeTwist_augmentedExt_ker_eq_residue_ker K m)⟩ w

theorem p3NegativeTwistAugmentedExtResidueHom_injective
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    Function.Injective (p3NegativeTwistAugmentedExtResidueHom K m) := by
  apply (injective_iff_map_eq_zero (p3NegativeTwistAugmentedExtResidueHom K m)).mpr
  intro z hz
  obtain ⟨w, rfl⟩ := p3RawTopCocycleToAugmentedExt_surjective K m z
  rw [p3NegativeTwistAugmentedExtResidueHom_raw] at hz
  exact (p3RawTopCocycleToAugmentedExt_eq_zero_iff K m w).2
    ((p3NegativeTwistRawTopResidueCoordinates_zero_iff_boundary K m w).1 hz)

/-- The actual intrinsic H³, transported only by the actual unit-target
additive isomorphism, embeds into the finite residue coordinates. No K-action
on H³ is replaced or transported, and no K-linearity is assumed. -/
def p3NegativeTwistCohomologyThreeResidueHom
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    schemeModuleCohomology (Proj PS) (sheafOfModules PS m) 3 →+
      (P3TopResidueExponent m → K) :=
  (p3NegativeTwistAugmentedExtResidueHom K m).comp
    (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)).symm.toAddMonoidHom

theorem p3NegativeTwistCohomologyThreeResidueHom_injective
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    Function.Injective (p3NegativeTwistCohomologyThreeResidueHom K m) := by
  exact (p3NegativeTwistAugmentedExtResidueHom_injective K m).comp
    (extPrecompIsoOfIso (p3SectionRepresenterCechTargetIsoUnit K)).symm.injective

/-- The complete small-twist edge case: for m<4 the coordinate index is
empty, so SAME intrinsic H³ is zero. This includes m=0 and m=2. -/
theorem p3NegativeTwist_cohomology_three_subsingleton_of_lt_four
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) (hm : m < 4) :
    Subsingleton (schemeModuleCohomology (Proj PS) (sheafOfModules PS m) 3) := by
  apply subsingleton_of_forall_eq 0
  intro z
  apply p3NegativeTwistCohomologyThreeResidueHom_injective K m
  funext b
  have hb := b.property
  omega

end PfaffianDescent.ProjectiveNegativeTwist
