import PfaffianDescent.CorayFiniteSchemeGenericNormalization
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Actual integrally closed charts and stalks of generic-point normalization

The installed relative-normalization gluing identifies actual affine preimage
sections with an integral closure. The actual generic-point preimage identifies
its ambient ring with the actual function field, preserving the chart algebra.
This constructs integrally closed actual sections and actual stalk rings.

No normality, regularity, finite normalization, or genus certificate is assumed.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

/-- Actual sections of the actual normalized affine preimage are the actual
integral closure of the original affine chart in the actual function field. -/
def integralGenericNormalization_preimageSectionsRingEquiv
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    Γ((X.fromSpecStalk (genericPoint X)).normalization,
      (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) ≃+*
        integralClosure Γ(X, U) X.functionField := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let f := X.fromSpecStalk (genericPoint X)
  letI : Algebra Γ(X, U) Γ(Spec X.functionField, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let sectionEquiv : Γ(Spec X.functionField, f ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] X.functionField :=
    AlgEquiv.ofBijective
      { toRingHom := (integralGenericPointPreimageSectionsIso X U).hom.hom
        commutes' := fun r => by
          exact ConcreteCategory.congr_hom (integralGenericPointPreimageSectionsIso_comp_app X U) r }
      (ConcreteCategory.bijective_of_isIso (integralGenericPointPreimageSectionsIso X U).hom)
  exact (f.normalizationObjIso hU).commRingCatIsoToRingEquiv.trans
    sectionEquiv.mapIntegralClosure.toRingEquiv

/-- The actual normalized preimage section ring is a domain, derived from
its actual embedding in the function field through the constructed chart iso. -/
theorem integralGenericNormalization_preimageSections_isDomain
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    IsDomain Γ((X.fromSpecStalk (genericPoint X)).normalization,
      (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  exact MulEquiv.isDomain _
    (integralGenericNormalization_preimageSectionsRingEquiv X U hU).toMulEquiv

/-- Integral closedness of actual normalized affine-preimage sections is
constructed from their actual integral closure in the actual fraction field. -/
theorem integralGenericNormalization_preimageSections_isIntegrallyClosed
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    IsIntegrallyClosed Γ((X.fromSpecStalk (genericPoint X)).normalization,
      (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsFractionRing (integralClosure Γ(X, U) X.functionField) X.functionField :=
    integralClosure.isFractionRing_of_finite_extension X.functionField X.functionField
  letI : IsIntegrallyClosed (integralClosure Γ(X, U) X.functionField) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn X.functionField).mpr inferInstance
  exact IsIntegrallyClosed.of_equiv
    (integralGenericNormalization_preimageSectionsRingEquiv X U hU).symm

/-- Every actual stalk of the actual canonical generic-point normalization
is integrally closed. The affine neighborhood and its actual localization
presentation are constructed, not supplied as a normality certificate. -/
theorem integralGenericNormalization_stalk_isIntegrallyClosed
    (X : Scheme.{u}) [IsIntegral X] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    ∀ y : (X.fromSpecStalk (genericPoint X)).normalization,
      IsIntegrallyClosed ((X.fromSpecStalk (genericPoint X)).normalization.presheaf.stalk y) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let f := X.fromSpecStalk (genericPoint X)
  intro y
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := f.fromNormalization y) (U := ⊤) (by simp)
  letI : Nonempty U := ⟨⟨f.fromNormalization y, hyU⟩⟩
  let V := f.fromNormalization ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f.fromNormalization
  have hyV : y ∈ V := hyU
  letI : IsDomain Γ(f.normalization, V) :=
    integralGenericNormalization_preimageSections_isDomain X U hU
  letI : IsIntegrallyClosed Γ(f.normalization, V) :=
    integralGenericNormalization_preimageSections_isIntegrallyClosed X U hU
  letI : Algebra Γ(f.normalization, V) (f.normalization.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk f.normalization.presheaf ⟨y, hyV⟩
  let P := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
  letI : IsLocalization P.primeCompl (f.normalization.presheaf.stalk y) :=
    hV.isLocalization_stalk ⟨y, hyV⟩
  exact isIntegrallyClosed_of_isLocalization (f.normalization.presheaf.stalk y)
    P.primeCompl P.primeCompl_le_nonZeroDivisors

end PfaffianDescent.Coray
