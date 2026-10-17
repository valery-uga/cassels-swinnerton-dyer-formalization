import PfaffianDescent.VoisinSelectedActualFiniteNeighborhood
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.AlgebraicGeometry.FunctionField

/-! Function fields of the compatible ordered and unordered affine charts. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory

universe u

/-- An open immersion of integral schemes identifies their function fields
through its isomorphism on stalks at the generic points. -/
noncomputable def openImmersion_functionFieldEquiv
    {Q X : Scheme.{u}} [IsIntegral Q] [IsIntegral X]
    (j : Q ⟶ X) [IsOpenImmersion j] :
    Q.functionField ≃+* X.functionField := by
  have hgen : j (genericPoint Q) = genericPoint X :=
    genericPoint_eq_of_isOpenImmersion j
  let e : X.functionField ≅ Q.functionField := by
    simpa only [Scheme.functionField, ← hgen] using
      (asIso (j.stalkMap (genericPoint Q)))
  exact e.symm.commRingCatIsoToRingEquiv

/-- An integral affine chart of an integral scheme has exactly the scheme's
function field. -/
noncomputable def affineOpenImmersion_fractionEquivFunctionField
    {Q X : Scheme.{u}} [IsAffine Q] [IsIntegral Q] [IsIntegral X]
    (j : Q ⟶ X) [IsOpenImmersion j] :
    FractionRing Γ(Q, ⊤) ≃+* X.functionField := by
  letI : Nonempty (⊤ : Q.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty Q), trivial⟩⟩
  letI : IsFractionRing Γ(Q, ⊤) Q.functionField :=
    functionField_isFractionRing_of_isAffineOpen Q ⊤ (isAffineOpen_top Q)
  exact (FractionRing.algEquiv Γ(Q, ⊤) Q.functionField).toRingEquiv.trans
    (openImmersion_functionFieldEquiv j)

/-- A surjective map between integral affine charts is injective on global
functions. This is the algebraic input for their function-field extension. -/
theorem affineSurjectiveIntegral_appTop_injective
    {U Q : Scheme.{u}} [IsAffine U] [IsAffine Q]
    [IsIntegral U] [IsIntegral Q]
    (r : U ⟶ Q) [Surjective r] :
    Function.Injective r.appTop.hom := by
  letI : IsSchemeTheoreticallyDominant r :=
    IsSchemeTheoreticallyDominant.of_isDominant r
  letI : QuasiCompact r := inferInstance
  exact r.app_injective ⊤

/-- The quotient chart's fraction field embeds into the ordered chart's
fraction field via the actual quotient morphism. -/
noncomputable def affineSurjectiveIntegral_fractionMap
    {U Q : Scheme.{u}} [IsAffine U] [IsAffine Q]
    [IsIntegral U] [IsIntegral Q]
    (r : U ⟶ Q) [Surjective r] :
    FractionRing Γ(Q, ⊤) →+* FractionRing Γ(U, ⊤) := by
  let g : Γ(Q, ⊤) →+* FractionRing Γ(U, ⊤) :=
    (algebraMap Γ(U, ⊤) (FractionRing Γ(U, ⊤))).comp r.appTop.hom
  have hg : Function.Injective g :=
    (IsFractionRing.injective Γ(U, ⊤) (FractionRing Γ(U, ⊤))).comp
      (affineSurjectiveIntegral_appTop_injective r)
  exact IsFractionRing.lift hg

theorem affineSurjectiveIntegral_fractionMap_commutes
    {U Q : Scheme.{u}} [IsAffine U] [IsAffine Q]
    [IsIntegral U] [IsIntegral Q]
    (r : U ⟶ Q) [Surjective r]
    (a : Γ(Q, ⊤)) :
    affineSurjectiveIntegral_fractionMap r
      (algebraMap Γ(Q, ⊤) (FractionRing Γ(Q, ⊤)) a) =
      algebraMap Γ(U, ⊤) (FractionRing Γ(U, ⊤)) (r.appTop.hom a) := by
  let g : Γ(Q, ⊤) →+* FractionRing Γ(U, ⊤) :=
    (algebraMap Γ(U, ⊤) (FractionRing Γ(U, ⊤))).comp r.appTop.hom
  have hg : Function.Injective g :=
    (IsFractionRing.injective Γ(U, ⊤) (FractionRing Γ(U, ⊤))).comp
      (affineSurjectiveIntegral_appTop_injective r)
  change IsFractionRing.lift hg
    (algebraMap Γ(Q, ⊤) (FractionRing Γ(Q, ⊤)) a) = g a
  exact IsFractionRing.lift_algebraMap hg a

theorem affineSurjectiveIntegral_fractionMap_injective
    {U Q : Scheme.{u}} [IsAffine U] [IsAffine Q]
    [IsIntegral U] [IsIntegral Q]
    (r : U ⟶ Q) [Surjective r] :
    Function.Injective (affineSurjectiveIntegral_fractionMap r) :=
  (affineSurjectiveIntegral_fractionMap r).injective

theorem affineSurjectiveIntegral_fractionFaithfulSMul
    {U Q : Scheme.{u}} [IsAffine U] [IsAffine Q]
    [IsIntegral U] [IsIntegral Q]
    (r : U ⟶ Q) [Surjective r] :
    letI : Algebra Γ(Q, ⊤) Γ(U, ⊤) := r.appTop.hom.toAlgebra
    FaithfulSMul Γ(Q, ⊤) (FractionRing Γ(U, ⊤)) := by
  letI : Algebra Γ(Q, ⊤) Γ(U, ⊤) := r.appTop.hom.toAlgebra
  exact (faithfulSMul_iff_algebraMap_injective Γ(Q, ⊤)
    (FractionRing Γ(U, ⊤))).mpr
    ((IsFractionRing.injective Γ(U, ⊤) (FractionRing Γ(U, ⊤))).comp
      (affineSurjectiveIntegral_appTop_injective r))

/-- An integral quotient chart induces an algebraic extension of function
fields.  This identifies the algebraic nature of the ordered/unordered
field comparison used in the selected configuration. -/
theorem affineIntegral_fractionMap_isAlgebraic
    {U Q : Scheme.{u}} [IsAffine U] [IsAffine Q]
    [IsIntegral U] [IsIntegral Q]
    (r : U ⟶ Q) [Surjective r] [IsIntegralHom r] :
    letI : Algebra Γ(Q, ⊤) Γ(U, ⊤) := r.appTop.hom.toAlgebra
    letI : FaithfulSMul Γ(Q, ⊤) (FractionRing Γ(U, ⊤)) :=
      affineSurjectiveIntegral_fractionFaithfulSMul r
    letI := FractionRing.liftAlgebra Γ(Q, ⊤) (FractionRing Γ(U, ⊤))
    Algebra.IsAlgebraic (FractionRing Γ(Q, ⊤))
      (FractionRing Γ(U, ⊤)) := by
  letI : Algebra Γ(Q, ⊤) Γ(U, ⊤) := r.appTop.hom.toAlgebra
  letI : FaithfulSMul Γ(Q, ⊤) (FractionRing Γ(U, ⊤)) :=
    affineSurjectiveIntegral_fractionFaithfulSMul r
  letI := FractionRing.liftAlgebra Γ(Q, ⊤) (FractionRing Γ(U, ⊤))
  letI : IsScalarTower Γ(Q, ⊤) Γ(U, ⊤) (FractionRing Γ(U, ⊤)) :=
    inferInstance
  letI : IsScalarTower Γ(Q, ⊤) (FractionRing Γ(Q, ⊤))
      (FractionRing Γ(U, ⊤)) :=
    FractionRing.isScalarTower_liftAlgebra Γ(Q, ⊤) (FractionRing Γ(U, ⊤))
  haveI : Algebra.IsIntegral Γ(Q, ⊤) Γ(U, ⊤) :=
    algebraMap_isIntegral_iff.mp (r.isIntegral_app ⊤ (isAffineOpen_top Q))
  exact isAlgebraic_of_isFractionRing Γ(Q, ⊤) Γ(U, ⊤)
    (FractionRing Γ(Q, ⊤)) (FractionRing Γ(U, ⊤))

/-- A finite surjective affine quotient gives a finite-dimensional extension
of the chart function fields. -/
theorem affineFinite_fractionMap_finiteDimensional
    {U Q : Scheme.{u}} [IsAffine U] [IsAffine Q]
    [IsIntegral U] [IsIntegral Q]
    (r : U ⟶ Q) [Surjective r] [IsFinite r] :
    letI : Algebra Γ(Q, ⊤) Γ(U, ⊤) := r.appTop.hom.toAlgebra
    letI : FaithfulSMul Γ(Q, ⊤) (FractionRing Γ(U, ⊤)) :=
      affineSurjectiveIntegral_fractionFaithfulSMul r
    letI := FractionRing.liftAlgebra Γ(Q, ⊤) (FractionRing Γ(U, ⊤))
    FiniteDimensional (FractionRing Γ(Q, ⊤))
      (FractionRing Γ(U, ⊤)) := by
  letI : Algebra Γ(Q, ⊤) Γ(U, ⊤) := r.appTop.hom.toAlgebra
  letI : FaithfulSMul Γ(Q, ⊤) (FractionRing Γ(U, ⊤)) :=
    affineSurjectiveIntegral_fractionFaithfulSMul r
  letI := FractionRing.liftAlgebra Γ(Q, ⊤) (FractionRing Γ(U, ⊤))
  haveI : Module.Finite Γ(Q, ⊤) Γ(U, ⊤) :=
    RingHom.finite_algebraMap.mp r.finite_appTop
  haveI : Module.IsTorsionFree Γ(Q, ⊤) Γ(U, ⊤) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr
      (affineSurjectiveIntegral_appTop_injective r)
  infer_instance

theorem affineSurjectiveIntegral_genericPoint_map
    {U Q : Scheme.{u}} [IsIntegral U] [IsIntegral Q]
    (r : U ⟶ Q) [Surjective r] :
    r (genericPoint U) = genericPoint Q :=
  AllCharacteristics.genericPoint_map_of_surjective r

/-- The unordered chart function field embeds in the fraction field of any
nonzero principal localization of the ordered chart. -/
noncomputable def affineSurjectiveIntegral_localizedFractionMap
    {U Q : Scheme.{u}} [IsAffine U] [IsAffine Q]
    [IsIntegral U] [IsIntegral Q]
    (r : U ⟶ Q) [Surjective r]
    (m : Γ(U, ⊤)) (hm : m ≠ 0) :
    FractionRing Γ(Q, ⊤) →+* FractionRing (Localization.Away m) := by
  letI : IsDomain (Localization.Away m) := Localization.Away.isDomain hm
  let loc : Γ(U, ⊤) →+* Localization.Away m :=
    algebraMap Γ(U, ⊤) (Localization.Away m)
  have hloc : Function.Injective loc :=
    IsLocalization.injective (Localization.Away m)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hm)
  let g : Γ(Q, ⊤) →+* FractionRing (Localization.Away m) :=
    (algebraMap (Localization.Away m) (FractionRing (Localization.Away m))).comp
      (loc.comp r.appTop.hom)
  have hg : Function.Injective g :=
    (IsFractionRing.injective (Localization.Away m)
      (FractionRing (Localization.Away m))).comp
      (hloc.comp (affineSurjectiveIntegral_appTop_injective r))
  exact IsFractionRing.lift hg

theorem affineSurjectiveIntegral_localizedFractionMap_commutes
    {U Q : Scheme.{u}} [IsAffine U] [IsAffine Q]
    [IsIntegral U] [IsIntegral Q]
    (r : U ⟶ Q) [Surjective r]
    (m : Γ(U, ⊤)) (hm : m ≠ 0)
    (a : Γ(Q, ⊤)) :
    affineSurjectiveIntegral_localizedFractionMap r m hm
      (algebraMap Γ(Q, ⊤) (FractionRing Γ(Q, ⊤)) a) =
      algebraMap (Localization.Away m) (FractionRing (Localization.Away m))
        (algebraMap Γ(U, ⊤) (Localization.Away m) (r.appTop.hom a)) := by
  letI : IsDomain (Localization.Away m) := Localization.Away.isDomain hm
  let loc : Γ(U, ⊤) →+* Localization.Away m :=
    algebraMap Γ(U, ⊤) (Localization.Away m)
  have hloc : Function.Injective loc :=
    IsLocalization.injective (Localization.Away m)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hm)
  let g : Γ(Q, ⊤) →+* FractionRing (Localization.Away m) :=
    (algebraMap (Localization.Away m) (FractionRing (Localization.Away m))).comp
      (loc.comp r.appTop.hom)
  have hg : Function.Injective g :=
    (IsFractionRing.injective (Localization.Away m)
      (FractionRing (Localization.Away m))).comp
      (hloc.comp (affineSurjectiveIntegral_appTop_injective r))
  change IsFractionRing.lift hg
    (algebraMap Γ(Q, ⊤) (FractionRing Γ(Q, ⊤)) a) = g a
  exact IsFractionRing.lift_algebraMap hg a

theorem affineSurjectiveIntegral_localizedFractionMap_injective
    {U Q : Scheme.{u}} [IsAffine U] [IsAffine Q]
    [IsIntegral U] [IsIntegral Q]
    (r : U ⟶ Q) [Surjective r]
    (m : Γ(U, ⊤)) (hm : m ≠ 0) :
    Function.Injective (affineSurjectiveIntegral_localizedFractionMap r m hm) := by
  letI : IsDomain (Localization.Away m) := Localization.Away.isDomain hm
  exact (affineSurjectiveIntegral_localizedFractionMap r m hm).injective

end PfaffianDescent
