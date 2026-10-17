import PfaffianDescent.CorayNormalizationDefectLocalizationComparison

/-! Localization of the SAME literal defect into any actual localization ring
and the SAME actual ambient fraction field. In particular Rf may be a native
scheme stalk with its germ algebra. No native sheaf comparison is assumed.
SOURCE ONLY / UNVERIFIED. Root owns compiler and acceptance checks. -/
noncomputable section
namespace PfaffianDescent.Coray
open Algebra Module
open scoped nonZeroDivisors
attribute [local instance] LocalizedModule.moduleOfIsLocalization

private theorem localized_algebraRange_eq_native
    {A D E Rf : Type*} [CommRing A] [CommRing D] [CommRing E] [CommRing Rf]
    [Algebra A D] [Algebra A E]
    (S : Submonoid A) [Algebra A Rf] [IsLocalization S Rf] [Algebra Rf E]
    [IsScalarTower A (Rf) E]
    (i : D →ₐ[A] E) [IsLocalizedModule S i.toLinearMap] :
    (LinearMap.range (Algebra.linearMap A D)).localized'
        (Rf) S i.toLinearMap =
      LinearMap.range (Algebra.linearMap (Rf) E) := by
  rw [Submodule.localized'_eq_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨z, ⟨a, rfl⟩, rfl⟩
    refine ⟨algebraMap A (Rf) a, ?_⟩
    change algebraMap (Rf) E (algebraMap A (Rf) a) =
      i (algebraMap A D a)
    exact (IsScalarTower.algebraMap_apply A (Rf) E a).symm.trans
      (i.commutes a).symm
  · rintro y ⟨l, rfl⟩
    have h1 : (1 : E) ∈ Submodule.span (Rf)
        (i.toLinearMap '' (LinearMap.range (Algebra.linearMap A D) : Set D)) := by
      apply Submodule.subset_span
      refine ⟨1, ⟨1, by simp⟩, by simp⟩
    have h := (Submodule.span (Rf)
      (i.toLinearMap '' (LinearMap.range (Algebra.linearMap A D) : Set D))).smul_mem l h1
    change algebraMap (Rf) E l ∈ Submodule.span (Rf)
      (i.toLinearMap '' (LinearMap.range (Algebra.linearMap A D) : Set D))
    simpa only [Algebra.smul_def, mul_one] using h

/-- The quotient by the ring image commutes with an actual module
localization. Its target is the literal quotient by the localized ring image. -/
def algebraRangeQuotientLocalizationEquiv_native
    {A D E Rf : Type*} [CommRing A] [CommRing D] [CommRing E] [CommRing Rf]
    [Algebra A D] [Algebra A E]
    (S : Submonoid A) [Algebra A Rf] [IsLocalization S Rf] [Algebra Rf E]
    [IsScalarTower A (Rf) E]
    (i : D →ₐ[A] E) [IsLocalizedModule S i.toLinearMap] :
    LocalizedModule S (D ⧸ LinearMap.range (Algebra.linearMap A D)) ≃ₗ[Rf]
      E ⧸ LinearMap.range (Algebra.linearMap (Rf) E) := by
  let N := LinearMap.range (Algebra.linearMap A D)
  let q := N.toLocalizedQuotient' (Rf) S i.toLinearMap
  let e := (IsLocalizedModule.iso S q).extendScalarsOfIsLocalization S Rf
  exact e.trans (Submodule.quotEquivOfEq _ _ (localized_algebraRange_eq_native (Rf := Rf) S i))

/-- The literal normalization defect localizes over the actual target ring,
not merely over an independently chosen Localization carrier. -/
def normalizationDefectLocalizationEquiv_native_commonField
    (A Rf F : Type*) [CommRing A] [IsDomain A] [CommRing Rf] [Field F]
    [Algebra A F] [IsFractionRing A F]
    (S : Submonoid A) (hS : S ≤ A⁰)
    [Algebra A Rf] [IsLocalization S Rf] [Algebra Rf F]
    [IsScalarTower A Rf F] :
    LocalizedModule S (localNormalizationDefect A F) ≃ₗ[Rf]
      localNormalizationDefect Rf F := by
  letI : IsLocalization (Algebra.algebraMapSubmonoid F S) F := by
    apply IsLocalization.of_le_isUnit
    rintro f ⟨a, ha, rfl⟩
    apply isUnit_iff_ne_zero.mpr
    apply (map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr
    exact mem_nonZeroDivisors_iff_ne_zero.mp (hS ha)
  let i : integralClosure A F →ₐ[A] integralClosure Rf F :=
    (integralClosure A F).val.codRestrict ((integralClosure Rf F).restrictScalars A)
      (fun y => y.property.tower_top)
  letI : Algebra (integralClosure A F) (integralClosure Rf F) := i.toRingHom.toAlgebra
  letI : IsScalarTower A (integralClosure A F) (integralClosure Rf F) :=
    IsScalarTower.of_algebraMap_eq (fun a => (i.commutes a).symm)
  letI : IsScalarTower (integralClosure A F) (integralClosure Rf F) F :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure A F) S)
      (integralClosure Rf F) :=
    IsLocalization.integralClosure (R := A) (S := F) (Rf := Rf) (Sf := F) S
  letI : IsLocalizedModule S i.toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  exact algebraRangeQuotientLocalizationEquiv_native (Rf := Rf) S i

/-- Restricting the native-ring-linear comparison along the SAME ground
algebra preserves both original native actions. No action is transported by
an equivalence; each K action is ordinary restriction along K -> Rf. -/
def normalizationDefectLocalizationEquiv_native_ground
    (K A Rf F : Type*) [CommRing K] [CommRing A] [IsDomain A]
    [CommRing Rf] [Field F] [Algebra A F] [IsFractionRing A F]
    (S : Submonoid A) (hS : S ≤ A⁰)
    [Algebra A Rf] [IsLocalization S Rf] [Algebra Rf F]
    [IsScalarTower A Rf F] [Algebra K Rf] :
    letI : Module K (LocalizedModule S (localNormalizationDefect A F)) :=
      Module.compHom _ (algebraMap K Rf)
    letI : Module K (localNormalizationDefect Rf F) :=
      Module.compHom _ (algebraMap K Rf)
    LocalizedModule S (localNormalizationDefect A F) ≃ₗ[K]
      localNormalizationDefect Rf F := by
  letI : Module K (LocalizedModule S (localNormalizationDefect A F)) :=
    Module.compHom _ (algebraMap K Rf)
  letI : Module K (localNormalizationDefect Rf F) :=
    Module.compHom _ (algebraMap K Rf)
  letI : IsScalarTower K Rf (LocalizedModule S (localNormalizationDefect A F)) :=
    IsScalarTower.of_compHom K Rf _
  letI : IsScalarTower K Rf (localNormalizationDefect Rf F) :=
    IsScalarTower.of_compHom K Rf _
  exact (normalizationDefectLocalizationEquiv_native_commonField A Rf F S hS).restrictScalars K

end PfaffianDescent.Coray
