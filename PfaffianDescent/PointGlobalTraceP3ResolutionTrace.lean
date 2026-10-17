import PfaffianDescent.PointGlobalTraceAmbientTwistExtVanishing
import PfaffianDescent.PointGlobalTraceAmbientResolutionPullback
import PfaffianDescent.P3CanonicalCohomologyTrace

/-! # The actual ambient trace from a geometrically identified point resolution

Only the resolution and its geometric term identifications remain inputs.
The six Ext vanishings and the ambient canonical trace are constructed
internally. The forward map is the actual augmentation followed by that trace.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The actual augmentation pullback is an equivalence after the native
Koszul terms are identified. No Ext vanishing is a premise. -/
def pointGlobalTraceP3ResolutionTraceEquiv
    [hExt : HasExt.{u} (Proj PS).Modules]
    (R : ThreeStepResolution (Proj PS).Modules)
    (e₀ : R.C₀ ≅ SheafOfModules.unit (Proj PS).ringCatSheaf)
    (e₁ : R.C₁ ≅ ⨁ pointGlobalTraceP3CoordinateTriple K 1)
    (e₂ : R.C₂ ≅ ⨁ pointGlobalTraceP3CoordinateTriple K 2)
    (e₃ : R.K₂ ≅ sheafOfModules PS 3) :
    Ext.{u} (C := (Proj PS).Modules) R.P (sheafOfModules PS 4) 3 ≃+ K := by
  letI := p3CanonicalTripleTwistExt_1_2_subsingleton K
  letI := p3CanonicalTripleTwistExt_1_3_subsingleton K
  letI := p3CanonicalTripleTwistExt_2_1_subsingleton K
  letI := p3CanonicalTripleTwistExt_2_2_subsingleton K
  letI := p3CanonicalTwistExt_3_0_subsingleton K
  letI := p3CanonicalTwistExt_3_1_subsingleton K
  letI : Subsingleton (Ext.{u} (C := (Proj PS).Modules) R.C₁ (sheafOfModules PS 4) 2) :=
    ext_subsingleton_of_iso_left e₁.symm 2
  letI : Subsingleton (Ext.{u} (C := (Proj PS).Modules) R.C₁ (sheafOfModules PS 4) 3) :=
    ext_subsingleton_of_iso_left e₁.symm 3
  letI : Subsingleton (Ext.{u} (C := (Proj PS).Modules) R.C₂ (sheafOfModules PS 4) 1) :=
    ext_subsingleton_of_iso_left e₂.symm 1
  letI : Subsingleton (Ext.{u} (C := (Proj PS).Modules) R.C₂ (sheafOfModules PS 4) 2) :=
    ext_subsingleton_of_iso_left e₂.symm 2
  letI : Subsingleton (Ext.{u} (C := (Proj PS).Modules) R.K₂ (sheafOfModules PS 4) 0) :=
    ext_subsingleton_of_iso_left e₃.symm 0
  letI : Subsingleton (Ext.{u} (C := (Proj PS).Modules) R.K₂ (sheafOfModules PS 4) 1) :=
    ext_subsingleton_of_iso_left e₃.symm 1
  let ePull : Ext.{u} (C := (Proj PS).Modules) R.P (sheafOfModules PS 4) 3 ≃+
      Ext.{u} (C := (Proj PS).Modules) R.C₀ (sheafOfModules PS 4) 3 :=
    pointGlobalTraceAmbientResolutionPullbackEquiv.{u + 1, u, u}
      R (sheafOfModules PS 4)
  let eUnit : Ext.{u} (C := (Proj PS).Modules) R.C₀ (sheafOfModules PS 4) 3 ≃+
      schemeModuleCohomology (Proj PS) (sheafOfModules PS 4) 3 :=
    extPrecompIsoOfIso e₀
  exact ePull.trans (eUnit.trans (p3NegativeFourCohomologyThreeTraceEquiv K))

/-- The equivalence evaluates the actual unit-source augmentation, rather
than an arbitrary scalar coordinate on the point Ext group. -/
theorem pointGlobalTraceP3ResolutionTraceEquiv_apply
    [hExt : HasExt.{u} (Proj PS).Modules]
    (R : ThreeStepResolution (Proj PS).Modules)
    (e₀ : R.C₀ ≅ SheafOfModules.unit (Proj PS).ringCatSheaf)
    (e₁ : R.C₁ ≅ ⨁ pointGlobalTraceP3CoordinateTriple K 1)
    (e₂ : R.C₂ ≅ ⨁ pointGlobalTraceP3CoordinateTriple K 2)
    (e₃ : R.K₂ ≅ sheafOfModules PS 3)
    (z : Ext.{u} (C := (Proj PS).Modules) R.P (sheafOfModules PS 4) 3) :
    pointGlobalTraceP3ResolutionTraceEquiv K R e₀ e₁ e₂ e₃ z =
      p3NegativeFourCohomologyThreeTraceEquiv K
        ((Ext.mk₀.{u} (C := (Proj PS).Modules) (e₀.inv ≫ R.p₀)).comp z
          (zero_add 3)) := by
  change p3NegativeFourCohomologyThreeTraceEquiv K
    ((Ext.mk₀ e₀.inv).comp ((Ext.mk₀ R.p₀).comp z (zero_add 3)) (zero_add 3)) = _
  rw [Ext.mk₀_comp_mk₀_assoc]

/-- Such an actual point resolution produces a class whose actual
augmentation pullback has canonical ambient trace one. -/
theorem pointGlobalTraceP3Resolution_exists_trace_one
    [hExt : HasExt.{u} (Proj PS).Modules]
    (R : ThreeStepResolution (Proj PS).Modules)
    (e₀ : R.C₀ ≅ SheafOfModules.unit (Proj PS).ringCatSheaf)
    (e₁ : R.C₁ ≅ ⨁ pointGlobalTraceP3CoordinateTriple K 1)
    (e₂ : R.C₂ ≅ ⨁ pointGlobalTraceP3CoordinateTriple K 2)
    (e₃ : R.K₂ ≅ sheafOfModules PS 3) :
    ∃ z : Ext.{u} (C := (Proj PS).Modules) R.P (sheafOfModules PS 4) 3,
      p3NegativeFourCohomologyThreeTraceEquiv K
        ((Ext.mk₀.{u} (C := (Proj PS).Modules) (e₀.inv ≫ R.p₀)).comp z
          (zero_add 3)) = 1 := by
  let E := pointGlobalTraceP3ResolutionTraceEquiv K R e₀ e₁ e₂ e₃
  refine ⟨E.symm 1, ?_⟩
  rw [← pointGlobalTraceP3ResolutionTraceEquiv_apply K R e₀ e₁ e₂ e₃]
  exact E.apply_symm_apply 1

end PfaffianDescent.ProjectiveNegativeTwist
