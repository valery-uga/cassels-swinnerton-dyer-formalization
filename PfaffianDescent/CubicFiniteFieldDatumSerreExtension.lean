import PfaffianDescent.CubicClosedDegreeElevenPointSerreExtension
import PfaffianDescent.CubicClosedPointSerreLocalFreeExistence
import PfaffianDescent.CubicClosedPointSerreQuotientSectionPencil
import AllCharacteristics.FiniteSubschemeRank
import Mathlib.Algebra.CharZero.Infinite

/-! # Native Serre construction for a rank-eleven finite field datum

The canonical spectrum of the datum's global coordinate algebra supplies
the actual closed immersion. Its algebra, finite dimension and degree are
constructed from the finite-flat datum. This is the interface used by the
generic unordered configuration, whose coordinate algebra is a field.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- The literal canonical spectrum presentation of a finite field datum
gives an actual Serre sequence with nonzero connecting product and a free
rank-two stalk at its original point. No coordinate algebra or Ext instance
is supplied as an additional assumption. -/
theorem cubicFiniteFieldDatumSerreExtension_exists_sequence
    (K : Type u) [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11)
    (hField : IsField Γ(D.val.subscheme, ⊤)) :
    letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
    letI : Field Γ(D.val.subscheme, ⊤) := hField.toField
    let i := finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D
    letI : HasExt.{u} (hypersurface p hp).Modules := schemeModules_hasExt _
    letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
    letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
    ∃ e : SerreExtensionSequenceData (hypersurface p hp)
        (closedImmersionIdealTwist i
          (positiveSheafOfModules (grading (equationIdeal p hp)) 3)),
      (closedImmersionIdealTwistSequence_shortExact i
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).extClass.comp
        (@SerreExtensionSequenceData.extensionClass.{u} (hypersurface p hp)
          (closedImmersionIdealTwist i
            (positiveSheafOfModules (grading (equationIdeal p hp)) 3)) e
          (schemeModules_hasExt (hypersurface p hp)))
        (show 1 + 1 = 2 by omega) ≠ 0 ∧
      (letI : Module ((hypersurface p hp).presheaf.stalk (i default))
          ((show (hypersurface p hp).Modules from e.E).presheaf.stalk (i default)) :=
        schemeModuleStalkModule (show (hypersurface p hp).Modules from e.E) (i default)
      Nonempty (((show (hypersurface p hp).Modules from e.E).presheaf.stalk (i default)) ≃ₗ[
        (hypersurface p hp).presheaf.stalk (i default)]
        ((hypersurface p hp).presheaf.stalk (i default)) ×
          ((hypersurface p hp).presheaf.stalk (i default)))) := by
  let f := hypersurfaceToBase p hp
  let g := D.val.subschemeι ≫ f
  letI : IsFinite g := D.property.1
  letI hLField : Field Γ(D.val.subscheme, ⊤) := hField.toField
  letI hAlg : Algebra K Γ(D.val.subscheme, ⊤) := finiteSchemeCoefficientAlgebra g
  letI hFin : Module.Finite K Γ(D.val.subscheme, ⊤) := finiteSchemeCoefficient_finite g
  let i := finiteSubschemeDatumSpecMap f D
  letI hClosed : IsClosedImmersion i := finiteSubschemeDatumSpecMap_isClosedImmersion f D
  letI hExt : HasExt.{u} (hypersurface p hp).Modules := schemeModules_hasExt _
  letI hExtAmbient : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules :=
    schemeModules_hasExt _
  letI hExtStalk : HasExt.{u+1} (ModuleCat.{u} ((hypersurface p hp).presheaf.stalk (i default))) :=
    moduleCatStalk_hasExt _
  letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits (equationIdeal p hp) 3
  letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits (equationIdeal p hp) 3
  have hi : i ≫ f = Spec.map (CommRingCat.ofHom
      (algebraMap K Γ(D.val.subscheme, ⊤))) := finiteSubschemeDatumSpecMap_toBase f D
  have hL : Module.finrank K Γ(D.val.subscheme, ⊤) = 11 := by
    rw [finiteSchemeCoefficient_finrank]
    exact finiteSubschemeDatum_finiteSchemeRank f D
  exact @cubicClosedPointSerreLocalFree_exists_sequence K _ p hp hp0 _
    Γ(D.val.subscheme, ⊤) hLField hAlg hFin inferInstance i hClosed hi
    hExtAmbient hExt hExtStalk hL

set_option backward.isDefEq.respectTransparency false in
/-- The actual canonical ideal of the same datum has a nonzero cubic
section, with all coefficient and Ext data constructed internally. -/
theorem cubicFiniteFieldDatumSerreQuotientSection_exists_nonzero
    (K : Type u) [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11)
    (hField : IsField Γ(D.val.subscheme, ⊤)) :
    ∃ t : (closedImmersionIdealTwist
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D)
        (positiveSheafOfModules (grading (equationIdeal p hp)) 3)).sections,
      t ≠ SerreExtensionData.zeroSection _ := by
  let f := hypersurfaceToBase p hp
  let g := D.val.subschemeι ≫ f
  letI : IsFinite g := D.property.1
  letI hLField : Field Γ(D.val.subscheme, ⊤) := hField.toField
  letI hAlg : Algebra K Γ(D.val.subscheme, ⊤) := finiteSchemeCoefficientAlgebra g
  letI hFin : Module.Finite K Γ(D.val.subscheme, ⊤) := finiteSchemeCoefficient_finite g
  let i := finiteSubschemeDatumSpecMap f D
  letI hClosed : IsClosedImmersion i := finiteSubschemeDatumSpecMap_isClosedImmersion f D
  letI hExtAmbient : HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules :=
    schemeModules_hasExt _
  have hi : i ≫ f = Spec.map (CommRingCat.ofHom
      (algebraMap K Γ(D.val.subscheme, ⊤))) := finiteSubschemeDatumSpecMap_toBase f D
  have hL : Module.finrank K Γ(D.val.subscheme, ⊤) = 11 := by
    rw [finiteSchemeCoefficient_finrank]
    exact finiteSubschemeDatum_finiteSchemeRank f D
  exact @cubicClosedPointSerreQuotientSection_exists_nonzero K _ inferInstance
    p hp hp0 _ Γ(D.val.subscheme, ⊤) hLField hAlg hFin i hClosed hi hExtAmbient hL

end PfaffianDescent.ProjectiveNegativeTwist
