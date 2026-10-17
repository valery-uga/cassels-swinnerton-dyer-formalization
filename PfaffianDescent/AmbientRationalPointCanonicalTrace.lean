import PfaffianDescent.AmbientRationalPointBasis
import PfaffianDescent.AmbientPointKoszulBasisResolution
import PfaffianDescent.PointGlobalTraceP3ResolutionTrace

/-! # The actual canonical ambient trace of every native rational point

The centered-basis resolution is constructed for the original morphism.
Its canonical augmentation map is injective in degree-three Ext and admits
a class of canonical trace one, without a resolution or nonvanishing premise.
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

/-- The original centered-point augmentation followed by the actual
canonical projective trace is an additive equivalence. -/
def ambientRationalPoint_basisCanonicalTraceEquiv
    [hExt : HasExt.{u} (Proj PS).Modules]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    Ext.{u} (C := (Proj PS).Modules)
      (ambientPointKoszul_basisPointModule M hM) (sheafOfModules PS 4) 3 ≃+ K :=
  pointGlobalTraceP3ResolutionTraceEquiv K (ambientPointKoszul_basisResolution M hM)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)

theorem ambientRationalPoint_basisCanonicalTraceEquiv_apply
    [hExt : HasExt.{u} (Proj PS).Modules]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)
    (z : Ext.{u} (C := (Proj PS).Modules)
      (ambientPointKoszul_basisPointModule M hM) (sheafOfModules PS 4) 3) :
    ambientRationalPoint_basisCanonicalTraceEquiv K M hM z =
      p3NegativeFourCohomologyThreeTraceEquiv K
        ((Ext.mk₀.{u} (C := (Proj PS).Modules)
          (ambientPointKoszul_basisAugmentation M hM)).comp z (zero_add 3)) := by
  change pointGlobalTraceP3ResolutionTraceEquiv K
    (ambientPointKoszul_basisResolution M hM)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) z = _
  rw [pointGlobalTraceP3ResolutionTraceEquiv_apply]
  rfl

theorem ambientRationalPoint_basisAugmentation_precomp_injective
    [hExt : HasExt.{u} (Proj PS).Modules]
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) :
    Function.Injective
      ((Ext.mk₀.{u} (C := (Proj PS).Modules)
        (ambientPointKoszul_basisAugmentation M hM)).precomp
          (sheafOfModules PS 4) (zero_add 3)) := by
  intro z w h
  apply (ambientRationalPoint_basisCanonicalTraceEquiv K M hM).injective
  rw [ambientRationalPoint_basisCanonicalTraceEquiv_apply,
    ambientRationalPoint_basisCanonicalTraceEquiv_apply]
  exact congrArg (p3NegativeFourCohomologyThreeTraceEquiv K) h

/-- Pullback along the original augmentation of every actual native
rational point is injective in canonical ambient degree-three Ext. -/
theorem ambientRationalPoint_augmentation_precomp_injective
    [hExt : HasExt.{u} (Proj PS).Modules]
    (i : Spec (.of K) ⟶ Proj PS)
    (hi : i ≫ AllCharacteristics.HomogeneousProjective.ambientToBase = 𝟙 _) :
    Function.Injective
      ((Ext.mk₀.{u} (C := (Proj PS).Modules)
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)).precomp
          (sheafOfModules PS 4) (zero_add 3)) := by
  obtain ⟨M, hM, hpoint⟩ := ambientRationalPoint_exists_basis K i hi
  subst i
  exact ambientRationalPoint_basisAugmentation_precomp_injective K M hM

/-- Every actual native rational point has a class of original augmentation
trace one under the actual canonical ambient trace. -/
theorem ambientRationalPoint_exists_canonical_trace_one
    [hExt : HasExt.{u} (Proj PS).Modules]
    (i : Spec (.of K) ⟶ Proj PS)
    (hi : i ≫ AllCharacteristics.HomogeneousProjective.ambientToBase = 𝟙 _) :
    ∃ z : Ext.{u} (C := (Proj PS).Modules)
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of K)).ringCatSheaf))
          (sheafOfModules PS 4) 3,
      p3NegativeFourCohomologyThreeTraceEquiv K
        ((Ext.mk₀.{u} (C := (Proj PS).Modules)
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)).comp z (zero_add 3)) = 1 := by
  obtain ⟨M, hM, hpoint⟩ := ambientRationalPoint_exists_basis K i hi
  subst i
  refine ⟨(ambientRationalPoint_basisCanonicalTraceEquiv K M hM).symm 1, ?_⟩
  change p3NegativeFourCohomologyThreeTraceEquiv K
    ((Ext.mk₀.{u} (C := (Proj PS).Modules)
      (ambientPointKoszul_basisAugmentation M hM)).comp
        ((ambientRationalPoint_basisCanonicalTraceEquiv K M hM).symm 1) (zero_add 3)) = 1
  rw [← ambientRationalPoint_basisCanonicalTraceEquiv_apply]
  exact (ambientRationalPoint_basisCanonicalTraceEquiv K M hM).apply_symm_apply 1

end PfaffianDescent.ProjectiveNegativeTwist
