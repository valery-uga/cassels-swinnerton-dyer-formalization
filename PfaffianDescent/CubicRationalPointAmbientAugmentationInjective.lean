import PfaffianDescent.CubicRationalPointAmbientAugmentationComparison
import PfaffianDescent.AmbientRationalPointCanonicalTrace
import PfaffianDescent.CubicPointCartierNonzeroReduction

/-! # Actual ambient augmentation injectivity for a rational cubic-surface point

The original Cartier augmentation is compared with the literal composite
point restriction using canonical unit and pushforward isomorphisms. Its
degree-three Ext pullback is therefore injective for every actual rational
point of the cubic surface, without a supplied square or injectivity premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- The actual augmentation entering the native Cartier criterion is
injective in canonical ambient degree-three Ext for every rational point. -/
theorem cubicRationalPointAmbientAugmentation_precomp_injective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (i : Spec (.of K) ⟶ Proj (grading (equationIdeal p hp))) [IsClosedImmersion i]
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    (hi : i ≫ hypersurfaceToBase p hp = 𝟙 (Spec (.of K))) :
    Function.Injective
      ((Ext.mk₀.{u} (C := (Proj PS).Modules)
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
          (hypersurfaceToAmbient p hp) ≫
          (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).map
            (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
              (closedImmersionIdealTwistSequenceUnitTargetIso i).inv))).precomp
        (sheafOfModules PS 4) (zero_add 3)) := by
  have hamb : hypersurfaceToAmbient p hp ≫ ambientToBase = hypersurfaceToBase p hp :=
    quotientProjMap_toBase (equationIdeal p hp)
  have hbase : (i ≫ hypersurfaceToAmbient p hp) ≫ ambientToBase = 𝟙 (Spec (.of K)) := by
    rw [Category.assoc, hamb]
    exact hi
  exact cubicRationalPointAmbientAugmentation_precomp_injective_of_targetIso.{u + 1, u, u}
    (C := (Proj PS).Modules) (Y := sheafOfModules PS 4)
    (cubicRationalPointAmbientAugmentation_map i (hypersurfaceToAmbient p hp))
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (i ≫ hypersurfaceToAmbient p hp))
    (cubicRationalPointAmbientAugmentation_targetIso i (hypersurfaceToAmbient p hp))
    (cubicRationalPointAmbientAugmentation_map_comp_targetIso i (hypersurfaceToAmbient p hp)) 3
    (ambientRationalPoint_augmentation_precomp_injective K (i ≫ hypersurfaceToAmbient p hp) hbase)

end PfaffianDescent.ProjectiveNegativeTwist
