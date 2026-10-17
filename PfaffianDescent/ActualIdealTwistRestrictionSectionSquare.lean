import PfaffianDescent.ActualIdealTwistRestrictionInclusion
import PfaffianDescent.ActualClosedImmersionFactorIdealTwistGlobalSections

/- SOURCE ONLY / UNVERIFIED. Actual global section square, BEFORE any
coordinate dictionary or residue-field identification. No comparison premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open BundleSectionZeroLocus IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] isIso_pullbackUnitComparison

lemma actualIdealTwistGlobalRestriction_nativeInclusion
    {K : Type u} [Field K] {Y X Z : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) (i : X ⟶ Y) (q : Z ⟶ X)
    [IsClosedImmersion q] [IsClosedImmersion (q ≫ i)]
    (T : Y.Modules) (N : X.Modules) (e : (Scheme.Modules.pullback i).obj T ≅ N)
    (s : SchemeModuleGlobalSectionsOver g
      (schemeModuleTensor (closedImmersionModule (q ≫ i)) T)) :
    actualClosedImmersionFactorIdealTwistGlobalSectionsRestriction g i q T s ≫
        schemeModuleTensorMap (𝟙 (closedImmersionModule q)) e.hom ≫
        actualIdealTwistInclusion q N =
      inv (pullbackUnitComparison i) ≫ (Scheme.Modules.pullback i).map
        (s ≫ actualIdealTwistInclusion (q ≫ i) T) ≫ e.hom := by
  change (inv (pullbackUnitComparison i) ≫ (Scheme.Modules.pullback i).map s ≫
      actualClosedImmersionFactorIdealTwistRestriction i q T) ≫ _ ≫ _ = _
  simp only [Category.assoc]
  rw [actualIdealTwistRestriction_nativeInclusion]
  rw [Functor.map_comp]
  simp only [Category.assoc]

end PfaffianDescent
