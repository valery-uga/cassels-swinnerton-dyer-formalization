import PfaffianDescent.NativeNormalizedPullbackSectionMap
import PfaffianDescent.TwistedCubicNativeGlobalCoordinateImages
import PfaffianDescent.ActualPositiveGradedHomogeneousSectionPullback

/-! SOURCE ONLY. Original ambient adjunct normalization and SAME actual
standard ambient bundle Iso image on all four literal coordinates. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist BundleSectionZeroLocus
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] isIso_pullbackUnitComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "I" => standardTwistedCubicHomogeneousIdeal (K := K)
local notation "L" => (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Genuine pullback of the original ambient coordinate along the actual
parametrization, normalized by the canonical unit comparison. -/
def actualLineAmbientPulledCoordinateHom (f : scheme L ⟶ Proj PS) (k : Fin 4) :
    SheafOfModules.unit (scheme L).ringCatSheaf ⟶
      (Scheme.Modules.pullback f).obj (positiveSheafOfModules PS 1) :=
  CategoryTheory.inv («I» := isIso_pullbackUnitComparison f)
    (pullbackUnitComparison f) ≫ (Scheme.Modules.pullback f).map
      ((positiveSheafOfModules PS 1).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous PS 1 ⟨X k, isHomogeneous_X K k⟩))

/-- The actual quotient adjunct sends EACH original ambient coordinate to
the SAME original curve coordinate-section map, internally and exactly. -/
theorem standardTwistedCubicActualAmbientAdjunct_coordinate (k : Fin 4) :
    CategoryTheory.inv («I» := isIso_pullbackUnitComparison (quotientProjMap I))
        (pullbackUnitComparison (quotientProjMap I)) ≫
      (Scheme.Modules.pullback (quotientProjMap I)).map
        ((positiveSheafOfModules PS 1).unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous PS 1 ⟨X k, isHomogeneous_X K k⟩)) ≫
      (actualAmbientPositiveTwistQuotientIso I 1).hom =
    standardTwistedCubicPositiveOneCoordinateHom (K := K) k :=
  actualAmbientPositiveTwistQuotientIso_homogeneousSection I 1 ⟨X k, isHomogeneous_X K k⟩

/-- The SAME composite normalized pullback and actual composite Iso send
an actual ambient section to its iterated pullback. Scheme/module arguments
remain abstract during all Iso-hom and pullback-composition conversion. -/
private theorem nativeActualComposedIso_sectionImageCut
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (Q : Z.Modules) (Q' : Y.Modules) (N : X.Modules)
    (e : (Scheme.Modules.pullback g).obj Q ≅ Q')
    (a : (Scheme.Modules.pullback f).obj Q' ≅ N)
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ Q)
    (t : SheafOfModules.unit Y.ringCatSheaf ⟶ Q')
    (h : CategoryTheory.inv («I» := isIso_pullbackUnitComparison g)
        (pullbackUnitComparison g) ≫ (Scheme.Modules.pullback g).map s ≫ e.hom = t) :
    CategoryTheory.inv («I» := isIso_pullbackUnitComparison (f ≫ g))
        (pullbackUnitComparison (f ≫ g)) ≫ (Scheme.Modules.pullback (f ≫ g)).map s ≫
      ((Scheme.Modules.pullbackComp f g).symm.app Q ≪≫
        (Scheme.Modules.pullback f).mapIso e ≪≫ a).hom =
    CategoryTheory.inv («I» := isIso_pullbackUnitComparison f)
        (pullbackUnitComparison f) ≫ (Scheme.Modules.pullback f).map t ≫ a.hom := by
  have hc := nativeNormalizedPullbackSectionMap_comp_coefficient f g Q Q' s e.hom
  change CategoryTheory.inv («I» := isIso_pullbackUnitComparison (f ≫ g))
      (pullbackUnitComparison (f ≫ g)) ≫ (Scheme.Modules.pullback (f ≫ g)).map s ≫
      (Scheme.Modules.pullbackComp f g).inv.app Q ≫
      (Scheme.Modules.pullback f).map e.hom ≫ a.hom = _
  have hc' : CategoryTheory.inv («I» := isIso_pullbackUnitComparison (f ≫ g))
      (pullbackUnitComparison (f ≫ g)) ≫ (Scheme.Modules.pullback (f ≫ g)).map s ≫
      (Scheme.Modules.pullbackComp f g).inv.app Q ≫
      (Scheme.Modules.pullback f).map e.hom ≫ a.hom =
      CategoryTheory.inv («I» := isIso_pullbackUnitComparison f) (pullbackUnitComparison f) ≫
        (Scheme.Modules.pullback f).map
          (CategoryTheory.inv («I» := isIso_pullbackUnitComparison g) (pullbackUnitComparison g) ≫
            (Scheme.Modules.pullback g).map s ≫ e.hom) ≫ a.hom := by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ a.hom) hc
  exact hc'.trans
    (congrArg (fun z =>
      CategoryTheory.inv («I» := isIso_pullbackUnitComparison f) (pullbackUnitComparison f) ≫
        (Scheme.Modules.pullback f).map z ≫ a.hom) h)

/-- ALL FOUR genuine ambient coordinate maps become their literal native
cubic-section maps under the SAME original ambient O1→O3 comparison Iso. -/
theorem standardTwistedCubicNativeAmbientPositiveOnePullbackIso_coordinate (k : Fin 4) :
    actualLineAmbientPulledCoordinateHom
        (standardProjectiveLineToTwistedCubic (K := K) ≫ quotientProjMap I) k ≫
      (standardTwistedCubicNativeAmbientPositiveOnePullbackIso (K := K)).hom =
    standardTwistedCubicLiteralLineSectionHom (K := K) k := by
  exact (nativeActualComposedIso_sectionImageCut
    (standardProjectiveLineToTwistedCubic (K := K)) (quotientProjMap I)
    (positiveSheafOfModules PS 1) (positiveSheafOfModules (grading I) 1)
    (positiveSheafOfModules (grading L) 3)
    (actualAmbientPositiveTwistQuotientIso I 1)
    (standardTwistedCubicNativePositiveOnePullbackIso (K := K))
    ((positiveSheafOfModules PS 1).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous PS 1 ⟨X k, isHomogeneous_X K k⟩))
    (standardTwistedCubicPositiveOneCoordinateHom (K := K) k)
    (standardTwistedCubicActualAmbientAdjunct_coordinate (K := K) k)).trans
      (standardTwistedCubicNativePositiveOnePullbackIso_coordinate (K := K) k)

end PfaffianDescent.QuarticNet
