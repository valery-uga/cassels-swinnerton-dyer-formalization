import PfaffianDescent.OriginalGenericPlanePointGlobalBoundaryNonzero224
import PfaffianDescent.CubicClosedDegreeElevenPointSerreExtension

/-! SOURCE ONLY227. Native Ext-existence providers instantiate the exact
original224 point factory; the SAME actual point section and quotient E
are retained. No nonzero or compatibility certificate is an input. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open IdealSheafDataModule SchemeModuleInternalHom
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

/-- All foundation dictionaries in224 are instantiated by genuine enough
injectives, giving an actual nonzero original point connecting VALUE. -/
theorem originalGenericPlanePoint_exists_boundaryValue227
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp))) :
    let X := hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
    let pF := p.map (algebraMap K (GenericHyperplaneField K))
    let hpF := hp.map (algebraMap K (GenericHyperplaneField K))
    let s := (genericPlaneCubicPairSchemeIso p hp).hom ≫
      cubicSecondEquationCurveImmersion pF (genericHyperplaneEquation (K := K)) hpF 1
        genericHyperplaneEquation_isHomogeneous
    letI := AllCharacteristics.pointAlgebra (s ≫ hypersurfaceToBase pF hpF) P.1
    let L := X.residueField P.1
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : HasExt.{u} X.Modules := schemeModules_hasExt X
    let S : ShortComplex X.Modules := incrementCokernelSequence (closedImmersionModuleToUnit i)
    ∃ (hS : S.ShortExact)
      (E : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
        (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
      (a : L),
      (Ext.mk₀.{u} (C := X.Modules)
        (closedImmersionUnitToPushforwardUnit i ≫
          fieldPointPushforwardScalarEndomorphismAddHom i a ≫ E.inv)).comp
        hS.extClass (zero_add 1) ≠ 0 := by
  classical
  dsimp only
  let X := hypersurface (genericPlaneCubic p) (genericPlaneCubic_isHomogeneous p hp)
  letI : HasExt.{u} X.Modules := schemeModules_hasExt X
  obtain ⟨j, hx, hData⟩ := originalGenericPlanePoint_exists_globalBoundaryNonzero224 p hp hp0 P
    (schemeModules_hasExt X) (schemeModules_hasExt _)
    (moduleCatStalk_hasExt (X.presheaf.stalk P.1))
  dsimp only [originalCurvePointBoundaryNonzeroData224] at hData
  obtain ⟨hS, E, a, ha, _⟩ := hData
    (moduleCatStalk_hasExt _) (moduleCatStalk_hasExt _)
    (schemeModules_hasExt _) (moduleCatStalk_hasExt _)
    (schemeModules_hasExt _) (schemeModules_hasExt _)
    (moduleCatStalk_hasExt _) (moduleCatStalk_hasExt _)
  exact ⟨hS, E, a, ha⟩

end PfaffianDescent.Coray
