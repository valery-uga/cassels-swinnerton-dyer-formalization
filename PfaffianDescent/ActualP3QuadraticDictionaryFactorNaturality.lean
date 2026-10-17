import PfaffianDescent.ActualAmbientClosedIdealFactorInclusion
import PfaffianDescent.ActualP3QuadraticRestrictionChartComparison

/-! SOURCE ONLY / UNVERIFIED. Naturality is proved through the actual
augmentation of the tensor ideal into O(2), not supplied as a square. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory IdealSheafDataModule MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Tracing all three equivalences of the dictionary: its polynomial maps
to precisely the augmented genuine ideal-sheaf section. -/
lemma p3ActualIdealQuadraticIntrinsicLinearEquiv_augmentation
    {K : Type u} [Field K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion i]
    (s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2))) :
    p3HomogeneousGlobalSectionsLinearEquiv K 2 (by decide)
      ⟨(p3ActualIdealQuadraticIntrinsicLinearEquiv i s).val,
        (p3ActualIdealQuadraticIntrinsicLinearEquiv i s).property.1⟩ =
      schemeModuleGlobalSectionsMap (ambientToBase (R := K) (σ := Fin 4))
        (actualAmbientClosedIdealTwistAugmentation i
          (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2)) s := by
  let E := p3HomogeneousGlobalSectionsLinearEquiv K 2 (by decide)
  let T := positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2
  let S := closedImmersionIdealTwistSequence i T
  let a := schemeModuleGlobalSectionsMap (ambientToBase (R := K) (σ := Fin 4))
    (S.f ≫ (schemeModuleTensorUnitLeftIso T).hom)
  change E (E.symm (a s)) = a s
  exact E.apply_symm_apply (a s)

/-- The genuine sheaf-induced H0 inclusion preserves the same polynomial
under the internally proved P3 dictionary. -/
lemma p3ActualIdealQuadraticIntrinsicLinearEquiv_factor_naturality
    {K : Type u} [Field K] {Z P : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (r : P ⟶ Z) (q : P ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (hfac : r ≫ i = q) [IsClosedImmersion i] [IsClosedImmersion q]
    (s : SchemeModuleGlobalSectionsOver (ambientToBase (R := K) (σ := Fin 4))
      (closedImmersionIdealTwist i
        (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2))) :
    (p3ActualIdealQuadraticIntrinsicLinearEquiv q
      (actualAmbientClosedIdealTwistHZeroFactorInclusion
        (ambientToBase (R := K) (σ := Fin 4)) i r q hfac
        (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2) s)).val =
      (p3ActualIdealQuadraticIntrinsicLinearEquiv i s).val := by
  let T := positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2
  let v := actualAmbientClosedIdealTwistHZeroFactorInclusion
    (ambientToBase (R := K) (σ := Fin 4)) i r q hfac T s
  have h : (⟨(p3ActualIdealQuadraticIntrinsicLinearEquiv q v).val,
      (p3ActualIdealQuadraticIntrinsicLinearEquiv q v).property.1⟩ :
      homogeneousSubmodule (Fin 4) K 2) =
      ⟨(p3ActualIdealQuadraticIntrinsicLinearEquiv i s).val,
        (p3ActualIdealQuadraticIntrinsicLinearEquiv i s).property.1⟩ := by
    apply (p3HomogeneousGlobalSectionsLinearEquiv K 2 (by decide)).injective
    rw [p3ActualIdealQuadraticIntrinsicLinearEquiv_augmentation,
      p3ActualIdealQuadraticIntrinsicLinearEquiv_augmentation]
    change (s ≫ actualAmbientClosedIdealTwistFactorInclusion i r q hfac T) ≫
      actualAmbientClosedIdealTwistAugmentation q T =
      s ≫ actualAmbientClosedIdealTwistAugmentation i T
    exact (Category.assoc s _ _).trans
      (congrArg (fun f => s ≫ f)
        (actualAmbientClosedIdealTwistFactorInclusion_augmentation i r q hfac T))
  exact congrArg (fun a : homogeneousSubmodule (Fin 4) K 2 => a.val) h

end PfaffianDescent
