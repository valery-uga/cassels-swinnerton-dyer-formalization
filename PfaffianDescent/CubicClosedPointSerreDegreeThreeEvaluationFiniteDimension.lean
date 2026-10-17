import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationDimension
import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationSchemeIso
import PfaffianDescent.FiniteSchemeAlgebra
import AllCharacteristics.FiniteSubschemeFunctor

/-! # The actual rank-three finite field datum has six restriction values -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual pullback to the finite datum itself has dimension six.
The canonical spectrum presentation and all its comparison maps are
constructed, and the datum's coefficient algebra supplies the field action. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationFiniteDimension_finrank_eq_six
    {K : Type u} [Field K] {X : Scheme.{u}} {M : X.Modules}
    (base : X ⟶ Spec (.of K)) (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (D : FiniteSubschemeDatum base 3) (hField : IsField Γ(D.val.subscheme, ⊤)) :
    Module.finrank K (SchemeModuleGlobalSectionsOver (D.val.subschemeι ≫ base)
      ((Scheme.Modules.pullback D.val.subschemeι).obj (show X.Modules from e.E))) = 6 := by
  let Z := D.val.subscheme
  let g := D.val.subschemeι ≫ base
  letI : IsFinite g := D.property.1
  letI : IsAffine Z := isAffine_of_isAffineHom g
  letI : Field Γ(Z, ⊤) := hField.toField
  letI : Algebra K Γ(Z, ⊤) := finiteSchemeCoefficientAlgebra g
  let j : Spec (.of Γ(Z, ⊤)) ⟶ X := Z.isoSpec.inv ≫ D.val.subschemeι
  have hj : j ≫ base = Spec.map (CommRingCat.ofHom (algebraMap K Γ(Z, ⊤))) := by
    simpa only [j, g, Category.assoc] using (finiteSchemeCoefficient_spec g).symm
  have hL : Module.finrank K Γ(Z, ⊤) = 3 := by
    rw [finiteSchemeCoefficient_finrank]
    exact finiteSubschemeDatum_finiteSchemeRank base D
  let E : X.Modules := e.E
  let q₁ := cubicClosedPointSerreDegreeThreeEvaluationSchemeIsoLinearEquiv g Z.isoSpec.symm
    ((Scheme.Modules.pullback D.val.subschemeι).obj E)
  let a := (Scheme.Modules.pullbackComp Z.isoSpec.inv D.val.subschemeι).app E
  let q₂ := cubicClosedPointSerreDegreeThreeEvaluationModuleIsoLinearEquiv
    (Z.isoSpec.inv ≫ g) a
  have hdim := cubicClosedPointSerreDegreeThreeEvaluationDimension_finrank_eq_six base e C j hj hL
  calc
    _ = Module.finrank K (SchemeModuleGlobalSectionsOver (Z.isoSpec.inv ≫ g)
        ((Scheme.Modules.pullback Z.isoSpec.inv).obj
          ((Scheme.Modules.pullback D.val.subschemeι).obj E))) := q₁.finrank_eq
    _ = Module.finrank K (SchemeModuleGlobalSectionsOver (Z.isoSpec.inv ≫ g)
        ((Scheme.Modules.pullback j).obj E)) := q₂.finrank_eq
    _ = 6 := by
      have hb : Z.isoSpec.inv ≫ g = j ≫ base := by
        dsimp only [g, j]
        exact (Category.assoc _ _ _).symm
      rw [hb]
      exact hdim

end PfaffianDescent
