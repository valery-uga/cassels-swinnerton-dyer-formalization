import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationFiniteDimension

/-! # Actual finite-datum restriction of a pulled-back original rank-two extension -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Pulling back the original bundle along any actual scheme morphism and
then restricting to an actual rank-three finite field datum gives precisely
six ground-field dimensions. The fiber coordinate is constructed from the
original actual rank-two cover. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationPullbackFiniteDimension_finrank_eq_six
    {F : Type u} [Field F] {X Y : Scheme.{u}} {M : X.Modules}
    (e : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (f : Y ⟶ X) (base : Y ⟶ Spec (.of F))
    (D : FiniteSubschemeDatum base 3) (hField : IsField Γ(D.val.subscheme, ⊤)) :
    Module.finrank F (SchemeModuleGlobalSectionsOver (D.val.subschemeι ≫ base)
      ((Scheme.Modules.pullback D.val.subschemeι).obj
        ((Scheme.Modules.pullback f).obj (show X.Modules from e.E)))) = 6 := by
  let Z := D.val.subscheme
  let g := D.val.subschemeι ≫ base
  letI : IsFinite g := D.property.1
  letI : IsAffine Z := isAffine_of_isAffineHom g
  letI : Field Γ(Z, ⊤) := hField.toField
  letI : Algebra F Γ(Z, ⊤) := finiteSchemeCoefficientAlgebra g
  have hL : Module.finrank F Γ(Z, ⊤) = 3 := by
    rw [finiteSchemeCoefficient_finrank]
    exact finiteSubschemeDatum_finiteSchemeRank base D
  letI : FiniteDimensional F Γ(Z, ⊤) := Module.finite_of_finrank_pos (by rw [hL]; omega)
  let E : X.Modules := e.E
  let N := (Scheme.Modules.pullback D.val.subschemeι).obj ((Scheme.Modules.pullback f).obj E)
  let j := Z.isoSpec.inv ≫ D.val.subschemeι
  obtain ⟨t⟩ := cubicClosedPointSerreDegreeThreeEvaluationFiber_exists_freeIso e C (j ≫ f)
  let a := (Scheme.Modules.pullbackComp j f).app E
  let b := (Scheme.Modules.pullbackComp Z.isoSpec.inv D.val.subschemeι).app
    ((Scheme.Modules.pullback f).obj E)
  let t' := t ≪≫ a.symm ≪≫ b.symm
  let q₁ := cubicClosedPointSerreDegreeThreeEvaluationSchemeIsoLinearEquiv g Z.isoSpec.symm N
  have hs : Z.isoSpec.inv ≫ g = Spec.map (CommRingCat.ofHom (algebraMap F Γ(Z, ⊤))) :=
    (finiteSchemeCoefficient_spec g).symm
  have hspec : Module.finrank F (SchemeModuleGlobalSectionsOver (Z.isoSpec.inv ≫ g)
      ((Scheme.Modules.pullback Z.isoSpec.inv).obj N)) = 6 := by
    rw [hs]
    let pL : Spec (.of Γ(Z, ⊤)) ⟶ Spec (.of F) :=
      Spec.map (CommRingCat.ofHom (algebraMap F Γ(Z, ⊤)))
    let P := (Scheme.Modules.pullback Z.isoSpec.inv).obj N
    letI := Module.compHom Γ(Spec (.of Γ(Z, ⊤)), ⊤) (schemeOpenBaseRingHom pL ⊤)
    let q := schemeModuleGlobalSectionsLinearEquivOpenTop pL P ≪≫ₗ
      moduleOpenTopLinearEquivOfFreeIsoOver pL (ULift.{u} (Fin 2)) P t' ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ => specGlobalFunctionsLinearEquiv F Γ(Z, ⊤))
    rw [q.finrank_eq, Module.finrank_pi_fintype]
    simp [hL]
  exact q₁.finrank_eq.trans hspec

end PfaffianDescent
