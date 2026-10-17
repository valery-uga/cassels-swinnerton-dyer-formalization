import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationSchemeIso
import PfaffianDescent.CubicClosedPointSerreDegreeThreeEvaluationFiber
import PfaffianDescent.FiniteSchemeAlgebra

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def pointSplittingGlobalSectionsOverBaseCongr
    {F : Type u} [Field F] {D : Scheme.{u}}
    (p q : D ⟶ Spec (.of F)) (h : p = q) (N : D.Modules) :
    SchemeModuleGlobalSectionsOver p N ≃ₗ[F] SchemeModuleGlobalSectionsOver q N := by
  subst q
  exact LinearEquiv.refl F _

/-- The actual finite-scheme Gamma space is identified with its canonical
Spec Gamma presentation by the literal geometric pullback. -/
def pointSplittingFiniteSpecSectionsEquiv
    {F : Type u} [Field F] {X D : Scheme.{u}}
    (base : X ⟶ Spec (.of F)) (d : D ⟶ X) [IsFinite (d ≫ base)] [IsAffine D]
    (M : X.Modules) :
    letI := finiteSchemeCoefficientAlgebra (d ≫ base)
    SchemeModuleGlobalSectionsOver (d ≫ base) ((Scheme.Modules.pullback d).obj M) ≃ₗ[F]
    SchemeModuleGlobalSectionsOver
      (Spec.map (CommRingCat.ofHom (algebraMap F Γ(D, ⊤))))
      ((Scheme.Modules.pullback D.isoSpec.inv).obj ((Scheme.Modules.pullback d).obj M)) := by
  letI := finiteSchemeCoefficientAlgebra (d ≫ base)
  let q := d ≫ base
  let N := (Scheme.Modules.pullback d).obj M
  exact cubicClosedPointSerreDegreeThreeEvaluationSchemeIsoLinearEquiv q D.isoSpec.symm N ≪≫ₗ
    pointSplittingGlobalSectionsOverBaseCongr (D.isoSpec.inv ≫ q)
      (Spec.map (CommRingCat.ofHom (algebraMap F Γ(D, ⊤))))
      (finiteSchemeCoefficient_spec q).symm ((Scheme.Modules.pullback D.isoSpec.inv).obj N)

/-- The actual Serre rank-two cover provides a free presentation on the
canonical coefficient spectrum of the actual finite field subscheme. -/
theorem pointSplittingFiniteSerreSpec_exists_freeIso
    {X D : Scheme.{u}} [IsAffine D] {M : X.Modules}
    (s : SerreExtensionData X M)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover s) (d : D ⟶ X)
    (hField : IsField Γ(D, ⊤)) :
    Nonempty (SheafOfModules.free (R := (Spec (.of Γ(D, ⊤))).ringCatSheaf)
      (ULift.{u} (Fin 2)) ≅
      (Scheme.Modules.pullback D.isoSpec.inv).obj
        ((Scheme.Modules.pullback d).obj (show X.Modules from s.E))) := by
  letI : Field Γ(D, ⊤) := hField.toField
  obtain ⟨t⟩ := cubicClosedPointSerreDegreeThreeEvaluationFiber_exists_freeIso s C
    (D.isoSpec.inv ≫ d)
  exact ⟨t ≪≫ ((Scheme.Modules.pullbackComp D.isoSpec.inv d).app
    (show X.Modules from s.E)).symm⟩

end PfaffianDescent
