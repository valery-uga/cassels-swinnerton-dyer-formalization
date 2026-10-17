import PfaffianDescent.AffineGammaPushforward

/- SOURCE ONLY / UNVERIFIED. Canonical actual point pullback of a module
section, through the genuine tilde and scheme pullback adjunction units. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u

/-- This is the actual composite adjunction unit, including original phi;
it is not an independently prescribed tensor point class. -/
def affineTildeActualPointClass {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (M : ModuleCat R) (m : M) :
    (moduleSpecΓFunctor (R := S)).obj
      ((Scheme.Modules.pullback (Spec.map φ)).obj ((tilde.functor R).obj M)) :=
  (((tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
        (affineGammaPushforwardNatIso φ)).unit.app M m

def affineTildeActualPointFiberEquiv {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (M : ModuleCat R) :
    letI : Algebra R S := φ.hom.toAlgebra
    (moduleSpecΓFunctor (R := S)).obj
      ((Scheme.Modules.pullback (Spec.map φ)).obj ((tilde.functor R).obj M)) ≃ₗ[S]
        S ⊗[R] M := by
  letI : Algebra R S := φ.hom.toAlgebra
  exact ((moduleSpecΓFunctor (R := S)).mapIso
      ((affineTildePullbackNatIso φ).app M)).toLinearEquiv ≪≫ₗ
    ((tilde.toTildeΓNatIso (R := S)).app ((ModuleCat.extendScalars φ.hom).obj M)).symm.toLinearEquiv

lemma affineTildeActualPointFiberEquiv_pointClass {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (M : ModuleCat R) (m : M) :
    letI : Algebra R S := φ.hom.toAlgebra
    affineTildeActualPointFiberEquiv φ M (affineTildeActualPointClass φ M m) =
      (1 : S) ⊗ₜ[R] m := by
  letI : Algebra R S := φ.hom.toAlgebra
  let adj₁ := ((tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
      (affineGammaPushforwardNatIso φ)
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))
  have h := affineTildePullbackNatIso_homEquiv φ M
  change adj₁.homEquiv M _ ((affineTildePullbackNatIso φ).hom.app M) =
    adj₂.unit.app M at h
  have hUnit : adj₁.unit.app M ≫
      (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).map
        ((affineTildePullbackNatIso φ).hom.app M) = adj₂.unit.app M := by
    calc
      _ = adj₁.homEquiv M _ ((affineTildePullbackNatIso φ).hom.app M) := rfl
      _ = adj₂.unit.app M := h
  have hm := ConcreteCategory.congr_hom hUnit m
  change (moduleSpecΓFunctor (R := S)).map (((affineTildePullbackNatIso φ).app M).hom)
      (affineTildeActualPointClass φ M m) = adj₂.unit.app M m at hm
  change ((tilde.toTildeΓNatIso (R := S)).app ((ModuleCat.extendScalars φ.hom).obj M)).inv
    ((moduleSpecΓFunctor (R := S)).map (((affineTildePullbackNatIso φ).app M).hom)
      (affineTildeActualPointClass φ M m)) = _
  rw [hm]
  change ((tilde.toTildeΓNatIso (R := S)).app ((ModuleCat.extendScalars φ.hom).obj M)).inv
    (((tilde.toTildeΓNatIso (R := S)).app ((ModuleCat.extendScalars φ.hom).obj M)).hom
      ((1 : S) ⊗ₜ[R] m)) = _
  exact ConcreteCategory.congr_hom
    (((tilde.toTildeΓNatIso (R := S)).app
      ((ModuleCat.extendScalars φ.hom).obj M)).hom_inv_id)
    ((1 : S) ⊗ₜ[R] m)

end PfaffianDescent
