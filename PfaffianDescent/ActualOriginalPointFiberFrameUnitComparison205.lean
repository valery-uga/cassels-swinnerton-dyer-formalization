import PfaffianDescent.ActualFieldUnitAutomorphismScalar
import PfaffianDescent.SchemeModuleInternalHomSupportedFiberIso

/-! SOURCE ONLY205. Actual point-fiber frames compare by the derived scalar
of their actual unit automorphism. Whole global quotient maps and canonical
projections retain the same intrinsic fiber and original adjunction unit. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SchemeModuleInternalHom IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The coefficient comes from the ACTUAL point-unit automorphism. -/
def actualPointFiberFrameComparisonScalar205
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) (T : X.Modules)
    (b₀ b₁ : (Scheme.Modules.pullback i).obj T ≅
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) : L :=
  actualFieldUnitAutomorphismScalar (b₀.inv ≫ b₁.hom)

theorem actualPointFiberFrameComparisonScalar_isUnit205
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) (T : X.Modules)
    (b₀ b₁ : (Scheme.Modules.pullback i).obj T ≅
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) :
    IsUnit (actualPointFiberFrameComparisonScalar205 i T b₀ b₁) := by
  apply isUnit_iff_ne_zero.mpr
  exact actualFieldUnitAutomorphismScalar_ne_zero (b₀.inv ≫ b₁.hom)

/-- Literal equality between actual fiber maps; the coefficient is derived,
not supplied by a frame-comparison hypothesis. -/
theorem actualPointFiberFrameComparison_square205
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) (T : X.Modules)
    (b₀ b₁ : (Scheme.Modules.pullback i).obj T ≅
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) :
    b₁.hom = b₀.hom ≫ schemeModuleConstantEndomorphism (𝟙 (Spec (.of L)))
      (actualPointFiberFrameComparisonScalar205 i T b₀ b₁) := by
  calc
    b₁.hom = b₀.hom ≫ (b₀.inv ≫ b₁.hom) := by
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = _ := congrArg (fun f => b₀.hom ≫ f)
      (actualFieldUnitAutomorphism_eq_constant (b₀.inv ≫ b₁.hom))

/-- The SAME original adjunction unit, after actual pushforward, has the
same derived comparison. This is an equality of actual scheme-module maps. -/
theorem actualPointFiberFrameComparison_adjunctionUnit205
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) (T : X.Modules)
    (b₀ b₁ : (Scheme.Modules.pullback i).obj T ≅
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) :
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T ≫
        (Scheme.Modules.pushforward i).map b₁.hom =
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app T ≫
        (Scheme.Modules.pushforward i).map b₀.hom) ≫
          (Scheme.Modules.pushforward i).map
            (schemeModuleConstantEndomorphism (𝟙 (Spec (.of L)))
              (actualPointFiberFrameComparisonScalar205 i T b₀ b₁)) := by
  rw [actualPointFiberFrameComparison_square205 i T b₀ b₁,
    Functor.map_comp, Category.assoc]

/-- Actual WHOLE canonical point-dual quotient, in the original ideal chart
and ANY second genuine fiber frame. All canonical projection equations are
derived from the supported-fiber provider; no comparison/trace premise occurs. -/
theorem actualClosedPointChartWholeFiberComparison205
    {L : Type u} [Field L] {X : Scheme.{u}}
    (U : X.Opens) (j : Spec (.of L) ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (closedImmersionModule (j ≫ U.ι)).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (e : (closedImmersionModule (j ≫ U.ι)).over U ≅
      (SheafOfModules.unit X.ringCatSheaf).over U)
    (b₁ : (Scheme.Modules.pullback (j ≫ U.ι)).obj
        (dual (closedImmersionModule (j ≫ U.ι))) ≅
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) :
    let i := j ≫ U.ι
    let D := dual (closedImmersionModule i)
    let b₀ := schemeModuleFiberFrameIso U.ι j D (dualRestrictUnitIso U e)
    let c := closedImmersionDualIncrement_canonicalFiberIso U j B hB eB e
    let E₀ := c ≪≫ (Scheme.Modules.pushforward i).mapIso b₀
    let E₁ := c ≪≫ (Scheme.Modules.pushforward i).mapIso b₁
    let α := actualPointFiberFrameComparisonScalar205 i D b₀ b₁
    IsUnit α ∧
      E₁.hom = E₀.hom ≫ (Scheme.Modules.pushforward i).map
        (schemeModuleConstantEndomorphism (𝟙 (Spec (.of L))) α) ∧
      cokernel.π (unitToHom (closedImmersionModuleToUnit i)) ≫ E₀.hom =
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D ≫
          (Scheme.Modules.pushforward i).map b₀.hom ∧
      cokernel.π (unitToHom (closedImmersionModuleToUnit i)) ≫ E₁.hom =
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D ≫
          (Scheme.Modules.pushforward i).map b₁.hom := by
  dsimp only
  let i := j ≫ U.ι
  let D := dual (closedImmersionModule i)
  let b₀ := schemeModuleFiberFrameIso U.ι j D (dualRestrictUnitIso U e)
  let c := closedImmersionDualIncrement_canonicalFiberIso U j B hB eB e
  refine ⟨actualPointFiberFrameComparisonScalar_isUnit205 i D b₀ b₁, ?_, ?_, ?_⟩
  · change c.hom ≫ (Scheme.Modules.pushforward i).map b₁.hom = _
    rw [actualPointFiberFrameComparison_square205 i D b₀ b₁, Functor.map_comp]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    rfl
  · change cokernel.π (unitToHom (closedImmersionModuleToUnit i)) ≫
      (c.hom ≫ (Scheme.Modules.pushforward i).map b₀.hom) = _
    rw [← Category.assoc, closedImmersionDualIncrement_canonicalFiberIso_projection]
  · change cokernel.π (unitToHom (closedImmersionModuleToUnit i)) ≫
      (c.hom ≫ (Scheme.Modules.pushforward i).map b₁.hom) = _
    rw [← Category.assoc, closedImmersionDualIncrement_canonicalFiberIso_projection]

end PfaffianDescent
