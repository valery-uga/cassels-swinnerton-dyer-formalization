import PfaffianDescent.ActualOriginalPointDualCoefficientFrameUnit205
import PfaffianDescent.ActualOriginalPointFiberFrameUnitComparison205
import PfaffianDescent.ActualOriginalResiduePointFiberStalkCoordinate207
import PfaffianDescent.ActualPointParameterResidueCoefficient194

/-! SOURCE ONLY209. Actual global quotient frame uniqueness and the total
unit comparison of the SAME whole native quotient coefficient. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open SchemeModuleInternalHom IdealSheafDataModule IsLocalRing
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual epi projection cancels. Actual whole quotient identifications
in two genuine fiber frames differ by their DERIVED point-unit scalar. -/
theorem actualWholePointQuotient_frameComparison209
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) (D Q : X.Modules) (π : D ⟶ Q) [Epi π]
    (b₀ b₁ : (Scheme.Modules.pullback i).obj D ≅
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (E₀ E₁ : Q ≅ (Scheme.Modules.pushforward i).obj
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (h₀ : π ≫ E₀.hom = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D ≫
      (Scheme.Modules.pushforward i).map b₀.hom)
    (h₁ : π ≫ E₁.hom = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D ≫
      (Scheme.Modules.pushforward i).map b₁.hom) :
    IsUnit (actualPointFiberFrameComparisonScalar205 i D b₀ b₁) ∧
      E₁.hom = E₀.hom ≫ (Scheme.Modules.pushforward i).map
        (schemeModuleConstantEndomorphism (𝟙 (Spec (.of L)))
          (actualPointFiberFrameComparisonScalar205 i D b₀ b₁)) := by
  refine ⟨actualPointFiberFrameComparisonScalar_isUnit205 i D b₀ b₁, ?_⟩
  apply (cancel_epi π).mp
  rw [← Category.assoc, h₀, h₁]
  exact actualPointFiberFrameComparison_adjunctionUnit205 i D b₀ b₁

/-- On EVERY whole native quotient element, the principal residue coefficient
is rho/alpha times the actual global point-fiber coordinate. rho is the actual
original local frame unit's residue; alpha is derived from actual fiber frames.
Projection laws here are ordinary generic construction data; the original
caller constructs both of them internally from194/200/203. -/
theorem actualWholePointQuotient_totalResidueUnit209
    {L : Type u} [Field L] {X : Scheme.{u}}
    (U : X.Opens) (j : Spec (.of L) ⟶ (U : Scheme))
    [IsClosedImmersion (j ≫ U.ι)] (y : Spec (.of L)) (M : X.Modules)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U)
    (χ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (hS : (incrementCokernelSequence χ).ShortExact)
    (e₀ : X.presheaf.stalk (U.ι (j y)) ≃ₗ[X.presheaf.stalk (U.ι (j y))]
      ((schemeModuleStalkModuleFunctor X (U.ι (j y))).obj M))
    (t : X.presheaf.stalk (U.ι (j y)))
    (he₀ : ∀ r, schemeModuleStalkToRingLinearMap χ (U.ι (j y)) (e₀ r) = r * t)
    (hspan : maximalIdeal (X.presheaf.stalk (U.ι (j y))) =
      Ideal.span ({t} : Set (X.presheaf.stalk (U.ι (j y)))))
    (q : ((incrementCokernelSequence χ).map
        (schemeModuleStalkModuleFunctor X (U.ι (j y)))).X₃ ≅
      (pointCartierYonedaCoefficientComplex t).X₃)
    (hq : ((incrementCokernelSequence χ).map
        (schemeModuleStalkModuleFunctor X (U.ι (j y)))).g ≫ q.hom =
      (actualDualIncrementStalkCoefficientIso194 U (j y) M e e₀).hom ≫
        (pointCartierYonedaCoefficientComplex t).g)
    (b₁ : (Scheme.Modules.pullback (j ≫ U.ι)).obj (dual M) ≅
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (E₁ : (incrementCokernelSequence χ).X₃ ≅ (Scheme.Modules.pushforward (j ≫ U.ι)).obj
      (show (Spec (.of L)).Modules from SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (hE₁ : (incrementCokernelSequence χ).g ≫ E₁.hom =
      (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ U.ι)).unit.app (dual M) ≫
        (Scheme.Modules.pushforward (j ≫ U.ι)).map b₁.hom) :
    let i := j ≫ U.ι
    let F := schemeModuleStalkModuleFunctor X (U.ι (j y))
    let b₀ := schemeModuleFiberFrameIso U.ι j (dual M) (dualRestrictUnitIso U e)
    let α := actualPointFiberFrameComparisonScalar205 i (dual M) b₀ b₁
    let ρ := closedFieldPointResidueRingEquivAt i y
      (residue (X.presheaf.stalk (U.ι (j y)))
        (actualOriginalIdealFrameUnit205 U (j y) M e e₀))
    IsUnit (ρ / α) ∧
      ∀ z : ((incrementCokernelSequence χ).map F).X₃,
        closedFieldPointResidueRingEquivAt i y
            (actualPointParameterResidueLinearEquiv194 t hspan (q.hom z)) =
          (ρ / α) * actualFieldPointPushforwardUnitStalkCoordinate207 i y
            ((F.map E₁.hom) z) := by
  dsimp only
  let i := j ≫ U.ι
  let F := schemeModuleStalkModuleFunctor X (U.ι (j y))
  let S := incrementCokernelSequence χ
  let b₀ := schemeModuleFiberFrameIso U.ι j (dual M) (dualRestrictUnitIso U e)
  let α := actualPointFiberFrameComparisonScalar205 i (dual M) b₀ b₁
  let κ := closedFieldPointResidueRingEquivAt i y
  let ρ := κ (residue (X.presheaf.stalk (U.ι (j y)))
    (actualOriginalIdealFrameUnit205 U (j y) M e e₀))
  have hα : IsUnit α := actualPointFiberFrameComparisonScalar_isUnit205 i (dual M) b₀ b₁
  have hρ : IsUnit ρ :=
    (actualOriginalIdealFrameResidue_isUnit205 U (j y) M e e₀).map κ.toRingHom
  refine ⟨isUnit_iff_ne_zero.mpr (div_ne_zero hρ.ne_zero hα.ne_zero), ?_⟩
  intro z
  have hNative := hS.map_of_exact F
  letI : Epi (S.map F).g := hNative.epi_g
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (S.map F).g).mp inferInstance z
  have hπ : S.g ≫ E₁.hom = actualPointChartFiberUnitMap207 U j (dual M)
      (dualRestrictUnitIso U e) ≫ fieldPointPushforwardScalarEndomorphismAddHom i α := by
    exact hE₁.trans (actualPointFiberFrameComparison_adjunctionUnit205 i (dual M) b₀ b₁)
  have hπNative := congrArg F.map hπ
  rw [F.map_comp, F.map_comp] at hπNative
  have hv := ConcreteCategory.congr_hom hπNative a
  change (F.map E₁.hom) ((S.map F).g a) =
    schemeModuleStalkLinearMap (fieldPointPushforwardScalarEndomorphismAddHom i α) (i y)
      ((F.map (actualPointChartFiberUnitMap207 U j (dual M) (dualRestrictUnitIso U e))) a) at hv
  have hGlobal : actualFieldPointPushforwardUnitStalkCoordinate207 i y
      ((F.map E₁.hom) ((S.map F).g a)) =
    α * κ (residue (X.presheaf.stalk (U.ι (j y)))
      ((actualDualFrameNativeStalkIso191 U (j y) M e).hom a)) := by
    rw [hv]
    have hs := fieldPointPushforwardScalarEndomorphism_stalk_coordinate i y α
      ((F.map (actualPointChartFiberUnitMap207 U j (dual M) (dualRestrictUnitIso U e))) a)
    change actualFieldPointPushforwardUnitStalkCoordinate207 i y
        (schemeModuleStalkLinearMap (fieldPointPushforwardScalarEndomorphismAddHom i α) (i y) _) =
      α * actualFieldPointPushforwardUnitStalkCoordinate207 i y _ at hs
    exact hs.trans (congrArg (fun w => α * w)
      (actualDualChartFiberUnitMap_stalkCoordinate207 U j y M e a))
  have hqv := ConcreteCategory.congr_hom hq a
  change q.hom ((S.map F).g a) =
    Ideal.Quotient.mk (Ideal.span ({t} : Set (X.presheaf.stalk (U.ι (j y)))))
      ((actualDualIncrementStalkCoefficientIso194 U (j y) M e e₀).hom a) at hqv
  rw [hqv, actualPointParameterResidueLinearEquiv_mk194,
    actualDualIncrementStalkCoefficient_residue_frameUnit205, κ.map_mul, hGlobal]
  change ρ * _ = (ρ / α) * (α * _)
  rw [← mul_assoc, div_mul_cancel₀ _ hα.ne_zero]

end PfaffianDescent
