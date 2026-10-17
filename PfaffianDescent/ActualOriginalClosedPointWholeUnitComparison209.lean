import PfaffianDescent.ActualWholePointQuotientFrameUnitAssembly209
import PfaffianDescent.ActualClosedPointRegularWholeDualCokernelPrincipal200
import PfaffianDescent.ActualClosedPointGlobalDualQuotientSupport203

/-! SOURCE ONLY209. Original point geometry constructs the WHOLE global
quotient comparison to200/194's principal coefficient. Literal lift_fac and
image=P transport are outputs; no coefficient comparison is a premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open SchemeModuleInternalHom IdealSheafDataModule IsLocalRing
open scoped nonZeroDivisors
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem actualOriginalClosedPoint_exists_wholeUnitComparison209
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (P : closedPoints X) [IsDiscreteValuationRing (X.presheaf.stalk P.1)] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let D := dual M
    let χ := closedImmersionModuleToUnit i
    let S := incrementCokernelSequence χ
    S.ShortExact ∧
      ∃ (U : X.Opens) (hPU : P.1 ∈ U)
        (j : Spec (X.residueField P.1) ⟶ (U : Scheme)) (hji : j ≫ U.ι = i),
        let y : Spec (X.residueField P.1) := default
        let x := j y
        let hp : U.ι x = P.1 := (congrArg (fun f => f y) hji).trans
          (Scheme.fromSpecResidueField_apply P.1 y)
        let R := X.presheaf.stalk (U.ι x)
        let F := schemeModuleStalkModuleFunctor X (U.ι x)
        ∃ (t : R) (e₀ : R ≃ₗ[R] F.obj M)
          (hspan : maximalIdeal R = Ideal.span ({t} : Set R)),
          t ∈ R⁰ ∧
          (∀ r, schemeModuleStalkToRingLinearMap χ (U.ι x) (e₀ r) = r * t) ∧
          ∃ e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U,
          let d := actualDualIncrementStalkCoefficientIso194 U x M e e₀
          ∃ (q : (S.map F).X₃ ≅ (pointCartierYonedaCoefficientComplex t).X₃)
            (a : S.map F ≅ pointCartierYonedaCoefficientComplex t),
            (S.map F).g ≫ q.hom = d.hom ≫ (pointCartierYonedaCoefficientComplex t).g ∧
            a.hom.τ₁ = (schemeModuleUnitStalkIso X (U.ι x)).hom ∧
            a.hom.τ₂ = d.hom ∧ a.hom.τ₃ = q.hom ∧
            ∃ (b₁ : (Scheme.Modules.pullback (j ≫ U.ι)).obj D ≅
              (show (Spec (X.residueField P.1)).Modules from
                SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf))
              (E₁ : S.X₃ ≅ (Scheme.Modules.pushforward (j ≫ U.ι)).obj
                (show (Spec (X.residueField P.1)).Modules from
                  SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)),
              S.g ≫ E₁.hom = (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ U.ι)).unit.app D ≫
                (Scheme.Modules.pushforward (j ≫ U.ι)).map b₁.hom ∧
              let b₀ := schemeModuleFiberFrameIso U.ι j D (dualRestrictUnitIso U e)
              let α : X.residueField P.1 :=
                actualPointFiberFrameComparisonScalar205 (L := X.residueField P.1) (j ≫ U.ι) D b₀ b₁
              let ρ := (X.residueFieldCongr hp).hom
                (residue R (actualOriginalIdealFrameUnit205 U x M e e₀))
              ∃ E₀ : S.X₃ ≅ (Scheme.Modules.pushforward (j ≫ U.ι)).obj
                (show (Spec (X.residueField P.1)).Modules from
                  SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf),
                S.g ≫ E₀.hom = (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ U.ι)).unit.app D ≫
                  (Scheme.Modules.pushforward (j ≫ U.ι)).map b₀.hom ∧
                E₁.hom = E₀.hom ≫ (Scheme.Modules.pushforward (j ≫ U.ι)).map
                  (schemeModuleConstantEndomorphism (𝟙 (Spec (X.residueField P.1))) α) ∧
                IsUnit (ρ / α) ∧
                ∀ z : (S.map F).X₃,
                  (X.residueFieldCongr hp).hom
                      (actualPointParameterResidueLinearEquiv194 t hspan (q.hom z)) =
                    (ρ / α) * actualFieldPointPushforwardUnitStalkCoordinate207
                      (L := X.residueField P.1) (j ≫ U.ι) y
                      ((F.map E₁.hom) z) := by
  classical
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let D := dual M
  let χ := closedImmersionModuleToUnit i
  let S := incrementCokernelSequence χ
  obtain ⟨hS, t, e₀, ht, hspan, he₀, U, hPU, e, q, hq, a, ha₁, ha₂, ha₃⟩ :=
    actualClosedPoint_exists_regularWholeDualCokernelPrincipal200 X P
  refine ⟨hS, U, hPU, ?_⟩
  have hrange : Set.range i ⊆ Set.range U.ι := by
    rintro w ⟨v, rfl⟩
    rw [Scheme.fromSpecResidueField_apply]
    exact ⟨⟨P.1, hPU⟩, rfl⟩
  let j := IsOpenImmersion.lift U.ι i hrange
  have hji : j ≫ U.ι = i := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion (j ≫ U.ι) := hji.symm ▸ inferInstance
  let y : Spec (X.residueField P.1) := default
  let xP : U := ⟨P.1, hPU⟩
  have hxy : j y = xP := by
    apply Subtype.ext
    exact (congrArg (fun f => f y) hji).trans (Scheme.fromSpecResidueField_apply P.1 y)
  let predicate (w : U) : Prop :=
    let R := X.presheaf.stalk (U.ι w)
    let F := schemeModuleStalkModuleFunctor X (U.ι w)
    ∃ (t : R) (e₀ : R ≃ₗ[R] F.obj M),
      t ∈ R⁰ ∧ maximalIdeal R = Ideal.span ({t} : Set R) ∧
      (∀ r, schemeModuleStalkToRingLinearMap χ (U.ι w) (e₀ r) = r * t) ∧
      ∃ (q : (S.map F).X₃ ≅ (pointCartierYonedaCoefficientComplex t).X₃)
        (a : S.map F ≅ pointCartierYonedaCoefficientComplex t),
        (S.map F).g ≫ q.hom =
          (actualDualIncrementStalkCoefficientIso194 U w M e e₀).hom ≫
            (pointCartierYonedaCoefficientComplex t).g ∧
        a.hom.τ₁ = (schemeModuleUnitStalkIso X (U.ι w)).hom ∧
        a.hom.τ₂ = (actualDualIncrementStalkCoefficientIso194 U w M e e₀).hom ∧
        a.hom.τ₃ = q.hom
  have hAtP : predicate xP := ⟨t, e₀, ht, hspan, he₀, q, a, hq, ha₁, ha₂, ha₃⟩
  have hAtImage : predicate (j y) := by simpa only [hxy] using hAtP
  obtain ⟨t₀, e₀', ht₀, hspan₀, he₀', q₀, a₀, hq₀, ha₁', ha₂', ha₃'⟩ := hAtImage
  obtain ⟨_, bGlobal, EGlobal, hGlobal⟩ := actualClosedPoint_exists_globalDualQuotientSupport203 X P
  have hFiber : ∃ (b₁ : (Scheme.Modules.pullback (j ≫ U.ι)).obj D ≅
      (show (Spec (X.residueField P.1)).Modules from
        SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf))
      (E₁ : S.X₃ ≅ (Scheme.Modules.pushforward (j ≫ U.ι)).obj
        (show (Spec (X.residueField P.1)).Modules from
          SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)),
      S.g ≫ E₁.hom = (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ U.ι)).unit.app D ≫
        (Scheme.Modules.pushforward (j ≫ U.ι)).map b₁.hom := by
    have hOriginal : ∃ (b : (Scheme.Modules.pullback i).obj D ≅
        (show (Spec (X.residueField P.1)).Modules from
          SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf))
        (E : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
          (show (Spec (X.residueField P.1)).Modules from
            SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)),
        S.g ≫ E.hom = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D ≫
          (Scheme.Modules.pushforward i).map b.hom := ⟨bGlobal, EGlobal, hGlobal⟩
    let fiberPredicate (k : Spec (X.residueField P.1) ⟶ X) : Prop :=
      ∃ (b : (Scheme.Modules.pullback k).obj D ≅
          (show (Spec (X.residueField P.1)).Modules from
            SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf))
        (E : S.X₃ ≅ (Scheme.Modules.pushforward k).obj
          (show (Spec (X.residueField P.1)).Modules from
            SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)),
        S.g ≫ E.hom = (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app D ≫
          (Scheme.Modules.pushforward k).map b.hom
    have hOriginalTyped : fiberPredicate i := hOriginal
    exact Eq.mp (congrArg fiberPredicate hji.symm) hOriginalTyped
  obtain ⟨b₁, E₁, hE₁⟩ := hFiber
  let G := Scheme.Modules.pushforward (j ≫ U.ι)
  let b₀ := schemeModuleFiberFrameIso U.ι j D (dualRestrictUnitIso U e)
  let α : X.residueField P.1 :=
    actualPointFiberFrameComparisonScalar205 (L := X.residueField P.1) (j ≫ U.ι) D b₀ b₁
  let E₀ := E₁ ≪≫ G.mapIso (b₁.symm ≪≫ b₀)
  have hE₀ : S.g ≫ E₀.hom =
      (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ U.ι)).unit.app D ≫ G.map b₀.hom := by
    change S.g ≫ (E₁.hom ≫ G.map (b₁.inv ≫ b₀.hom)) = _
    rw [← Category.assoc, hE₁]
    calc
      ((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ U.ι)).unit.app D ≫
          G.map b₁.hom) ≫ G.map (b₁.inv ≫ b₀.hom) =
        (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ U.ι)).unit.app D ≫
          G.map (b₁.hom ≫ (b₁.inv ≫ b₀.hom)) := by
            simp only [G.map_comp, Category.assoc]
      _ = _ := by rw [← Category.assoc, b₁.hom_inv_id, Category.id_comp]
  letI : Epi S.g := hS.epi_g
  have hFrame := (actualWholePointQuotient_frameComparison209 (L := X.residueField P.1)
    (j ≫ U.ι) D S.X₃ S.g b₀ b₁ E₀ E₁ hE₀ hE₁).2
  let F := schemeModuleStalkModuleFunctor X (U.ι (j y))
  have hTotal :
      IsUnit ((closedFieldPointResidueRingEquivAt (L := X.residueField P.1) (j ≫ U.ι) y
        (residue (X.presheaf.stalk (U.ι (j y)))
          (actualOriginalIdealFrameUnit205 U (j y) M e e₀'))) / α) ∧
      ∀ z : (S.map F).X₃,
        closedFieldPointResidueRingEquivAt (L := X.residueField P.1) (j ≫ U.ι) y
            (actualPointParameterResidueLinearEquiv194 t₀ hspan₀ (q₀.hom z)) =
          ((closedFieldPointResidueRingEquivAt (L := X.residueField P.1) (j ≫ U.ι) y
            (residue (X.presheaf.stalk (U.ι (j y)))
              (actualOriginalIdealFrameUnit205 U (j y) M e e₀'))) / α) *
            actualFieldPointPushforwardUnitStalkCoordinate207 (L := X.residueField P.1)
              (j ≫ U.ι) y ((F.map E₁.hom) z) :=
    actualWholePointQuotient_totalResidueUnit209 (L := X.residueField P.1) U j y M e χ hS
      e₀' t₀ he₀' hspan₀ q₀ hq₀ b₁ E₁ hE₁
  let hp : U.ι (j y) = P.1 := (congrArg (fun f => f y) hji).trans
    (Scheme.fromSpecResidueField_apply P.1 y)
  have hResidue : closedFieldPointResidueRingEquivAt (L := X.residueField P.1) (j ≫ U.ι) y =
      (X.residueFieldCongr hp).commRingCatIsoToRingEquiv :=
    actualOriginalResiduePointCoordinate_eq207 P.1 (j ≫ U.ι) hji y
  rw [hResidue] at hTotal
  refine ⟨j, hji, t₀, e₀', hspan₀, ht₀, he₀', e, q₀, a₀,
    hq₀, ha₁', ha₂', ha₃', b₁, E₁, hE₁, E₀, hE₀, hFrame, ?_, ?_⟩
  · exact hTotal.1
  · exact hTotal.2

end PfaffianDescent
