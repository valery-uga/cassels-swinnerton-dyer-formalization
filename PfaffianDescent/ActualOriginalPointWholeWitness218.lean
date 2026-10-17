import PfaffianDescent.ActualOriginalClosedPointWholeUnitComparison209

/-! SOURCE ONLY218. Transport the SAME209 witnesses to the literal original
closed point. No independently chosen principal frame or quotient frame. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open SchemeModuleInternalHom IdealSheafDataModule IsLocalRing
open scoped nonZeroDivisors
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem actualOriginalClosedPoint_exists_literalWholeWitness218
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (P : closedPoints X) [IsDiscreteValuationRing (X.presheaf.stalk P.1)] :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let D := dual M
    let chi := closedImmersionModuleToUnit i
    let S := incrementCokernelSequence chi
    let B := X.presheaf.stalk P.1
    let F := schemeModuleStalkModuleFunctor X P.1
    S.ShortExact ∧
      ∃ (U : X.Opens) (hPU : P.1 ∈ U)
        (j : Spec (X.residueField P.1) ⟶ (U : Scheme)) (hji : j ≫ U.ι = i),
      ∃ e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U,
      ∃ (t : B) (e0 : B ≃ₗ[B] F.obj M)
        (hspan : maximalIdeal B = Ideal.span ({t} : Set B)),
        t ∈ B⁰ ∧
        (∀ r, schemeModuleStalkToRingLinearMap chi P.1 (e0 r) = r * t) ∧
        ∃ a : S.map F ≅ pointCartierYonedaCoefficientComplex t,
          a.hom.τ₁ = (schemeModuleUnitStalkIso X P.1).hom ∧
          a.hom.τ₂ = (actualDualIncrementStalkCoefficientIso194 U ⟨P.1, hPU⟩ M e e0).hom ∧
          ∃ (b : (Scheme.Modules.pullback i).obj D ≅
            (show (Spec (X.residueField P.1)).Modules from
              SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf))
            (E : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
              (show (Spec (X.residueField P.1)).Modules from
                SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)),
            S.g ≫ E.hom = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D ≫
              (Scheme.Modules.pushforward i).map b.hom := by
  classical
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let D := dual M
  let chi := closedImmersionModuleToUnit i
  let S := incrementCokernelSequence chi
  obtain ⟨hS, U, hPU, j, hji, t, e0, hspan, ht, he0, e,
    q, a, hq, ha1, ha2, ha3, b, E, hE, E0, hE0, hFrame, hUnit, hCoeff⟩ :=
    actualOriginalClosedPoint_exists_wholeUnitComparison209 X P
  let y : Spec (X.residueField P.1) := default
  have hImage : j y = (⟨P.1, hPU⟩ : U) := by
    apply Subtype.ext
    exact (congrArg (fun f => f y) hji).trans
      (Scheme.fromSpecResidueField_apply P.1 y)
  let nativeData (w : U) : Prop :=
    let B := X.presheaf.stalk (U.ι w)
    let F := schemeModuleStalkModuleFunctor X (U.ι w)
    ∃ (t : B) (e0 : B ≃ₗ[B] F.obj M)
      (hspan : maximalIdeal B = Ideal.span ({t} : Set B)),
      t ∈ B⁰ ∧
      (∀ r, schemeModuleStalkToRingLinearMap chi (U.ι w) (e0 r) = r * t) ∧
      ∃ a : S.map F ≅ pointCartierYonedaCoefficientComplex t,
        a.hom.τ₁ = (schemeModuleUnitStalkIso X (U.ι w)).hom ∧
        a.hom.τ₂ = (actualDualIncrementStalkCoefficientIso194 U w M e e0).hom
  have hNativeImage : nativeData (j y) :=
    ⟨t, e0, hspan, ht, he0, a, ha1, ha2⟩
  have hNativePoint : nativeData ⟨P.1, hPU⟩ :=
    Eq.mp (congrArg nativeData hImage) hNativeImage
  obtain ⟨tP, e0P, hspanP, htP, he0P, aP, ha1P, ha2P⟩ := hNativePoint
  let globalData (k : Spec (X.residueField P.1) ⟶ X) : Prop :=
    ∃ (bP : (Scheme.Modules.pullback k).obj D ≅
      (show (Spec (X.residueField P.1)).Modules from
        SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf))
      (EP : S.X₃ ≅ (Scheme.Modules.pushforward k).obj
        (show (Spec (X.residueField P.1)).Modules from
          SheafOfModules.unit (Spec (X.residueField P.1)).ringCatSheaf)),
      S.g ≫ EP.hom = (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app D ≫
        (Scheme.Modules.pushforward k).map bP.hom
  have hAtChart : globalData (j ≫ U.ι) := ⟨b, E, hE⟩
  have hGlobal : globalData i := Eq.mp (congrArg globalData hji) hAtChart
  obtain ⟨bP, EP, hEP⟩ := hGlobal
  exact ⟨hS, U, hPU, j, hji, e, tP, e0P, hspanP, htP, he0P,
    aP, ha1P, ha2P, bP, EP, hEP⟩

end PfaffianDescent
