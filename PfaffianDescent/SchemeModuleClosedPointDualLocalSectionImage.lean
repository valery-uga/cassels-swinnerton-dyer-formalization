import PfaffianDescent.SchemeModuleClosedPointDualFractionFormula
import Mathlib.LinearAlgebra.Span.Basic

/-! The image of ACTUAL local dual sections near the actual closed point.
No stalk-dual or rational-image comparison is assumed. The local section
image is identified with the inverse-generator fractional ideal of the
original local ring. Descent to the literal dual stalk is a later step. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {X : Scheme.{u}} [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Evaluation on an actual regular affine ideal generator attains EVERY
original ring section. Both the unit chart and dual-section surjectivity
are internally constructed from the same regular-principal ideal. -/
theorem closedImmersionModule_dualEvaluation_generator_surjective
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.affineOpens) [Nonempty V.1]
    (m : (closedImmersionModule i).val.obj (op V.1))
    (hreg : @IsRegular (Γ(X, V.1)) inferInstance
      ((closedImmersionModuleToUnit i).val.app (op V.1) m))
    (hprincipal : i.ker.ideal V = Ideal.span
      ({(closedImmersionModuleToUnit i).val.app (op V.1) m} : Set Γ(X, V.1))) :
    Function.Surjective
      (SchemeModuleInternalHom.evaluationBilinear (closedImmersionModule i)
        (SheafOfModules.unit X.ringCatSheaf) V.1 m) := by
  let M := (show X.Modules from closedImmersionModule i)
  let j := closedImmersionModuleToUnit i
  let z : Γ(X, V.1) := j.val.app (op V.1) m
  have hz : z ≠ 0 := isRegular_iff_ne_zero.mp hreg
  let E := closedImmersionModule_affineSectionsLinearEquivIdeal i V
  let A : Γ(X, V.1) ≃ₗ[Γ(X, V.1)] i.ker.ideal V :=
    (LinearEquiv.toSpanNonzeroSingleton (Γ(X, V.1)) (Γ(X, V.1)) z hz).trans
      (LinearEquiv.ofEq _ _ hprincipal.symm)
  let q : Γ(X, V.1) ≃ₗ[Γ(X, V.1)] M.val.obj (op V.1) := A.trans E.symm
  have hq : q (1 : Γ(X, V.1)) = m := by
    apply E.injective
    change E (E.symm (A 1)) = E m
    rw [E.apply_symm_apply]
    apply Subtype.ext
    change (1 : Γ(X, V.1)) * z = z
    exact one_mul z
  have hqm : q.symm m = (1 : Γ(X, V.1)) :=
    (congrArg q.symm hq.symm).trans (q.symm_apply_apply 1)
  letI : IsIso (schemeModuleSectionOnOpenHom M V.1 m) :=
    Coray.closedImmersionModule_affineSection_isIso_of_regularPrincipal
      i V m hreg hprincipal
  let e0 : SheafOfModules.unit (V.1 : Scheme).ringCatSheaf ≅ M.restrict V.1.ι :=
    asIso (schemeModuleSectionOnOpenHom M V.1 m)
  let e : M.over V.1 ≅ (SheafOfModules.unit X.ringCatSheaf).over V.1 :=
    ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit V.1 e0.symm ≪≫
      (SchemeModuleInternalHom.unitOverIso V.1).symm
  intro r
  change Γ(X, V.1) at r
  let F : Module.Dual (Γ(X, V.1)) (M.val.obj (op V.1)) := r • q.symm.toLinearMap
  obtain ⟨a, ha⟩ := (SchemeModuleInternalHom.sectionToDual_bijective M V.1 e).surjective F
  refine ⟨a, ?_⟩
  calc
    _ = SchemeModuleInternalHom.sectionToDual M V.1 a m := rfl
    _ = F m := congrArg (fun f : Module.Dual (Γ(X, V.1)) (M.val.obj (op V.1)) => f m) ha
    _ = r * q.symm m := rfl
    _ = r := (congrArg (fun c : Γ(X, V.1) => r * c) hqm).trans (mul_one r)

variable {K : Type u} [Field K]

/-- A rational value occurs from an ACTUAL dual section on an affine
neighborhood of P inside the generator chart iff multiplying by the actual
local equation germ lands in the original local ring. This is a genuine
local-section image theorem, not yet a map on the literal dual stalk. -/
theorem schemeModuleClosedPointDual_localSectionImage_iff
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) (V : X.affineOpens) [Nonempty V.1]
    (hPV : P.1 ∈ V.1) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let D := SchemeModuleInternalHom.dual M
    ∀ (m : M.val.obj (op V.1))
      (hreg : @IsRegular (Γ(X, V.1)) inferInstance
        ((closedImmersionModuleToUnit i).val.app (op V.1) m))
      (hprincipal : i.ker.ideal V = Ideal.span
        ({(closedImmersionModuleToUnit i).val.app (op V.1) m} : Set Γ(X, V.1)))
      (f : X.functionField),
      (∃ (W : X.affineOpens) (_hWV : W.1 ≤ V.1) (hPW : P.1 ∈ W.1),
        letI : Nonempty W.1 := ⟨⟨P.1, hPW⟩⟩
        ∃ a : SchemeModuleOpenSectionsOver pi D W.1,
          (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP W.1 a :
            X.functionField) = f) ↔
      f * algebraMap (X.presheaf.stalk P.1) X.functionField
        (X.presheaf.germ V.1 P.1 hPV
          ((closedImmersionModuleToUnit i).val.app (op V.1) m)) ∈
        Set.range (algebraMap (X.presheaf.stalk P.1) X.functionField) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let D := SchemeModuleInternalHom.dual M
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let j := closedImmersionModuleToUnit i
  intro m hreg hprincipal f
  let z : Γ(X, V.1) := j.val.app (op V.1) m
  let zP : X.presheaf.stalk P.1 := X.presheaf.germ V.1 P.1 hPV z
  let kappa : X.presheaf.stalk P.1 →+* X.functionField :=
    algebraMap (X.presheaf.stalk P.1) X.functionField
  have hz : z ≠ 0 := isRegular_iff_ne_zero.mp hreg
  have hden : kappa zP ≠ 0 := by
    have hg : kappa zP = X.germToFunctionField V.1 z :=
      Scheme.algebraMap_germ_eq_germToFunctionField X hPV z
    rw [hg]
    intro he
    apply hz
    apply X.germToFunctionField_injective V.1
    exact he.trans (map_zero (X.germToFunctionField V.1).hom).symm
  have hprod (W : X.affineOpens) (hWV : W.1 ≤ V.1) (hPW : P.1 ∈ W.1)
      (a : D.val.obj (op W.1)) :
      letI : Nonempty W.1 := ⟨⟨P.1, hPW⟩⟩
      @HMul.hMul X.functionField X.functionField X.functionField inferInstance
        (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP W.1 a)
        (kappa zP) =
      X.germToFunctionField W.1
        (SchemeModuleInternalHom.evaluationBilinear M O W.1
          (M.val.map (homOfLE hWV).op m) a) := by
    dsimp only
    letI : Nonempty W.1 := ⟨⟨P.1, hPW⟩⟩
    have hgW : genericPoint X ∈ W.1 :=
      ((genericPoint_spec X).mem_open_set_iff W.1.isOpen).mpr
        (by simpa using (inferInstance : Nonempty W.1))
    have hnat : (j.val.app (op W.1) (M.val.map (homOfLE hWV).op m) : Γ(X, W.1)) =
        X.presheaf.map (homOfLE hWV).op z :=
      PresheafOfModules.naturality_apply j.val (homOfLE hWV).op m
    have hfieldZ : X.germToFunctionField W.1
        (j.val.app (op W.1) (M.val.map (homOfLE hWV).op m)) = kappa zP :=
      (congrArg (X.germToFunctionField W.1) hnat).trans
        ((X.presheaf.germ_res_apply (homOfLE hWV) (genericPoint X) hgW z).trans
          (Scheme.algebraMap_germ_eq_germToFunctionField X hPV z).symm)
    exact (congrArg (fun t : X.functionField =>
      @HMul.hMul X.functionField X.functionField X.functionField inferInstance
        (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P hP W.1 a) t) hfieldZ).symm.trans
      (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap_mul_frame
        pi P hP W.1 (M.val.map (homOfLE hWV).op m) a)
  constructor
  · rintro ⟨W, hWV, hPW, a, ha⟩
    letI : Nonempty W.1 := ⟨⟨P.1, hPW⟩⟩
    let v : Γ(X, W.1) := SchemeModuleInternalHom.evaluationBilinear M O W.1
      (M.val.map (homOfLE hWV).op m) a
    refine ⟨X.presheaf.germ W.1 P.1 hPW v, ?_⟩
    exact (Scheme.algebraMap_germ_eq_germToFunctionField X hPW v).trans
      ((hprod W hWV hPW a).symm.trans
        (congrArg (fun t : X.functionField => t * kappa zP) ha))
  · rintro ⟨r, hr⟩
    obtain ⟨A, hAV, hPA, rA, hA⟩ := X.presheaf.exists_le_germ_eq r hPV
    obtain ⟨_, ⟨B, hB, rfl⟩, hPB, hBA⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hPA A.isOpen
    let W : X.affineOpens := ⟨B, hB⟩
    have hWV : W.1 ≤ V.1 := hBA.trans hAV
    letI : Nonempty W.1 := ⟨⟨P.1, hPB⟩⟩
    let rW : Γ(X, W.1) := X.presheaf.map (homOfLE hBA).op rA
    have hrW : X.presheaf.germ W.1 P.1 hPB rW = r :=
      (X.presheaf.germ_res_apply (homOfLE hBA) P.1 hPB rA).trans hA
    let mW := M.val.map (homOfLE hWV).op m
    let zW : Γ(X, W.1) := j.val.app (op W.1) mW
    have hnat : zW = X.presheaf.map (homOfLE hWV).op z :=
      PresheafOfModules.naturality_apply j.val (homOfLE hWV).op m
    have hzW : zW ≠ 0 := by
      intro he
      apply hz
      apply map_injective_of_isIntegral X (homOfLE hWV)
      exact hnat.symm.trans (he.trans (map_zero (X.presheaf.map (homOfLE hWV).op).hom).symm)
    have hregW : IsRegular zW := isRegular_iff_ne_zero.mpr hzW
    have hprincipalW : i.ker.ideal W = Ideal.span ({zW} : Set Γ(X, W.1)) := by
      calc
        i.ker.ideal W = (i.ker.ideal V).map (X.presheaf.map (homOfLE hWV).op).hom :=
          (i.ker.map_ideal (U := W) (V := V) hWV).symm
        _ = Ideal.span ({X.presheaf.map (homOfLE hWV).op z} : Set Γ(X, W.1)) := by
          rw [hprincipal, Ideal.map_span, Set.image_singleton]
        _ = Ideal.span ({zW} : Set Γ(X, W.1)) :=
          congrArg (fun t : Γ(X, W.1) => Ideal.span ({t} : Set Γ(X, W.1))) hnat.symm
    obtain ⟨a, ha⟩ := closedImmersionModule_dualEvaluation_generator_surjective
      i W mW hregW hprincipalW rW
    refine ⟨W, hWV, hPB, a, ?_⟩
    apply mul_right_cancel₀ hden
    exact (hprod W hWV hPB a).trans
      ((congrArg (X.germToFunctionField W.1) ha).trans
        (((Scheme.algebraMap_germ_eq_germToFunctionField X hPB rW).symm.trans
          (congrArg kappa hrW)).trans hr))

end PfaffianDescent

namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Assemble the actual generator chart and its proved local image before
specializing to the original normalization. No image comparison is supplied. -/
private theorem dual_localSectionImage_chart_of_generator003
    {X : Scheme.{u}} [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X)
    (hgen :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    ∃ (V : X.affineOpens), P.1 ∈ V.1 ∧
      ∃ m : M.val.obj (op V.1),
        let z : Γ(X, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
        IsRegular z ∧ i.ker.ideal V = Ideal.span ({z} : Set Γ(X, V.1))) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let D := SchemeModuleInternalHom.dual M
    ∃ (V : X.affineOpens) (hPV : P.1 ∈ V.1),
      letI : Nonempty V.1 := ⟨⟨P.1, hPV⟩⟩
      ∃ m : M.val.obj (op V.1),
        let z : Γ(X, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
        IsRegular z ∧ i.ker.ideal V = Ideal.span ({z} : Set Γ(X, V.1)) ∧
        ∀ f : X.functionField,
          (∃ (W : X.affineOpens) (_hWV : W.1 ≤ V.1) (hPW : P.1 ∈ W.1),
            letI : Nonempty W.1 := ⟨⟨P.1, hPW⟩⟩
            ∃ a : SchemeModuleOpenSectionsOver pi D W.1,
              (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P
                hP
                W.1 a : X.functionField) = f) ↔
          f * algebraMap (X.presheaf.stalk P.1) X.functionField
            (X.presheaf.germ V.1 P.1 hPV z) ∈
            Set.range (algebraMap (X.presheaf.stalk P.1) X.functionField) := by
  dsimp only at hgen ⊢
  obtain ⟨V, hPV, m, hreg, hprincipal⟩ := hgen
  letI : Nonempty V.1 := ⟨⟨P.1, hPV⟩⟩
  refine ⟨V, hPV, m, hreg, hprincipal, ?_⟩
  intro f
  exact schemeModuleClosedPointDual_localSectionImage_iff pi P hP
    V hPV m hreg hprincipal f

/-- Primitive original normalization has actual affine equations whose
inverse-generator local-section image is proved, never supplied. This keeps
all original pi scalars and the literal dual/point inclusion. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dual_localSectionImage
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show N.Modules from closedImmersionModule i)
      let D := SchemeModuleInternalHom.dual M
      ∃ (V : N.affineOpens) (hPV : P.1 ∈ V.1),
        letI : Nonempty V.1 := ⟨⟨P.1, hPV⟩⟩
        ∃ m : M.val.obj (op V.1),
          let z : Γ(N, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
          IsRegular z ∧ i.ker.ideal V = Ideal.span ({z} : Set Γ(N, V.1)) ∧
          ∀ f : N.functionField,
            (∃ (W : N.affineOpens) (_hWV : W.1 ≤ V.1) (hPW : P.1 ∈ W.1),
              letI : Nonempty W.1 := ⟨⟨P.1, hPW⟩⟩
              ∃ a : SchemeModuleOpenSectionsOver pi D W.1,
                (schemeModuleClosedPointDualOpenToFunctionFieldLinearMap pi P
                  (projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq P)
                  W.1 a : N.functionField) = f) ↔
            f * algebraMap (N.presheaf.stalk P.1) N.functionField
              (N.presheaf.germ V.1 P.1 hPV z) ∈
              Set.range (algebraMap (N.presheaf.stalk P.1) N.functionField) := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  intro P
  exact dual_localSectionImage_chart_of_generator003 pi P
    (projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq P)
    (projectiveIntersection_genericNormalization_closedPoint_ideal_affine_regularGenerator
      p q hp hp0 n hn hq hnot P)

end PfaffianDescent.Coray
