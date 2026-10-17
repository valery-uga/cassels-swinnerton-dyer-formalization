import PfaffianDescent.SchemeModuleClosedPointDualStalkFunctionField
import PfaffianDescent.SchemeModuleClosedPointDualLocalSectionImage

/-! Range of the SAME canonical actual dual-stalk map. Actual local
germ representatives and the proved local-section image give the literal
inverse-generator fractional ideal; no image comparison is a premise.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open IdealSheafDataModule
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The range of the LITERAL canonical stalk map is detected by the SAME
regular affine generator. The only generic geometric data is the actual
regular-principal ideal chart; the local image condition is proved. -/
theorem schemeModuleClosedPointDual_stalkRange_iff
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) (V : X.affineOpens) [Nonempty V.1]
    (hPV : P.1 ∈ V.1) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let D := SchemeModuleInternalHom.dual M
    letI := schemeModuleStalkModule D P.1
    ∀ (m : M.val.obj (op V.1))
      (hreg : @IsRegular (Γ(X, V.1)) inferInstance
        ((closedImmersionModuleToUnit i).val.app (op V.1) m))
      (hprincipal : i.ker.ideal V = Ideal.span
        ({(closedImmersionModuleToUnit i).val.app (op V.1) m} : Set Γ(X, V.1)))
      (f : X.functionField),
      f ∈ Set.range (schemeModuleClosedPointDualStalkToFunctionFieldLinearMap pi P hP) ↔
        f * algebraMap (X.presheaf.stalk P.1) X.functionField
          (X.presheaf.germ V.1 P.1 hPV
            ((closedImmersionModuleToUnit i).val.app (op V.1) m)) ∈
          Set.range (algebraMap (X.presheaf.stalk P.1) X.functionField) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let D := SchemeModuleInternalHom.dual M
  letI := schemeModuleStalkModule D P.1
  let ψ := schemeModuleClosedPointDualStalkToFunctionFieldLinearMap pi P hP
  intro m hreg hprincipal f
  refine Iff.trans ?_
    (schemeModuleClosedPointDual_localSectionImage_iff pi P hP V hPV m hreg hprincipal f)
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨U, hUV, hPU, aU, hUa⟩ := D.presheaf.exists_le_germ_eq a hPV
    obtain ⟨_, ⟨W, hW, rfl⟩, hPW, hWU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hPU U.isOpen
    let A : X.affineOpens := ⟨W, hW⟩
    letI : Nonempty A.1 := ⟨⟨P.1, hPW⟩⟩
    let aW : D.val.obj (op A.1) := D.val.map (homOfLE hWU).op aU
    have hgerm : D.presheaf.germ A.1 P.1 hPW aW = a :=
      (D.presheaf.germ_res_apply (homOfLE hWU) P.1 hPW aU).trans hUa
    refine ⟨A, hWU.trans hUV, hPW, aW, ?_⟩
    exact (schemeModuleClosedPointDualStalkToFunctionFieldLinearMap_germ
      pi P hP A.1 hPW aW).symm.trans ((congrArg ψ hgerm).trans ha)
  · rintro ⟨W, _hWV, hPW, a, ha⟩
    letI : Nonempty W.1 := ⟨⟨P.1, hPW⟩⟩
    exact ⟨D.presheaf.germ W.1 P.1 hPW a,
      (schemeModuleClosedPointDualStalkToFunctionFieldLinearMap_germ
        pi P hP W.1 hPW a).trans ha⟩

/-- Actual range equals the image of r ↦ kappa(r)/kappa(z_P), on the
ORIGINAL local ring and field. Nonzero denominator follows internally
from actual regularity and the original injective generic germ. -/
theorem schemeModuleClosedPointDual_stalkRange_eq_inverseGenerator
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X) (V : X.affineOpens) [Nonempty V.1]
    (hPV : P.1 ∈ V.1) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let D := SchemeModuleInternalHom.dual M
    letI := schemeModuleStalkModule D P.1
    ∀ (m : M.val.obj (op V.1))
      (hreg : @IsRegular (Γ(X, V.1)) inferInstance
        ((closedImmersionModuleToUnit i).val.app (op V.1) m))
      (hprincipal : i.ker.ideal V = Ideal.span
        ({(closedImmersionModuleToUnit i).val.app (op V.1) m} : Set Γ(X, V.1))),
      Set.range (schemeModuleClosedPointDualStalkToFunctionFieldLinearMap pi P hP) =
        Set.range (fun r : X.presheaf.stalk P.1 =>
          algebraMap (X.presheaf.stalk P.1) X.functionField r /
          algebraMap (X.presheaf.stalk P.1) X.functionField
            (X.presheaf.germ V.1 P.1 hPV
              ((closedImmersionModuleToUnit i).val.app (op V.1) m))) := by
  dsimp only
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  intro m hreg hprincipal
  let z : Γ(X, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
  let zP : X.presheaf.stalk P.1 := X.presheaf.germ V.1 P.1 hPV z
  let κ : X.presheaf.stalk P.1 →+* X.functionField :=
    algebraMap (X.presheaf.stalk P.1) X.functionField
  have hz : z ≠ 0 := isRegular_iff_ne_zero.mp hreg
  have hden : κ zP ≠ 0 := by
    have hg : κ zP = X.germToFunctionField V.1 z :=
      Scheme.algebraMap_germ_eq_germToFunctionField X hPV z
    rw [hg]
    intro he
    apply hz
    apply X.germToFunctionField_injective V.1
    exact he.trans (map_zero (X.germToFunctionField V.1).hom).symm
  apply Set.ext
  intro f
  refine (schemeModuleClosedPointDual_stalkRange_iff
    pi P hP V hPV m hreg hprincipal f).trans ?_
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, ((eq_div_iff hden).mpr hr.symm).symm⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, ((eq_div_iff hden).mp hr.symm).symm⟩

end PfaffianDescent

namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Assemble the actual stalk-range chart BEFORE specializing X to the
normalization. Only actual unit-chart geometry and an actual regular ideal
generator are generic inputs; every image/injectivity conclusion is derived. -/
private theorem dual_stalkRange_chart_of_regularGenerator
    {X : Scheme.{u}} [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hP : P.1 ≠ genericPoint X)
    (hM : let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i))
    (hgen :
      let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show X.Modules from closedImmersionModule i)
      ∃ V : X.affineOpens, P.1 ∈ V.1 ∧ ∃ m : M.val.obj (op V.1),
        let z : Γ(X, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
        IsRegular z ∧ i.ker.ideal V = Ideal.span ({z} : Set Γ(X, V.1))) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let D := SchemeModuleInternalHom.dual M
    letI := schemeModuleStalkModule D P.1
    Function.Injective (schemeModuleClosedPointDualStalkToFunctionFieldLinearMap pi P hP) ∧
      ∃ (V : X.affineOpens) (hPV : P.1 ∈ V.1),
        letI : Nonempty V.1 := ⟨⟨P.1, hPV⟩⟩
        ∃ m : M.val.obj (op V.1),
          let z : Γ(X, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
          IsRegular z ∧ i.ker.ideal V = Ideal.span ({z} : Set Γ(X, V.1)) ∧
          Set.range (schemeModuleClosedPointDualStalkToFunctionFieldLinearMap pi P hP) =
            Set.range (fun r : X.presheaf.stalk P.1 =>
              algebraMap (X.presheaf.stalk P.1) X.functionField r /
              algebraMap (X.presheaf.stalk P.1) X.functionField
                (X.presheaf.germ V.1 P.1 hPV z)) := by
  dsimp only at hM hgen ⊢
  constructor
  · exact schemeModuleClosedPointDualStalkToFunctionFieldLinearMap_injective pi P hP hM
  · obtain ⟨V, hPV, m, hreg, hprincipal⟩ := hgen
    letI : Nonempty V.1 := ⟨⟨P.1, hPV⟩⟩
    exact ⟨V, hPV, m, hreg, hprincipal,
      schemeModuleClosedPointDual_stalkRange_eq_inverseGenerator
        pi P hP V hPV m hreg hprincipal⟩

/-- Primitive ORIGINAL normalization: the SAME actual dual stalk embeds
into N.functionField, with image the inverse of its actual local point
equation times the actual local ring. Nongenericity, actual rank-one charts
and the regular generator are all derived from ordinary positive-degree
integral p/q geometry. No rational/image/chart/injectivity certificate input. -/
theorem projectiveIntersection_genericNormalization_closedPoint_dual_stalkRange
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
      let hP := projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq P
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show N.Modules from closedImmersionModule i)
      let D := SchemeModuleInternalHom.dual M
      letI := schemeModuleStalkModule D P.1
      Function.Injective (schemeModuleClosedPointDualStalkToFunctionFieldLinearMap pi P hP) ∧
        ∃ (V : N.affineOpens) (hPV : P.1 ∈ V.1),
          letI : Nonempty V.1 := ⟨⟨P.1, hPV⟩⟩
          ∃ m : M.val.obj (op V.1),
            let z : Γ(N, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
            IsRegular z ∧ i.ker.ideal V = Ideal.span ({z} : Set Γ(N, V.1)) ∧
            Set.range (schemeModuleClosedPointDualStalkToFunctionFieldLinearMap pi P hP) =
              Set.range (fun r : N.presheaf.stalk P.1 =>
                algebraMap (N.presheaf.stalk P.1) N.functionField r /
                algebraMap (N.presheaf.stalk P.1) N.functionField
                  (N.presheaf.germ V.1 P.1 hPV z)) := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  intro P
  let i := N.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show N.Modules from closedImmersionModule i)
  have hP : P.1 ≠ genericPoint N :=
    projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq P
  have hM : schemeModuleLocallyRankOne M := by
    intro x
    obtain ⟨U, hxU, m, hm, _hreg, _hprincipal⟩ :=
      projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
        p q hp hp0 n hn hq hnot P x
    letI := hm
    let e : SheafOfModules.unit (U.1 : Scheme).ringCatSheaf ≅ M.restrict U.1.ι :=
      asIso (schemeModuleSectionOnOpenHom M U.1 m)
    exact ⟨U.1, hxU, ⟨ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit U.1 e.symm ≪≫
      (SchemeModuleInternalHom.unitOverIso U.1).symm⟩⟩
  exact dual_stalkRange_chart_of_regularGenerator pi P hP hM
    (projectiveIntersection_genericNormalization_closedPoint_ideal_affine_regularGenerator
      p q hp hp0 n hn hq hnot P)

end PfaffianDescent.Coray
