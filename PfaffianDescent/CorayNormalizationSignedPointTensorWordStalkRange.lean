import PfaffianDescent.SchemeModuleSignedPointTensorWordStalkRange
import PfaffianDescent.SchemeModuleFixedFrameStalkInjectiveOfLocallyRankOne

/-! Primitive local image and injectivity of the SAME actual signed word
on the SAME normalization. Actual point charts and ONE affine generator
are constructed internally before any word is chosen.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem locallyRankOne_of_affineUnitSections
    {X : Scheme.{u}} (L : X.Modules)
    (hcharts : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ m : L.val.obj (op U.1), IsIso (schemeModuleSectionOnOpenHom L U.1 m)) :
    schemeModuleLocallyRankOne L := by
  intro x
  obtain ⟨U, hxU, m, hm⟩ := hcharts x
  letI := hm
  let e : SheafOfModules.unit (U.1 : Scheme).ringCatSheaf ≅ L.restrict U.1.ι :=
    asIso (schemeModuleSectionOnOpenHom L U.1 m)
  exact ⟨U.1, hxU, ⟨ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit U.1 e.symm ≪≫
    (SchemeModuleInternalHom.unitOverIso U.1).symm⟩⟩

private theorem wordStalkRange_of_actualGenerator
    {X : Scheme.{u}} [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hNG : ∀ Q : closedPoints X, Q.1 ≠ genericPoint X)
    (hM : ∀ Q : closedPoints X,
      let i := X.fromSpecResidueField Q.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp Q.2
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
    ∃ (V : X.affineOpens) (hPV : P.1 ∈ V.1) (m : M.val.obj (op V.1)),
      let z : Γ(X, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
      let zP := X.presheaf.germ V.1 P.1 hPV z
      IsRegular z ∧ i.ker.ideal V = Ideal.span ({z} : Set Γ(X, V.1)) ∧ Irreducible zP ∧
      ∀ ops : List (closedPoints X × Bool),
        let hP : ∀ operation ∈ ops, operation.1.1 ≠ genericPoint X := fun operation _ => hNG operation.1
        let C := schemeSignedPointTensorWordComplementOpen ops
        letI : Nonempty C := ⟨⟨genericPoint X, schemeSignedPointTensorWordComplementOpen_generic_mem ops hP⟩⟩
        let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
        let W := schemeModuleIteratedSignedClosedPointTensor O ops
        letI := schemeModuleStalkModule W P.1
        let ψ := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi W C
          (schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso C ops
            (schemeSignedPointTensorWordComplementOpen_excludes ops) O (Iso.refl _)) P.1
        Function.Injective ψ ∧ Set.range ψ =
          Set.range (fun r : X.presheaf.stalk P.1 =>
            @HMul.hMul X.functionField X.functionField X.functionField inferInstance
              (algebraMap (X.presheaf.stalk P.1) X.functionField r)
              ((algebraMap (X.presheaf.stalk P.1) X.functionField zP) ^
                schemeSignedPointTensorWordLocalOrder P ops)) := by
  dsimp only at hgen ⊢
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  obtain ⟨V, hPV, m, hreg, hprincipal⟩ := hgen
  refine ⟨V, hPV, m, hreg, hprincipal,
    closedPointIdeal_affineRegularGenerator_germ_irreducible X P V hPV m hreg hprincipal, ?_⟩
  intro ops
  let hP : ∀ operation ∈ ops, operation.1.1 ≠ genericPoint X := fun operation _ => hNG operation.1
  let C := schemeSignedPointTensorWordComplementOpen ops
  letI : Nonempty C := ⟨⟨genericPoint X, schemeSignedPointTensorWordComplementOpen_generic_mem ops hP⟩⟩
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let W := schemeModuleIteratedSignedClosedPointTensor O ops
  letI := schemeModuleStalkModule W P.1
  let eW := schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso C ops
    (schemeSignedPointTensorWordComplementOpen_excludes ops) O (Iso.refl _)
  have hO : schemeModuleLocallyRankOne O := fun x => ⟨⊤, by simp, ⟨Iso.refl _⟩⟩
  constructor
  · exact schemeModuleFixedFrameStalkToFunctionFieldLinearMap_injective_of_locallyRankOne pi W
      (schemeModuleIteratedSignedClosedPointTensor_locallyRankOne ops O hM hO) C eW P.1
  · exact schemeModuleSignedPointTensorWord_stalkRange_zpow pi P V hPV ops hP hM m hreg hprincipal

/-- Original positive-degree integral p/q normalization: ONE actual
regular affine generator is chosen at each test point P BEFORE any word.
EVERY actual signed word then embeds into the original function field with
FULL original local-ring image scaled by its germ to negative-count minus
positive-count at P. All point geometry and the canonical word frame are
derived internally; no rank-one, generator, image or valuation premise. -/
theorem projectiveIntersection_genericNormalization_signedPointTensorWord_stalkRange
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
      ∃ (V : N.affineOpens) (hPV : P.1 ∈ V.1) (m : M.val.obj (op V.1)),
        let z : Γ(N, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
        let zP := N.presheaf.germ V.1 P.1 hPV z
        IsRegular z ∧ i.ker.ideal V = Ideal.span ({z} : Set Γ(N, V.1)) ∧ Irreducible zP ∧
        ∀ ops : List (closedPoints N × Bool),
          let hP : ∀ operation ∈ ops, operation.1.1 ≠ genericPoint N :=
            fun operation _ => projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq operation.1
          let C := schemeSignedPointTensorWordComplementOpen ops
          letI : Nonempty C := ⟨⟨genericPoint N, schemeSignedPointTensorWordComplementOpen_generic_mem ops hP⟩⟩
          let O := (show N.Modules from SheafOfModules.unit N.ringCatSheaf)
          let W := schemeModuleIteratedSignedClosedPointTensor O ops
          letI := schemeModuleStalkModule W P.1
          let ψ := schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi W C
            (schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso C ops
              (schemeSignedPointTensorWordComplementOpen_excludes ops) O (Iso.refl _)) P.1
          Function.Injective ψ ∧ Set.range ψ =
            Set.range (fun r : N.presheaf.stalk P.1 =>
              @HMul.hMul N.functionField N.functionField N.functionField inferInstance
                (algebraMap (N.presheaf.stalk P.1) N.functionField r)
                ((algebraMap (N.presheaf.stalk P.1) N.functionField zP) ^
                  schemeSignedPointTensorWordLocalOrder P ops)) := by
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  have hNG : ∀ Q : closedPoints N, Q.1 ≠ genericPoint N :=
    projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq
  have hM : ∀ Q : closedPoints N,
      let i := N.fromSpecResidueField Q.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp Q.2
      schemeModuleLocallyRankOne (closedImmersionModule i) := by
    intro Q
    dsimp only
    let i := N.fromSpecResidueField Q.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp Q.2
    let M := (show N.Modules from closedImmersionModule i)
    apply locallyRankOne_of_affineUnitSections M
    intro x
    obtain ⟨U, hxU, m, hm, _hreg, _hprincipal⟩ :=
      projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
        p q hp hp0 n hn hq hnot Q x
    exact ⟨U, hxU, m, hm⟩
  intro P
  exact wordStalkRange_of_actualGenerator pi P hNG hM
    (projectiveIntersection_genericNormalization_closedPoint_ideal_affine_regularGenerator
      p q hp hp0 n hn hq hnot P)

end PfaffianDescent.Coray
