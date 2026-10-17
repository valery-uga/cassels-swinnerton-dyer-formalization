import PfaffianDescent.SchemeModuleCanonicalSignedPointTensorWord
import PfaffianDescent.CorayNormalizationClosedPointNongeneric

/-! Primitive original-K actual signed tensor WORD injection and actual
canonical word-prefix multiplication on the SAME original normalization.
Nongenericity, common-open nonemptiness and rank-one word geometry are
internal. No rational frame or multiplication/injection certificate input.
The full local pole/zero image classification remains separate.
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

/-- The primitive actual finite signed WORD embeds original-K global
sections into SAME N.functionField through its canonical support-complement
frame. All geometric construction/injectivity inputs are internally proved. -/
theorem projectiveIntersection_genericNormalization_signedPointTensorWord_toFunctionField_injective
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
    ∀ ops : List (closedPoints N × Bool),
      let hP : ∀ operation ∈ ops, operation.1.1 ≠ genericPoint N :=
        fun operation _ => projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq operation.1
      Function.Injective (schemeModuleSignedPointTensorWordToFunctionFieldLinearMap pi ops hP) := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  intro ops
  have hM : ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      schemeModuleLocallyRankOne (closedImmersionModule i) := by
    intro P
    dsimp only
    let i := N.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show N.Modules from closedImmersionModule i)
    intro x
    obtain ⟨U, hxU, m, hm, _hreg, _hprincipal⟩ :=
      projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
        p q hp hp0 n hn hq hnot P x
    letI := hm
    let e : SheafOfModules.unit (U.1 : Scheme).ringCatSheaf ≅ M.restrict U.1.ι :=
      asIso (schemeModuleSectionOnOpenHom M U.1 m)
    exact ⟨U.1, hxU, ⟨ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit U.1 e.symm ≪≫
      (SchemeModuleInternalHom.unitOverIso U.1).symm⟩⟩
  exact schemeModuleSignedPointTensorWordToFunctionFieldLinearMap_injective pi ops _ hM

/-- Primitive canonical WORD-prefix field multiplication, on the full
word's actual common complement. The original factor order, sheafification
unit and original pi scalars remain unchanged. Point nongenericity and
all frames are internal; list containment is ordinary combinatorial data. -/
theorem projectiveIntersection_genericNormalization_signedPointTensorWord_prefixStep_fieldPureSection
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
    ∀ (ops «prefix» : List (closedPoints N × Bool)) (hprefix : «prefix» ⊆ ops)
      (operation : closedPoints N × Bool) (hmem : operation ∈ ops),
      let hP : ∀ a ∈ ops, a.1.1 ≠ genericPoint N :=
        fun a _ => projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq a.1
      let U := schemeSignedPointTensorWordComplementOpen ops
      let hgU := schemeSignedPointTensorWordComplementOpen_generic_mem ops hP
      let hPU := schemeSignedPointTensorWordComplementOpen_excludes ops operation hmem
      let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
      let L := schemeModuleIteratedSignedClosedPointTensor O «prefix»
      let eL := schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso U «prefix»
        (fun a ha => schemeSignedPointTensorWordComplementOpen_excludes ops a (hprefix ha)) O (Iso.refl _)
      ∀ (s : SchemeModuleOpenSectionsOver pi L ⊤)
        (t : SchemeModuleOpenSectionsOver pi (schemeModuleSignedClosedPointFactor operation) ⊤),
        (schemeModuleTopSectionsToFunctionFieldLinearMap pi (schemeModuleSignedClosedPointTensor operation L)
            U hgU (schemeModuleSignedClosedPointTensorOverCanonicalIso operation U hPU L eL)
            (schemeModuleSignedClosedPointTensorPureSection operation L s t) : N.functionField) =
          (schemeModuleTopSectionsToFunctionFieldLinearMap pi L U hgU eL s : N.functionField) *
            (schemeModuleTopSectionsToFunctionFieldLinearMap pi (schemeModuleSignedClosedPointFactor operation)
              U hgU (schemeModuleSignedClosedPointFactorOverCanonicalIso operation U hPU) t : N.functionField) := by
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  intro ops «prefix» hprefix operation hmem s t
  exact schemeModuleSignedPointTensorWord_prefixStep_fieldPureSection pi ops
    (fun a _ => projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq a.1)
    «prefix» hprefix operation hmem s t

end PfaffianDescent.Coray
