import PfaffianDescent.SchemeModuleFixedFrameClosedPointSectionReconstruction
import PfaffianDescent.SchemeModuleCanonicalSignedPointTensorWord
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! Actual normalization compactness and closed-point reconstruction of
SAME original-pi signed-word global sections. Compactness, nongenericity
and rank-one geometry are derived internally for the primitive curve.
No finite-normalization, cover, classification, image or RR certificate.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME canonical generic normalization of a compact integral
scheme is compact. The actual normalization morphism is internally
integral, hence affine and quasi-compact. Finiteness, finite type,
Noetherianity, Jacobsonity and characteristic zero are not inputs. -/
theorem integralGenericNormalization_compactSpace
    (X : Scheme.{u}) [IsIntegral X] [CompactSpace X] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    CompactSpace (X.fromSpecStalk (genericPoint X)).normalization := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : IsIntegralHom nu := inferInstance
  letI : IsAffineHom nu := inferInstance
  letI : QuasiCompact nu := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace nu

variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem locallyRankOne_of_actualAffineCharts
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

/-- Primitive original-K positive-degree integral p/q normalization:
EVERY actual signed word's ORIGINAL global field image is precisely the
intersection of its SAME original closed-point stalk images. Actual
normalization compactness, selected-point nongenericity and all word
rank-one geometry are internally constructed; no cover, classification,
finite-dimensionality, valuation, desired image or reconstruction premise. -/
theorem projectiveIntersection_genericNormalization_signedPointTensorWord_globalRange_iff_closedPointStalkRange
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
      let C := schemeSignedPointTensorWordComplementOpen ops
      letI : Nonempty C := ⟨⟨genericPoint N,
        schemeSignedPointTensorWordComplementOpen_generic_mem ops hP⟩⟩
      let O := (show N.Modules from SheafOfModules.unit N.ringCatSheaf)
      let W := schemeModuleIteratedSignedClosedPointTensor O ops
      ∀ f : N.functionField,
        f ∈ Set.range (schemeModuleSignedPointTensorWordToFunctionFieldLinearMap pi ops hP) ↔
          ∀ P : closedPoints N,
            letI := schemeModuleStalkModule W P.1
            f ∈ Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi W C
              (schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso C ops
                (schemeSignedPointTensorWordComplementOpen_excludes ops) O (Iso.refl _)) P.1) := by
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (toBase I)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  letI : CompactSpace N := integralGenericNormalization_compactSpace X
  have hM : ∀ Q : closedPoints N,
      let i := N.fromSpecResidueField Q.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp Q.2
      schemeModuleLocallyRankOne (closedImmersionModule i) := by
    intro Q
    dsimp only
    let i := N.fromSpecResidueField Q.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp Q.2
    let M := (show N.Modules from closedImmersionModule i)
    apply locallyRankOne_of_actualAffineCharts M
    intro x
    obtain ⟨U, hxU, m, hm, _hreg, _hprincipal⟩ :=
      projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
        p q hp hp0 n hn hq hnot Q x
    exact ⟨U, hxU, m, hm⟩
  intro ops f
  let hP : ∀ operation ∈ ops, operation.1.1 ≠ genericPoint N :=
    fun operation _ => projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq operation.1
  let C := schemeSignedPointTensorWordComplementOpen ops
  let hgC := schemeSignedPointTensorWordComplementOpen_generic_mem ops hP
  letI : Nonempty C := ⟨⟨genericPoint N, hgC⟩⟩
  let O := (show N.Modules from SheafOfModules.unit N.ringCatSheaf)
  let W := schemeModuleIteratedSignedClosedPointTensor O ops
  let eW := schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso C ops
    (schemeSignedPointTensorWordComplementOpen_excludes ops) O (Iso.refl _)
  have hO : schemeModuleLocallyRankOne O := fun x => ⟨⊤, by simp, ⟨Iso.refl _⟩⟩
  exact schemeModuleTopSectionsToFunctionFieldLinearMap_mem_range_iff_closedPointStalkRange pi W
    (schemeModuleIteratedSignedClosedPointTensor_locallyRankOne ops O hM hO) C hgC eW f

end PfaffianDescent.Coray
