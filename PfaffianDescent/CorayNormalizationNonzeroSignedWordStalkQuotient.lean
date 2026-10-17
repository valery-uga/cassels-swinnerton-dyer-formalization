import PfaffianDescent.SchemeModuleUnitHomStalkPrincipalQuotient
import PfaffianDescent.SchemeModuleLocalIsoCoordinate
import PfaffianDescent.CorayNormalizationNonzeroSignedWordSection
import PfaffianDescent.CorayProjectiveNormalizationStalkDimension

/-! Actual native frames and local quotient lengths for the SAME given
nonzero signed-word section on the literal p/q normalization. Frames,
monicity and closed-point DVR are derived from original geometry. Native
R-linear actions and the original cokernel projection are retained.
This does not construct a nonzero section or assert a weighted cycle degree.
SOURCE ONLY / UNVERIFIED: root alone compiles. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine native stalk frame from an actual unit neighborhood. The
over-site chart is transported to restriction via the installed equivalence,
then the existing ambient-stalk comparison retains the SAME local-ring action. -/
theorem schemeModuleLocallyRankOne_nativeStalkFrame
    {X : Scheme.{u}} (M : X.Modules) (hM : schemeModuleLocallyRankOne M) (x : X) :
    Nonempty ((schemeModuleStalkModuleFunctor X x).obj M ≅
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) := by
  classical
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hM x
  let O := (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
  let eR : M.restrict U.ι ≅ O.restrict U.ι :=
    ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
      (Scheme.Modules.overEquiv U).functor.mapIso eU ≪≫
      (Scheme.Modules.overFunctorEquiv U).app O
  exact ⟨schemeModuleLocalStalkModuleIso U ⟨x, hxU⟩ M O eR ≪≫
    schemeModuleUnitStalkIso X x⟩

/-- Ordinary rank-one geometry internally discharges the native-frame
input of the original stalk quotient theorem. Monicity and DVR remain
explicit generic inputs here; the primitive caller below derives them. -/
theorem schemeModuleLocallyRankOne_unitHom_stalkPrincipalQuotientData
    {X : Scheme.{u}} (M : X.Modules) (hM : schemeModuleLocallyRankOne M)
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) [Mono φ] (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    ∃ eW : (schemeModuleStalkModuleFunctor X x).obj M ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
      let a := schemeModuleUnitHomStalkCoefficient M φ x eW
      a ≠ 0 ∧
        (schemeModuleStalkModuleFunctor X x).map (cokernel.π φ) ≫
          (schemeModuleUnitHomStalkCokernelIsoPrincipalQuotient M φ x eW).hom =
            eW.hom ≫ ModuleCat.ofHom (Algebra.linearMap (X.presheaf.stalk x)
              ((X.presheaf.stalk x) ⧸ Ideal.span ({a} : Set (X.presheaf.stalk x)))) ∧
        Module.length (X.presheaf.stalk x)
          ((schemeModuleStalkModuleFunctor X x).obj (cokernel φ)) =
            IsDiscreteValuationRing.addVal (X.presheaf.stalk x) a ∧
        IsFiniteLength (X.presheaf.stalk x)
          ((schemeModuleStalkModuleFunctor X x).obj (cokernel φ)) := by
  obtain ⟨eW⟩ := schemeModuleLocallyRankOne_nativeStalkFrame M hM x
  exact ⟨eW, schemeModuleUnitHomStalkCoefficient_ne_zero_of_mono M φ x eW,
    schemeModuleUnitHomStalkCokernelIsoPrincipalQuotient_π M φ x eW,
    schemeModuleUnitHomStalkCokernel_length M φ x eW,
    schemeModuleUnitHomStalkCokernel_isFiniteLength M φ x eW⟩

namespace Coray
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Primitive native closed-point quotient/length for the SAME GIVEN
nonzero signed-word section. Original point-ideal charts imply word rank
one; the actual nonzero-section theorem gives Mono; actual normalization
geometry gives nongenericity and DVR. No frame, Mono, DVR, quotient,
finite-support or length conclusion is assumed in these primitive inputs. -/
theorem projectiveIntersection_genericNormalization_nonzeroSignedWordSection_stalkPrincipalQuotient
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ ops : List (closedPoints N × Bool),
      let W := schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops
      ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → ∀ P : closedPoints N,
        let R := N.presheaf.stalk P.1
        letI : IsDiscreteValuationRing R :=
          projectiveIntersection_genericNormalization_nongeneric_stalk_isDVR p q hp hp0 n hq hnot P.1
            (projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq P)
        let F := schemeModuleStalkModuleFunctor N P.1
        let φ := schemeModuleTopSectionHom W s
        ∃ eW : F.obj W ≅ ModuleCat.of R R,
          let a := schemeModuleUnitHomStalkCoefficient W φ P.1 eW
          a ≠ 0 ∧
            F.map (cokernel.π φ) ≫
              (schemeModuleUnitHomStalkCokernelIsoPrincipalQuotient W φ P.1 eW).hom =
                eW.hom ≫ ModuleCat.ofHom (Algebra.linearMap R (R ⧸ Ideal.span ({a} : Set R))) ∧
            Module.length R (F.obj (cokernel φ)) = IsDiscreteValuationRing.addVal R a ∧
            IsFiniteLength R (F.obj (cokernel φ)) := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  intro ops
  let O := (show N.Modules from SheafOfModules.unit N.ringCatSheaf)
  let W := schemeModuleIteratedSignedClosedPointTensor O ops
  have hM : ∀ Q : closedPoints N,
      let i := N.fromSpecResidueField Q.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp Q.2
      schemeModuleLocallyRankOne (closedImmersionModule i) := by
    intro Q
    dsimp only
    let i := N.fromSpecResidueField Q.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp Q.2
    let M := (show N.Modules from closedImmersionModule i)
    intro x
    obtain ⟨U, hxU, m, hm, _hregular, _hprincipal⟩ :=
      projectiveIntersection_genericNormalization_closedPoint_ideal_rankOne_chart
        p q hp hp0 n hn hq hnot Q x
    letI := hm
    let e : SheafOfModules.unit (U.1 : Scheme).ringCatSheaf ≅ M.restrict U.1.ι :=
      asIso (schemeModuleSectionOnOpenHom M U.1 m)
    exact ⟨U.1, hxU, ⟨ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit U.1 e.symm ≪≫
      (SchemeModuleInternalHom.unitOverIso U.1).symm⟩⟩
  have hO : schemeModuleLocallyRankOne O := fun x => ⟨⊤, by simp, ⟨Iso.refl _⟩⟩
  have hW : schemeModuleLocallyRankOne W :=
    schemeModuleIteratedSignedClosedPointTensor_locallyRankOne ops O hM hO
  intro s hs P
  let φ := schemeModuleTopSectionHom W s
  letI : Mono φ :=
    (projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_shortExact
      p q hp hp0 n hn hq hnot ops s hs).1
  letI : IsDomain (N.presheaf.stalk P.1) := by infer_instance
  letI : IsDiscreteValuationRing (N.presheaf.stalk P.1) :=
    projectiveIntersection_genericNormalization_nongeneric_stalk_isDVR p q hp hp0 n hq hnot P.1
      (projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq P)
  exact schemeModuleLocallyRankOne_unitHom_stalkPrincipalQuotientData W hW φ P.1

end Coray
end PfaffianDescent
