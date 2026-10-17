import PfaffianDescent.CorayCartierIntrinsicNormalHomSequence
import PfaffianDescent.CoraySelectedComponentCubicResidueTrace
import PfaffianDescent.CoraySelectedComponentActualConormalNormalModules

/-! The native adjunction candidate on the SAME selected minimal component
of the ORIGINAL smooth cubic, with a genuine Hom resolution and original
ambient quotient maps. This does not prove dualizing universal properties,
Serre perfectness, genus or normalization H1. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Original smooth-cubic geometry constructs the native candidate
i^*O_S(-1) tensor dual(actualConormal i), its actual rank-one neighborhoods,
and its literal Hom/cokernel/pushforward resolution on the SAME selected C.
No smoothness or geometric integrality of C is assumed. -/
theorem selectedProjectiveMinimalComponent_actualCubicHomResolutionData
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    let hCp : p ∈ C.toIdeal := hCmin.le (by
      rw [projectiveIntersectionIdeal_toIdeal]
      exact Ideal.subset_span (Set.mem_insert p {q}))
    let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
    letI : IsClosedImmersion i :=
      PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
    let H := selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
      p q hp hp0 n hq hnot C hCmin
    let W := sheafOfModules (grading (equationIdeal p hp)) 1
    let hW := cubicIntrinsicNegativeOne_locallyRankOne p hp
    let D := schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
      (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i))
    let S := H.actualCartierIntrinsicNormalHomSequence W hW
    schemeModuleLocallyRankOne D ∧ S.ShortExact ∧
      S.g =
        (SchemeModuleInternalHom.rankOneTensorHomIso
          (IdealSheafDataModule.closedImmersionModule i) W
          H.inverseCartierTwist_locallyRankOne).inv ≫
        (H.actualCartierResidueSequence W).g ≫
        ((H.actualCartierResidueProjectionIso W hW).hom ≫
          (Scheme.Modules.pushforward i).map
            (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap i W
              (SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i))) ≫
          (Scheme.Modules.pushforward i).map
            (schemeModuleTensorMap (𝟙 ((Scheme.Modules.pullback i).obj W))
              (schemeModulePullbackIntrinsicDualIsoOfLocallyRankOne i
                (IdealSheafDataModule.closedImmersionModule i)
                H.inverseCartierTwist_locallyRankOne).hom)) := by
  let hCp : p ∈ C.toIdeal := hCmin.le (by
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q}))
  let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
  letI : IsClosedImmersion i :=
    PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
  let H := selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
    p q hp hp0 n hq hnot C hCmin
  let W := sheafOfModules (grading (equationIdeal p hp)) 1
  let hW : schemeModuleLocallyRankOne W := cubicIntrinsicNegativeOne_locallyRankOne p hp
  let D := schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
    (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i))
  let S := H.actualCartierIntrinsicNormalHomSequence W hW
  have hD : schemeModuleLocallyRankOne D :=
    schemeModuleLocallyRankOne_tensor _ _
      (schemeModuleLocallyRankOne_pullback i W hW) H.actualNormal_locallyRankOne
  refine ⟨hD, H.actualCartierIntrinsicNormalHomSequence_shortExact W hW, ?_⟩
  let eH := SchemeModuleInternalHom.rankOneTensorHomIso
    (IdealSheafDataModule.closedImmersionModule i) W H.inverseCartierTwist_locallyRankOne
  have hp := H.actualCartierHomCokernelIntrinsicNormalIso_projection W hW
  have hn := H.actualCartierResidueIntrinsicNormalTensorIso_hom W hW
  exact hp.trans (congrArg (fun a => eH.inv ≫ (H.actualCartierResidueSequence W).g ≫ a) hn)

end PfaffianDescent.Coray
end
