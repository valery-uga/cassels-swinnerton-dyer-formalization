import PfaffianDescent.CorayNormalizationNonzeroSignedWordCokernelCohomologyOneZero
import PfaffianDescent.CorayNormalizationNonzeroSignedWordSection
import PfaffianDescent.CorayNormalizationNonzeroSignedWordCokernelGlobalWeightedLength
import PfaffianDescent.CorayNormalizationFiniteSignedPointTensorIteration
import PfaffianDescent.CorayNormalizationGlobalUnitSectionsFinite
import PfaffianDescent.CorayProjectiveNormalizationIntrinsicH1FiniteCore
import PfaffianDescent.SchemeModuleFinitePointSequenceBalance
import PfaffianDescent.SchemeModuleFiniteClosedSupportLengthCycle

/-! L7: degree of the actual native-length cycle of the SAME section
cokernel equals the literal signed-word weight over the original K.
The actual O_N H0/H1 cancel, with no H0(N)=K assertion. Conditional only
on a GIVEN nonzero actual word section; existence is a separate caller.
SOURCE ONLY / UNVERIFIED. Pending imports are recorded in the manifest. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pure rank cancellation. Actual O_N ranks need not equal 1 or 0. -/
private theorem ownCokernel_rankBalance_and_eulerChange
    (wordH0 baseH0 wordH1 baseH1 cokernelH0 : ℕ) (weight : ℤ)
    (hbalance : wordH0 + baseH1 = baseH0 + cokernelH0 + wordH1)
    (hchange : (wordH0 : ℤ) - (wordH1 : ℤ) =
      (baseH0 : ℤ) - (baseH1 : ℤ) + weight) :
    (cokernelH0 : ℤ) = weight := by
  omega

/-- Actual original-K top-section dimension of Q_s is the signed word's
full original residue-degree weight. The genuine cokernel sequence and
its own supported H1 vanishing give a rank balance; the actual finite
signed iteration gives the other equality. Actual normalization constants
are retained and canceled, rather than identified with K. -/
theorem projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_topSections_finrank_eq_weight
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
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    letI : Linear K N.Modules := schemeModulesLinearOver pi
    ∀ ops : List (closedPoints N × Bool),
      let W := schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops
      ∀ s : W.val.obj (op ⊤), s ≠ 0 →
        (Module.finrank K (SchemeModuleOpenSectionsOver pi
          (cokernel (schemeModuleTopSectionHom W s)) ⊤) : ℤ) =
            schemeModuleSignedClosedPointTensorWeightSum pi ops := by
  classical
  intro I X N nu pi
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  let O := (show N.Modules from SheafOfModules.unit N.ringCatSheaf)
  intro ops W s hs
  let Q := (show N.Modules from cokernel (schemeModuleTopSectionHom W s))
  let S : ShortComplex N.Modules := ShortComplex.cokernelSequence (schemeModuleTopSectionHom W s)
  have hS : S.ShortExact :=
    (projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_shortExact
      p q hp hp0 n hn hq hnot ops s hs).2
  have h0 : Module.Finite K (SchemeModuleOpenSectionsOver pi O ⊤) :=
    projectiveIntersection_genericNormalization_unit_topSections_finite_native p q hp hp0 n hn hq hnot
  have h1 : Module.Finite K (schemeModuleCohomology N O 1) :=
    projectiveIntersection_genericNormalization_unit_cohomology_one_finite_native p q hp hp0 n hq hnot
  obtain ⟨_hC, _e, _he, hF, _hdim⟩ :=
    projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_topSections_finite_and_weighted_finrank
      p q hp hp0 n hn hq hnot ops s hs
  have hv : Subsingleton (schemeModuleCohomology N Q 1) :=
    projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_cohomology_one_subsingleton
      p q hp hp0 n hn hq hnot ops s hs
  have hbalance := schemeModuleShortExact_finite_second_and_h0_h1_balance pi S hS h0 h1 hF hv
  have hbalanceNat :
      Module.finrank K (SchemeModuleOpenSectionsOver pi W ⊤) +
        Module.finrank K (schemeModuleCohomology N O 1) =
      Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) +
        Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) +
        Module.finrank K (schemeModuleCohomology N W 1) := hbalance.2.2
  have hchange :
      (Module.finrank K (SchemeModuleOpenSectionsOver pi W ⊤) : ℤ) -
        (Module.finrank K (schemeModuleCohomology N W 1) : ℤ) =
      (Module.finrank K (SchemeModuleOpenSectionsOver pi O ⊤) : ℤ) -
        (Module.finrank K (schemeModuleCohomology N O 1) : ℤ) +
        schemeModuleSignedClosedPointTensorWeightSum pi ops :=
    (projectiveIntersection_genericNormalization_signedPointTensorIteration_finite_and_h0_h1_change
      p q hp hp0 n hn hq hnot ops).2.2.2
  exact ownCokernel_rankBalance_and_eulerChange _ _ _ _ _ _ hbalanceNat hchange

/-- The actual effective zero cycle uses native module lengths at the
actual closed support of Q_s. Its degree over the original field equals
word weight. In particular, no extension to a constants field drops any
residue-degree factor. This gives the promised cycle only for a GIVEN
nonzero section, and makes no degree-reduction existence claim. -/
theorem projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_lengthCycle_degree_eq_weight
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
      let W := schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops
      ∀ s : W.val.obj (op ⊤), s ≠ 0 →
        let Q := cokernel (schemeModuleTopSectionHom W s)
        let C := schemeModuleStalkSupport Q
        ∃ (hC : C.Finite) (hpoints : ∀ x ∈ C, IsClosed ({x} : Set N)),
          (EffectiveZeroCycle.degree pi
            (schemeModuleFiniteClosedSupportLengthCycle Q C hC hpoints) : ℤ) =
              schemeModuleSignedClosedPointTensorWeightSum pi ops := by
  classical
  intro I X N nu pi
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  intro ops W s hs Q C
  obtain ⟨hC, _e, _he, _hF, hdim⟩ :=
    projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_topSections_finite_and_weighted_finrank
      p q hp hp0 n hn hq hnot ops s hs
  obtain ⟨_hclosed, _hfinite, hpoints⟩ :=
    projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_stalkSupport_finite_closed
      p q hp hp0 n hn hq hnot ops s hs
  refine ⟨hC, hpoints, ?_⟩
  letI : Fintype C := hC.fintype
  have hdegree : EffectiveZeroCycle.degree pi
      (schemeModuleFiniteClosedSupportLengthCycle Q C hC hpoints) =
      Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) :=
    (schemeModuleFiniteClosedSupportLengthCycle_degree pi Q C hC hpoints).trans hdim.symm
  rw [hdegree]
  exact projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_topSections_finrank_eq_weight
    p q hp hp0 n hn hq hnot ops s hs

end PfaffianDescent.Coray
