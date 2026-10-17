import PfaffianDescent.CorayNormalizationNonzeroSignedWordCokernelCycleDegree
import PfaffianDescent.CorayNormalizationSignedPointTensorSharpSection

/-! Actual nonzero section and its OWN native-length cycle from the accepted
Euler windows. No section or degree certificate is an input. The original
K, literal signed word, own cokernel, own finite support, native lengths and
full pi residue degrees remain unchanged. These are actual-word consumers;
operation selection from original cycles is separate. SOURCE ONLY /
UNVERIFIED; the L7 degree leaf in this packet is the sole new prerequisite. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The sharp actual Euler window constructs a nonzero section AND its
own literal native-length cycle of exactly the full original-K word weight.
The normalization quotient occurs only in the positivity window; the
constructed cycle uses the different, actual section cokernel Q_s. -/
theorem projectiveIntersection_genericNormalization_signedPointTensorIteration_exists_nonzeroSection_and_ownLengthCycle_of_weight_add_quotient_ge_bound
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    ∀ ops : List (closedPoints N × Bool),
      let W := schemeModuleIteratedSignedClosedPointTensor
        (SheafOfModules.unit N.ringCatSheaf) ops
      ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ) ≤
          schemeModuleSignedClosedPointTensorWeightSum pi ops +
            (Module.finrank K (SchemeModuleGlobalSectionsOver (toBase I)
              (genericNormalizationQuotientSheaf X)) : ℤ) →
        ∃ s : W.val.obj (op ⊤), s ≠ 0 ∧
          let Q := cokernel (schemeModuleTopSectionHom W s)
          let C := schemeModuleStalkSupport Q
          ∃ (hC : C.Finite) (hpoints : ∀ x ∈ C, IsClosed ({x} : Set N)),
            (EffectiveZeroCycle.degree pi
              (schemeModuleFiniteClosedSupportLengthCycle Q C hC hpoints) : ℤ) =
                schemeModuleSignedClosedPointTensorWeightSum pi ops := by
  classical
  intro I X N nu pi ops W hwindow
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  obtain ⟨s, hs⟩ :=
    projectiveIntersection_genericNormalization_signedPointTensorIteration_exists_nonzero_topSection_of_weight_add_quotient_ge_bound
      p q hp hp0 n hn hq hnot ops hwindow
  exact ⟨s, hs,
    projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_lengthCycle_degree_eq_weight
      p q hp hp0 n hn hq hnot ops s hs⟩

/-- The conservative weight window constructs the same actual section and
own length cycle; neither existence nor its degree is assumed. -/
theorem projectiveIntersection_genericNormalization_signedPointTensorIteration_exists_nonzeroSection_and_ownLengthCycle_of_weight_ge_bound
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    ∀ ops : List (closedPoints N × Bool),
      let W := schemeModuleIteratedSignedClosedPointTensor
        (SheafOfModules.unit N.ringCatSheaf) ops
      ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ) ≤
          schemeModuleSignedClosedPointTensorWeightSum pi ops →
        ∃ s : W.val.obj (op ⊤), s ≠ 0 ∧
          let Q := cokernel (schemeModuleTopSectionHom W s)
          let C := schemeModuleStalkSupport Q
          ∃ (hC : C.Finite) (hpoints : ∀ x ∈ C, IsClosed ({x} : Set N)),
            (EffectiveZeroCycle.degree pi
              (schemeModuleFiniteClosedSupportLengthCycle Q C hC hpoints) : ℤ) =
                schemeModuleSignedClosedPointTensorWeightSum pi ops := by
  classical
  intro I X N nu pi ops W hwindow
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  obtain ⟨s, hs⟩ :=
    projectiveIntersection_genericNormalization_signedPointTensorIteration_exists_nonzero_topSection_of_weight_ge_bound
      p q hp hp0 n hn hq hnot ops hwindow
  exact ⟨s, hs,
    projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_lengthCycle_degree_eq_weight
      p q hp hp0 n hn hq hnot ops s hs⟩

end PfaffianDescent.Coray
