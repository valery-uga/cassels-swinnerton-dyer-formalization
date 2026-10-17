import PfaffianDescent.CorayNormalizationSignedPointTensorEulerPositivity

/-! Actual section existence from the sharper original-K Euler window.
The given operations build the SAME actual signed word. Its full residue
weight and the SAME actual normalization quotient defect suffice; no
nonzero section, rank-one constant field, genus or RR identity is input.
SOURCE ONLY / UNVERIFIED. Positivity001 and actual finite iteration remain
root-owned prerequisites; this module constructs no normalization cycles. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The sharper window DERIVES a nonzero section of the actual signed
tensor word, retaining the full actual quotient contribution. In particular
the boundary choice w = d-3 or d-2 may use its actual defect gain instead
of incorrectly requiring w >= B(n). Operations and their window remain
explicit; no word construction from original surface data is asserted. -/
theorem projectiveIntersection_genericNormalization_signedPointTensorIteration_exists_nonzero_topSection_of_weight_add_quotient_ge_bound
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    let piX := toBase I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ piX
    ∀ ops : List (closedPoints N × Bool),
      let T := schemeModuleIteratedSignedClosedPointTensor
        (SheafOfModules.unit N.ringCatSheaf) ops
      ((1 + 3 * n * (n - 1) / 2 : ℕ) : ℤ) ≤
          schemeModuleSignedClosedPointTensorWeightSum pi ops +
          (Module.finrank K (SchemeModuleGlobalSectionsOver piX
            (genericNormalizationQuotientSheaf X)) : ℤ) →
        ∃ s : SchemeModuleOpenSectionsOver pi T ⊤, s ≠ 0 := by
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let piX := toBase I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ piX
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K N.Modules := schemeModulesLinearOver pi
  intro ops hw
  have h :=
    projectiveIntersection_genericNormalization_signedPointTensorIteration_euler_and_h0_pos_of_weight_add_quotient_ge_bound
      p q hp hp0 n hn hq hnot ops hw
  letI := Module.nontrivial_of_finrank_pos h.2
  exact exists_ne 0

end PfaffianDescent.Coray
