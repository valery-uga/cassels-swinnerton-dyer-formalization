import PfaffianDescent.SchemeModuleQuasicoherentClosedSupportH1Vanishing
import PfaffianDescent.CorayNormalizationNonzeroSignedWordCokernelFiniteSupport
import PfaffianDescent.CorayNormalizationNonzeroSignedWordCokernelFinitePresentation
import PfaffianDescent.CorayFiniteSchemeGenericNormalization
import AllCharacteristics.ProjectiveCommonAffineNeighborhood

/-! Actual H1(Q_s)=0 on the SAME original normalization for a GIVEN
nonzero literal signed-word section. The finite image of Q_s's OWN
support has a common affine neighborhood downstairs; finite normalization
pulls this back to an affine neighborhood of Q_s's OWN support upstairs.
SOURCE ONLY / UNVERIFIED. No section existence is asserted. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual section cokernel has zero intrinsic H1, from its own QC
and finite closed support. No normalization-defect quotient is substituted. -/
theorem projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_cohomology_one_subsingleton
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    ∀ ops : List (closedPoints N × Bool),
      let W := schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops
      ∀ s : W.val.obj (op ⊤), s ≠ 0 →
        Subsingleton (schemeModuleCohomology N (cokernel (schemeModuleTopSectionHom W s)) 1) := by
  classical
  intro I X N
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  letI : IsFinite nu := integralScheme_genericNormalization_isFinite X (toBase I)
  letI : IsLocallyNoetherian N := integralGenericNormalization_isLocallyNoetherian X (toBase I)
  intro ops W s hs
  let Q := (show N.Modules from cokernel (schemeModuleTopSectionHom W s))
  let C := schemeModuleStalkSupport Q
  letI : Q.IsQuasicoherent :=
    (projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_finitePresentation_quasicoherent_genericZero
      p q hp hp0 n hn hq hnot ops s hs).2.1
  obtain ⟨hclosed, hfinite, _hpoints⟩ :=
    projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_stalkSupport_finite_closed
      p q hp hp0 n hn hq hnot ops s hs
  have hImage : (nu '' C).Finite := hfinite.image nu
  obtain ⟨U, hU⟩ := AllCharacteristics.exists_affineOpen_containing_projective_finset
    (grading I) hImage.toFinset
  let V : N.Opens := nu ⁻¹ᵁ U.1
  have hV : IsAffineOpen V := U.2.preimage nu
  have hCV : C ⊆ V := by
    intro x hx
    exact hU (nu x) (hImage.mem_toFinset.mpr ⟨x, hx, rfl⟩)
  exact schemeModule_quasicoherent_cohomology_one_subsingleton_of_closedSupport_subset_affine
    pi Q hclosed V hV hCV

end PfaffianDescent.Coray
