import PfaffianDescent.CorayPerfectOwnNormalizationNonzeroWordCokernel
import PfaffianDescent.SchemeModuleQuasicoherentClosedSupportH1Vanishing
import PfaffianDescent.SchemeModuleUnitHomCokernelFinitePresentation
import AllCharacteristics.ProjectiveCommonAffineNeighborhood

/-! SOURCE ONLY / UNVERIFIED. H1 of the SAME actual nonzero-word section
cokernel vanishes on the SAME OWN minimal component's normalization over
ORIGINAL perfect K. Actual finite normalization and actual finite support
construct a common affine neighborhood. No H1/Euler/genus, quasicoherence,
support or affine-neighborhood premise is supplied. No section existence. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Abstract finite-map geometry only; no native cohomology carrier occurs. -/
private theorem projectiveFiniteMap_finiteSet_affineNeighborhood
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    {N : Scheme.{u}} (nu : N ⟶ scheme C) [hnu : AlgebraicGeometry.IsFinite nu]
    (S : Set N) (hfinite : S.Finite) :
    ∃ V : N.affineOpens, S ⊆ V.1 := by
  classical
  letI : AlgebraicGeometry.IsAffineHom nu := hnu.toIsAffineHom
  have hImage : (nu '' S).Finite := hfinite.image nu
  obtain ⟨U, hU⟩ := AllCharacteristics.exists_affineOpen_containing_projective_finset
    (grading C) hImage.toFinset
  let V : N.Opens := nu ⁻¹ᵁ U.1
  have hV : IsAffineOpen V :=
    @AlgebraicGeometry.IsAffineOpen.preimage N (scheme C) U.1 U.2 nu hnu.toIsAffineHom
  refine ⟨⟨V, hV⟩, ?_⟩
  intro x hx
  exact hU (nu x) (hImage.mem_toFinset.mpr ⟨x, hx, rfl⟩)

/-- OWN actual word cokernel QC only, independent of finite-map geometry. -/
private theorem ownNonzeroWordCokernel_quasicoherent
    {K : Type u} [Field K] [PerfectField K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
    ∀ ops : List (closedPoints N × Bool),
      let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
      ∀ (s : W.val.obj (op ⊤)), s ≠ 0 →
        let Q : N.Modules := cokernel (schemeModuleTopSectionHom W s)
        Q.IsQuasicoherent := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
  change ∀ ops : List (closedPoints N × Bool),
    let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
    ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro ops
  let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
  change ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro s hs
  have hW : schemeModuleLocallyRankOne W :=
    (perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_mono_and_genericZero
      p q hp hp0 n hq hnot C hmin P ops s hs).1
  exact (schemeModuleTopSectionHom_cokernel_isFinitePresentation_and_isQuasicoherent W hW s).2

/-- OWN actual closed-affine support only; QC and Ext dictionaries are absent. -/
private theorem ownNonzeroWordCokernel_closedAffineSupport
    {K : Type u} [Field K] [PerfectField K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
    ∀ ops : List (closedPoints N × Bool),
      let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
      ∀ (s : W.val.obj (op ⊤)), s ≠ 0 →
        let Q : N.Modules := cokernel (schemeModuleTopSectionHom W s)
        IsClosed (schemeModuleStalkSupport Q) ∧
          ∃ V : N.affineOpens, schemeModuleStalkSupport Q ⊆ V.1 := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : AlgebraicGeometry.IsFinite nu := perfectField_integralScheme_genericNormalization_isFinite X (toBase C)
  let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
  change ∀ ops : List (closedPoints N × Bool),
    let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
    ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro ops
  let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
  change ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro s hs
  let Q : N.Modules := cokernel (schemeModuleTopSectionHom W s)
  obtain ⟨hclosed, hfinite, _hpoints⟩ :=
    perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_cokernel_finiteClosedSupport
      p q hp hp0 n hq hnot C hmin P ops s hs
  exact ⟨hclosed, projectiveFiniteMap_finiteSet_affineNeighborhood C nu
    (schemeModuleStalkSupport Q) hfinite⟩

/-- Abstract native application cut. SAME coefficient and canonical HasExt
are retained, with no normalization or projective telescope in conversion. -/
private theorem nativeModuleHOneZero_of_quasicoherent_closedAffineSupport
    {K : Type u} [Field K] {N : Scheme.{u}} [IsLocallyNoetherian N]
    [HasExt.{u} N.Modules] (pi : N ⟶ Spec (CommRingCat.of K)) (Q : N.Modules)
    (hgeometry : Q.IsQuasicoherent ∧ IsClosed (schemeModuleStalkSupport Q) ∧
      ∃ V : N.affineOpens, schemeModuleStalkSupport Q ⊆ V.1) :
    Subsingleton (schemeModuleCohomology.{u} N Q 1) := by
  obtain ⟨hQC, hclosed, V, hsV⟩ := hgeometry
  letI : Q.IsQuasicoherent := hQC
  exact schemeModule_quasicoherent_cohomology_one_subsingleton_of_closedSupport_subset_affine
    pi Q hclosed V.1 V.2 hsV

/-- The SAME actual section cokernel has zero native intrinsic H1. All
actual quasicoherence and whole closed affine support are derived internally. -/
theorem perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_cokernel_cohomology_one_subsingleton
    {K : Type u} [Field K] [PerfectField K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
    letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
    let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
    ∀ ops : List (closedPoints N × Bool),
      let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
      ∀ (s : W.val.obj (op ⊤)), s ≠ 0 →
        let Q : N.Modules := cokernel (schemeModuleTopSectionHom W s)
        Subsingleton (schemeModuleCohomology.{u} N Q 1) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : IsLocallyNoetherian N := perfectField_integralGenericNormalization_isLocallyNoetherian X (toBase C)
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
  change ∀ ops : List (closedPoints N × Bool),
    let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
    ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro ops
  let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
  change ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro s hs
  let Q : N.Modules := cokernel (schemeModuleTopSectionHom W s)
  exact nativeModuleHOneZero_of_quasicoherent_closedAffineSupport (nu ≫ toBase C) Q
    ⟨ownNonzeroWordCokernel_quasicoherent p q hp hp0 n hq hnot C hmin P ops s hs,
      ownNonzeroWordCokernel_closedAffineSupport p q hp hp0 n hq hnot C hmin P ops s hs⟩

end PfaffianDescent.Coray
