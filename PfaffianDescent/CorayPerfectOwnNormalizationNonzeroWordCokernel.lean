import PfaffianDescent.CorayPerfectOwnNormalizationPointIdealRankOne
import PfaffianDescent.SchemeModuleCanonicalSignedPointTensorWord
import PfaffianDescent.SchemeModuleNonzeroTopSectionGenericStalk
import PfaffianDescent.CorayRankOneSectionCokernelClosedSupport
import PfaffianDescent.CorayIntegralCurveClosedSupportFinite
import PfaffianDescent.CorayNormalizationSignedPointTensorWordClosedPointReconstruction
import PfaffianDescent.CorayOwnPositiveCoordinateCokernelHZero
import PfaffianDescent.SchemeModuleFiniteClosedSupportLengthCycle

/-! SOURCE ONLY / UNVERIFIED. Actual GIVEN nonzero signed-word section on the
SAME OWN minimal component's canonical normalization over ORIGINAL perfect K.
Its SAME monic section map/cokernel, actual finite closed support, native finite
stalk lengths, original-K finite H0 and actual effective native-length cycle
are constructed internally. No H1/Euler/genus/duality or section existence input;
no signed-weight equality or degree-reduction conclusion is claimed. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- OWN ideal charts and the canonical signed-word complement frame detect the
SAME given nonzero section in the actual function field. The actual section map
is monic and its SAME cokernel is zero at the actual native generic stalk. -/
theorem perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_mono_and_genericZero
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
        schemeModuleLocallyRankOne W ∧ Mono (schemeModuleTopSectionHom W s) ∧
          (ShortComplex.cokernelSequence (schemeModuleTopSectionHom W s)).ShortExact ∧
          Subsingleton ((Scheme.Modules.presheaf (X := N)
            (show N.Modules from cokernel (schemeModuleTopSectionHom W s))).stalk (genericPoint N)) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase C
  let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
  change ∀ ops : List (closedPoints N × Bool),
    let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
    ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro ops
  let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
  have hM : ∀ Q : closedPoints N,
      let i := N.fromSpecResidueField Q.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp Q.2
      schemeModuleLocallyRankOne (closedImmersionModule i) :=
    fun Q => perfectField_selectedProjectiveMinimalComponent_genericNormalization_closedPoint_ideal_locallyRankOne
      p q hp hp0 n hq hnot C hmin P Q
  have hO : schemeModuleLocallyRankOne O := fun x => ⟨⊤, by simp, ⟨Iso.refl _⟩⟩
  have hW : schemeModuleLocallyRankOne W :=
    schemeModuleIteratedSignedClosedPointTensor_locallyRankOne ops O hM hO
  let hP : ∀ operation ∈ ops, operation.1.1 ≠ genericPoint N :=
    fun operation _ => selectedProjectiveMinimalComponent_genericNormalization_closedPoint_ne_generic
      p q hp hp0 n hq hnot C hmin P operation.1
  let U := schemeSignedPointTensorWordComplementOpen ops
  have hgU : genericPoint N ∈ U := schemeSignedPointTensorWordComplementOpen_generic_mem ops hP
  let eW := schemeModuleIteratedSignedClosedPointTensorOverCanonicalIso U ops
    (schemeSignedPointTensorWordComplementOpen_excludes ops) O (Iso.refl _)
  change ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro s hs
  have hm := schemeModuleTopSectionHom_mono_and_cokernelSequence_shortExact pi W hW U hgU eW s hs
  have hz := schemeModuleTopSectionHom_cokernel_genericStalk_isZero pi W hW U hgU eW s hs
  exact ⟨hW, hm.1, hm.2, ModuleCat.subsingleton_of_isZero hz⟩

/-- The actual SAME section cokernel on the OWN normalization has finite CLOSED
support consisting of actual closed points. No support/dimension/cokernel-zero
certificate is supplied; own normalization geometry discharges them internally. -/
theorem perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_cokernel_finiteClosedSupport
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
        IsClosed (schemeModuleStalkSupport Q) ∧ (schemeModuleStalkSupport Q).Finite ∧
          ∀ x ∈ schemeModuleStalkSupport Q, IsClosed ({x} : Set N) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (toBase C)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  letI : IsLocallyNoetherian N := perfectField_integralGenericNormalization_isLocallyNoetherian X (toBase C)
  letI : CompactSpace N := integralGenericNormalization_compactSpace X
  letI : IsNoetherian N := ⟨⟩
  let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
  change ∀ ops : List (closedPoints N × Bool),
    let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
    ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro ops
  let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
  change ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro s hs
  let Q : N.Modules := cokernel (schemeModuleTopSectionHom W s)
  obtain ⟨hW, _hm, _hS, hzero⟩ :=
    perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_mono_and_genericZero
      p q hp hp0 n hq hnot C hmin P ops s hs
  have hclosed : IsClosed (schemeModuleStalkSupport Q) :=
    schemeModuleUnitHom_cokernel_stalkSupport_isClosed W hW (schemeModuleTopSectionHom W s)
  have hg : genericPoint N ∉ schemeModuleStalkSupport Q := by
    change ¬ Nontrivial ((Scheme.Modules.presheaf (X := N) Q).stalk (genericPoint N))
    exact not_nontrivial_iff_subsingleton.mpr hzero
  have hdim : ∀ x : N, Ring.DimensionLEOne (N.presheaf.stalk x) :=
    selectedProjectivePrimeComponent_genericNormalization_stalk_dimensionLEOne
      p q hp hp0 n hq hnot C hmin.le hmin.isPrime P
  exact ⟨hclosed, integralCurve_closed_avoiding_generic_finite_and_closedPoints
    N hdim (schemeModuleStalkSupport Q) hclosed hg⟩

/-- The SAME actual cokernel has native finite lengths at all its support
points and finite ORIGINAL-K H0. Its actual effective native-length cycle has
degree equal to those actual original-K sections, retaining every residue
factor. No Euler premise or signed-weight numerical degree is supplied. -/
theorem perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_cokernel_finiteHZero_and_lengthCycle
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
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase C
    let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
    ∀ ops : List (closedPoints N × Bool),
      let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
      ∀ (s : W.val.obj (op ⊤)), s ≠ 0 →
        let Q : N.Modules := cokernel (schemeModuleTopSectionHom W s)
        let S := schemeModuleStalkSupport Q
        ∃ (hS : S.Finite) (hpoints : ∀ x ∈ S, IsClosed ({x} : Set N)),
          (∀ x : S, IsFiniteLength (N.presheaf.stalk x.1)
            ((schemeModuleStalkModuleFunctor N x.1).obj Q)) ∧
          Module.Finite K (SchemeModuleOpenSectionsOver pi Q ⊤) ∧
          EffectiveZeroCycle.degree pi (schemeModuleFiniteClosedSupportLengthCycle Q S hS hpoints) =
            Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hmin.isPrime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase C
  letI : IsFinite nu := perfectField_integralScheme_genericNormalization_isFinite X (toBase C)
  letI : LocallyOfFiniteType pi := inferInstance
  letI : IsLocallyNoetherian N := perfectField_integralGenericNormalization_isLocallyNoetherian X (toBase C)
  let O : N.Modules := SheafOfModules.unit N.ringCatSheaf
  change ∀ ops : List (closedPoints N × Bool),
    let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
    ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro ops
  let W : N.Modules := schemeModuleIteratedSignedClosedPointTensor O ops
  change ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → _
  intro s hs
  let phi : O ⟶ W := schemeModuleTopSectionHom W s
  let Q : N.Modules := cokernel phi
  let S := schemeModuleStalkSupport Q
  obtain ⟨hW, hm, _hshort, _hzero⟩ :=
    perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_mono_and_genericZero
      p q hp hp0 n hq hnot C hmin P ops s hs
  letI : Mono phi := hm
  have hO : schemeModuleLocallyRankOne O := fun x => ⟨⊤, by simp, ⟨Iso.refl _⟩⟩
  obtain ⟨_hclosed, hfinite, hpoints⟩ :=
    perfectField_selectedProjectiveMinimalComponent_normalization_nonzeroWordSection_cokernel_finiteClosedSupport
      p q hp hp0 n hq hnot C hmin P ops s hs
  have hlength (x : S) : IsFiniteLength (N.presheaf.stalk x.1)
      ((schemeModuleStalkModuleFunctor N x.1).obj Q) := by
    letI : Ring.DimensionLEOne (N.presheaf.stalk x.1) :=
      selectedProjectivePrimeComponent_genericNormalization_stalk_dimensionLEOne
        p q hp hp0 n hq hnot C hmin.le hmin.isPrime P x.1
    exact rankOneMono_actualStalkCokernel_isFiniteLength O W hO hW phi x.1
  have hfiniteHZero := (schemeModuleOriginalBaseTopSections_finite_and_weighted_finrank
    pi Q S hfinite hpoints Set.Subset.rfl hlength).1
  exact ⟨hfinite, hpoints, hlength, hfiniteHZero,
    schemeModuleFiniteClosedSupportLengthCycle_degree_eq_topSections_finrank
      pi Q S hfinite hpoints Set.Subset.rfl hlength⟩

end PfaffianDescent.Coray
