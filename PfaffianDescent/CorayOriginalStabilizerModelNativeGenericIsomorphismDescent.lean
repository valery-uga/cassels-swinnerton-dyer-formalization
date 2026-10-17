import PfaffianDescent.CorayNativeIsomorphismOpenAssembly
import PfaffianDescent.CorayStabilizerModelNativeExclusiveOpenIsomorphism
import PfaffianDescent.CorayActualCurveMultipleComponentLocusFinite
import PfaffianDescent.CorayAlgebraicProjectiveCoefficientFiniteClosedImage
import PfaffianDescent.CorayCoefficientModelOriginalPairInputs
import Mathlib.Topology.JacobsonSpace
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! Source only: actual original-field generic isomorphism of the SAME whole
stabilizer coefficient-model map, with no supplied birationality/finite support. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option autoImplicit false
open AllCharacteristics AllCharacteristics.HomogeneousProjective MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-- For SAME original selected p/q prime I and its WHOLE stabilizer model,
construct a finite closed original-K bad set on whose complement the actual
finite map f is an isomorphism. Neither birationality nor finite support is
supplied. The proof constructs the geometric isomorphism loci, finite bad
locus, closed image and native fpqc descent comparison. -/
theorem selectedOriginalPrime_stabilizerModel_exists_finiteClosedBadSet_restriction_isIso001
    {K L Ω : Type u} [Field K] [CharZero K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [FiniteDimensional K L] [IsGalois K L] [IsAlgClosed Ω] [IsGalois K Ω]
    [Algebra.IsAlgebraic K Ω]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hIrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ I)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (hC : C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes)
    (hCO : (C.toIdeal.map (MvPolynomial.map (algebraMap L Ω))).IsPrime) :
    let M := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
    ∃ hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal,
      let f := coefficientComponentToOriginal I D hID
      ∃ S : Set (scheme I), ∃ hS : IsClosed S,
        S.Finite ∧ (∀ x ∈ S, IsClosed ({x} : Set (scheme I))) ∧
          let U : (scheme I).Opens := ⟨Sᶜ, hS.isOpen_compl⟩
          IsIso (f ∣_ U) := by
  classical
  letI : I.toIdeal.IsPrime := hI.isPrime
  letI : C.toIdeal.IsPrime := hC.isPrime
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
  letI : Module.Finite K M := inferInstance
  letI : Algebra.IsSeparable K M := inferInstance
  let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let g := projectiveCoefficientMap (algebraMap K Ω) I IO rfl
  let iO := projectiveBaseChangeIso (algebraMap K Ω) I IO rfl
  obtain ⟨hID, hOpens⟩ :=
    stabilizerModel_originalBaseChange_exists_componentExclusiveOpen_wholeMap_isIso001
      I hIrel C hC hCO
  dsimp only at hOpens
  let f := coefficientComponentToOriginal I D hID
  let a := pullback.fst (f ≫ toBase I) b
  let F0 := nativeOriginalBaseChangeMap f (toBase I) b
  let F := F0 ≫ iO.inv
  let phi0 : M →ₐ[K] Ω := (IsScalarTower.toAlgHom K L Ω).domRestrict M
  let Q0 := D.map (componentPolynomialCoefficientMap phi0.toRingHom)
  have hQ0 : Q0.toIdeal ∈ IO.toIdeal.minimalPrimes :=
    stabilizerModel_embedding_componentIdeal_minimalPrime I C hC hCO phi0
  obtain ⟨hpO0, hSmooth, hnotO, _⟩ :=
    selectedOriginalMinimalComponent_coefficientMinimalPrime_originalPairInputs001
      p q hp hp0 n hq hnot I hI Q0 hQ0
  letI := hSmooth
  have hMapPQ : (projectiveIntersectionIdeal p q hp hq).toIdeal.map
      (MvPolynomial.map (algebraMap K Ω)) =
        (projectiveIntersectionIdeal (p.map (algebraMap K Ω)) (q.map (algebraMap K Ω))
          (hp.map (algebraMap K Ω)) (hq.map (algebraMap K Ω))).toIdeal := by
    rw [projectiveIntersectionIdeal_toIdeal, projectiveIntersectionIdeal_toIdeal,
      Ideal.map_span]
    simp only [Set.image_insert_eq, Set.image_singleton]
  have hPQIO : (projectiveIntersectionIdeal
      (p.map (algebraMap K Ω)) (q.map (algebraMap K Ω))
      (hp.map (algebraMap K Ω)) (hq.map (algebraMap K Ω))).toIdeal ≤ IO.toIdeal := by
    rw [← hMapPQ]
    exact Ideal.map_mono hI.le
  let eB := homogeneousRelevantMinimalPrimesEquivProjectiveComponents IO
  let DB := fun z : irreducibleComponents (scheme IO) => eB.symm z
  let jB := fun z : irreducibleComponents (scheme IO) =>
    schemeQuotientMap IO (DB z).1 (DB z).2.1.le
  let SB := fun z => jB z ⁻¹' (⋃ w, ⋃ (_ : w ≠ z), Set.range (jB w))
  let Bad := ⋃ z, jB z '' SB z
  have hBadData : IsClosed Bad ∧ Bad.Finite ∧
      ∀ x ∉ Bad, ∃! z : irreducibleComponents (scheme IO), x ∈ z.1 :=
    selectedCubicCurve_actualMultipleComponentLocus_finite001
      (p.map (algebraMap K Ω)) (q.map (algebraMap K Ω))
      (hp.map (algebraMap K Ω)) hpO0 n (hq.map (algebraMap K Ω)) hnotO IO hPQIO
  obtain ⟨c, hc⟩ := stabilizerModel_exists_embedding_projectiveComponentEquiv I hIrel C hC hCO
  have hc' (phi : M →ₐ[K] Ω) : (c phi).1 =
      Set.range (modelEmbeddingComponentToGeometricOriginal I D hID phi) := hc phi
  choose O hO hClosure hNonempty hOI using hOpens
  have hImageData := algebraicField_projectiveCoefficientProjection_integral_finiteClosedImage001 (K := K) (E := Ω) I
  dsimp only at hImageData
  letI : IsIntegralHom g := hImageData.1
  obtain ⟨hImageClosed, hImageFinite, hImageComplement⟩ :=
    hImageData.2 Bad hBadData.1 hBadData.2.1
  let S := g '' Bad
  let U : (scheme I).Opens := ⟨Sᶜ, hImageClosed.isOpen_compl⟩
  let V := g ⁻¹ᵁ U
  have hCover : V ≤ ⨆ phi, O phi := by
    intro x hx
    have hxBad : x ∉ Bad := hImageComplement hx
    obtain ⟨Z, hxZ, hUnique⟩ := hBadData.2.2 x hxBad
    let phi := c.symm Z
    have hZR : Z.1 = Set.range
        (modelEmbeddingComponentToGeometricOriginal I D hID phi) :=
      (congrArg Subtype.val (c.apply_symm_apply Z)).symm.trans (hc' phi)
    have hxO : x ∈ O phi := by
      change x ∈ (↑(O phi) : Set (scheme IO))
      rw [hO phi]
      intro hOther
      obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.mp hOther
      let w : irreducibleComponents (scheme IO) := ⟨W, hW.1⟩
      have hWZ : W = Z.1 := congrArg Subtype.val (hUnique w hxW)
      exact hW.2 (Set.mem_singleton_iff.mpr (hWZ.trans hZR))
    exact Opens.mem_iSup.mpr ⟨phi, hxO⟩
  have hFIso : IsIso (F ∣_ V) :=
    nativeMorphismRestrict_isIso_of_isomorphismOpenCover001 F V O hCover hOI
  have hiFst : iO.hom ≫ pullback.fst (toBase I) b = g :=
    projectiveBaseChangeIso_hom_fst (algebraMap K Ω) I IO rfl
  have hiSnd : iO.hom ≫ pullback.snd (toBase I) b = toBase IO :=
    projectiveBaseChangeIso_hom_snd (algebraMap K Ω) I IO rfl
  have hFfst : F ≫ g = a ≫ f := by
    rw [← hiFst]
    simp only [F, Category.assoc, Iso.inv_hom_id_assoc]
    dsimp only [F0, nativeOriginalBaseChangeMap, a]
    exact pullback.lift_fst _ _ _
  have hFsnd : F ≫ toBase IO = pullback.snd (f ≫ toBase I) b := by
    rw [← hiSnd]
    simp only [F, Category.assoc, Iso.inv_hom_id_assoc]
    dsimp only [F0, nativeOriginalBaseChangeMap]
    exact pullback.lift_snd _ _ _
  have hWide : IsPullback a (F ≫ toBase IO) (f ≫ toBase I) b := by
    rw [hFsnd]
    exact IsPullback.of_hasPullback (f ≫ toBase I) b
  have H : IsPullback a F f g :=
    IsPullback.of_bot hWide hFfst.symm
      (isPullback_projectiveCoefficientMap (algebraMap K Ω) I IO rfl)
  have hPre : F ⁻¹ᵁ V = a ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    change (F ≫ g) ⁻¹ᵁ U = (a ≫ f) ⁻¹ᵁ U
    rw [hFfst]
  have hUY : F ⁻¹ᵁ V = F ⁻¹ᵁ V ⊓ a ⁻¹ᵁ (f ⁻¹ᵁ U) :=
    (inf_eq_left.mpr hPre.le).symm
  have hRes := Scheme.Hom.isPullback_resLE H.flip
    (US := U) (UT := f ⁻¹ᵁ U) (UX := V) le_rfl le_rfl hUY
  dsimp only [V] at hRes
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at hRes
  have hb : Flat b ∧ Surjective b :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap K Ω))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr (inferInstance : Module.FaithfullyFlat K Ω))
  letI : Flat g := MorphismProperty.of_isPullback (P := @Flat.{u})
    (isPullback_projectiveCoefficientMap (algebraMap K Ω) I IO rfl).flip hb.1
  letI : Surjective g := MorphismProperty.of_isPullback (P := @Surjective.{u})
    (isPullback_projectiveCoefficientMap (algebraMap K Ω) I IO rfl).flip hb.2
  letI : QuasiCompact g := inferInstance
  letI : Flat (g ∣_ U) := MorphismProperty.of_isPullback (P := @Flat.{u})
    (isPullback_morphismRestrict g U).flip (inferInstance : Flat g)
  letI : Surjective (g ∣_ U) := MorphismProperty.of_isPullback (P := @Surjective.{u})
    (isPullback_morphismRestrict g U).flip (inferInstance : Surjective g)
  letI : QuasiCompact (g ∣_ U) := MorphismProperty.of_isPullback (P := @QuasiCompact.{u})
    (isPullback_morphismRestrict g U).flip (inferInstance : QuasiCompact g)
  have hRestrictedFpqc :
      (Surjective (g ∣_ U) ∧ Flat (g ∣_ U)) ∧ QuasiCompact (g ∣_ U) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hIso : IsIso (f ∣_ U) :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme.{u})
      (Q := @Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u}) hRes
      hRestrictedFpqc hFIso
  have hSPoints : ∀ x ∈ S, IsClosed ({x} : Set (scheme I)) := by
    letI : JacobsonSpace (scheme I) := LocallyOfFiniteType.jacobsonSpace (toBase I)
    letI : Finite S := hImageFinite.to_subtype
    letI : JacobsonSpace S :=
      JacobsonSpace.of_isClosedEmbedding hImageClosed.isClosedEmbedding_subtypeVal
    letI : DiscreteTopology S := inferInstance
    intro x hx
    let y : S := ⟨x, hx⟩
    have h : IsClosed ((Subtype.val : S → scheme I) '' ({y} : Set S)) :=
      hImageClosed.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_singleton
    simpa only [Set.image_singleton] using h
  exact ⟨hID, S, hImageClosed, hImageFinite, hSPoints, hIso⟩

end PfaffianDescent.Coray
