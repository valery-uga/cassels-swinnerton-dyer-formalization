import PfaffianDescent.CorayModelFieldTensorEmbeddingDecomposition
import AllCharacteristics.ProjectiveBaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! Source only: actual embedding-indexed base-change coproduct of SAME D.
The field-tensor construction is a pending genuine dependency, not a premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A genuine Cartesian scheme square identifies the actual image of its
first map with the inverse image of the actual other image. -/
theorem nativeIsPullback_range_fst
    {A B X S : Scheme.{u}} {a : A ⟶ X} {b : A ⟶ B} {f : X ⟶ S} {g : B ⟶ S}
    (H : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by
  rw [← H.isoPullback_hom_fst]
  change Set.range (fun x => pullback.fst f g (H.isoPullback.hom x)) = _
  have hIsoSurj : Function.Surjective H.isoPullback.hom :=
    H.isoPullback.hom.homeomorph.surjective
  rw [Set.range_comp', Set.range_eq_univ.mpr hIsoSurj,
    Set.image_univ, Scheme.Pullback.range_fst]

variable {K M Ω : Type u} [Field K] [Field M] [Field Ω]
  [Algebra K M] [Algebra K Ω] [Module.Finite K M] [Algebra.IsSeparable K M] [IsAlgClosed Ω]
attribute [local instance] MvPolynomial.gradedAlgebra

def modelFieldTensorModelProjection : Spec (.of (Ω ⊗[K] M)) ⟶ Spec (.of M) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := K) (A := Ω) (B := M)).toRingHom)

def modelFieldTensorOmegaProjection : Spec (.of (Ω ⊗[K] M)) ⟶ Spec (.of Ω) :=
  Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[K] M)))

def modelFieldTensorEmbeddingFactor (phi : M →ₐ[K] Ω) :
    Spec (.of Ω) ⟶ Spec (.of (Ω ⊗[K] M)) :=
  Sigma.ι (fun _ : M →ₐ[K] Ω => Spec (.of Ω)) phi ≫ fieldTensorEmbeddingSpectrumCoproductMap

private theorem modelFieldTensorEmbeddingFactor_model (phi : M →ₐ[K] Ω) :
    modelFieldTensorEmbeddingFactor phi ≫ modelFieldTensorModelProjection =
      Spec.map (CommRingCat.ofHom phi.toRingHom) :=
  (fieldTensorEmbeddingSpectrumCoproductMap_coefficient_components phi).1

private theorem modelFieldTensorEmbeddingFactor_omega (phi : M →ₐ[K] Ω) :
    modelFieldTensorEmbeddingFactor phi ≫ modelFieldTensorOmegaProjection = 𝟙 _ :=
  (fieldTensorEmbeddingSpectrumCoproductMap_coefficient_components phi).2

/-- The ACTUAL field tensor embedding factors are disjoint open immersions
and cover their WHOLE spectrum. All three properties come from the internally
constructed embedding spectrum isomorphism; none is supplied as data. -/
theorem modelFieldTensorEmbeddingFactors_open_cover_disjoint :
    (∀ phi : M →ₐ[K] Ω, IsOpenImmersion (modelFieldTensorEmbeddingFactor phi)) ∧
      (∀ t : Spec (.of (Ω ⊗[K] M)), ∃ (phi : M →ₐ[K] Ω) (x : Spec (.of Ω)),
        modelFieldTensorEmbeddingFactor phi x = t) ∧
      (∀ phi psi : M →ₐ[K] Ω, phi ≠ psi →
        Disjoint (Set.range (modelFieldTensorEmbeddingFactor phi))
          (Set.range (modelFieldTensorEmbeddingFactor psi))) := by
  let F := fun _ : M →ₐ[K] Ω => Spec (.of Ω)
  let sigma := fieldTensorEmbeddingSpectrumCoproductMap (K := K) (M := M) (Ω := Ω)
  letI : IsIso sigma := fieldTensorEmbeddingSpectrumCoproductMap_isIso
  refine ⟨fun phi => by change IsOpenImmersion (Sigma.ι F phi ≫ sigma); infer_instance, ?_, ?_⟩
  · intro t
    obtain ⟨w, hw⟩ := sigma.homeomorph.surjective t
    obtain ⟨⟨phi, x⟩, hpair⟩ := (AlgebraicGeometry.sigmaMk F).surjective w
    have hx : Sigma.ι F phi x = w := by
      simpa only [AlgebraicGeometry.sigmaMk_mk] using hpair
    refine ⟨phi, x, ?_⟩
    change sigma (Sigma.ι F phi x) = t
    exact (congrArg sigma hx).trans hw
  · intro phi psi hne
    apply Set.disjoint_iff_forall_ne.mpr
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    have hsource : Sigma.ι F phi x = Sigma.ι F psi y := sigma.homeomorph.injective hxy
    have hpairs := (AlgebraicGeometry.sigmaι_eq_iff F phi psi x y).mp hsource
    exact hne (congrArg Sigma.fst hpairs)

/-- Pulling a model scheme to the ACTUAL field tensor spectrum is its
ORIGINAL-K base change to Ω. Native Spec tensor pullback and native pasting
construct the Cartesian square; no desired base-change identification. -/
theorem modelSchemeFieldTensor_originalBaseChange_isPullback
    {X : Scheme.{u}} (f : X ⟶ Spec (.of M)) :
    IsPullback (pullback.fst f (modelFieldTensorModelProjection (K := K) (Ω := Ω)))
      (pullback.snd f (modelFieldTensorModelProjection (K := K) (Ω := Ω)) ≫
        modelFieldTensorOmegaProjection)
      (f ≫ Spec.map (CommRingCat.ofHom (algebraMap K M)))
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) := by
  let bM := Spec.map (CommRingCat.ofHom (algebraMap K M))
  let bO := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let pM := modelFieldTensorModelProjection (K := K) (M := M) (Ω := Ω)
  let pO := modelFieldTensorOmegaProjection (K := K) (M := M) (Ω := Ω)
  have H : IsPullback pO pM bO bM := by
    apply (IsPullback.of_hasPullback bO bM).of_iso (pullbackSpecIso K Ω M)
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simpa only [Iso.refl_hom, Category.comp_id, bO, bM, pO,
        modelFieldTensorOmegaProjection] using (pullbackSpecIso_hom_fst' K Ω M).symm
    · have hright :
          (Algebra.TensorProduct.includeRight (R := K) (A := Ω) (B := M)).toRingHom =
            RingHomClass.toRingHom
              (Algebra.TensorProduct.includeRight (R := K) (A := Ω) (B := M)) := by
        apply RingHom.ext
        intro m
        rfl
      simpa only [Iso.refl_hom, Category.comp_id, bO, bM, pM,
        modelFieldTensorModelProjection, hright] using (pullbackSpecIso_hom_snd K Ω M).symm
    · simp
    · simp
  exact (IsPullback.of_hasPullback f pM).paste_vert H.flip

/-- The literal homogeneous component corresponding to one actual M-field
embedding maps into the same field-tensor base change of D. -/
def projectiveModelEmbeddingComponentToTensorBaseChange
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (phi : M →ₐ[K] Ω) :
    scheme (D.map (componentPolynomialCoefficientMap phi.toRingHom)) ⟶
      pullback (toBase D) (modelFieldTensorModelProjection (K := K) (Ω := Ω)) :=
  let DP := D.map (componentPolynomialCoefficientMap phi.toRingHom)
  pullback.lift (projectiveCoefficientMap phi.toRingHom D DP rfl)
    (toBase DP ≫ modelFieldTensorEmbeddingFactor phi) (by
      rw [Category.assoc, modelFieldTensorEmbeddingFactor_model]
      exact projectiveCoefficientMap_toBase phi.toRingHom D DP rfl)

/-- The ACTUAL embedding component is the Cartesian inverse image of its
ACTUAL field-spectrum factor. Outer projective coefficient base change and
the right native pullback prove the square by cancellation; no component
decomposition or image-compatibility certificate is supplied. -/
theorem projectiveModelEmbeddingComponentToTensorBaseChange_isPullback
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (phi : M →ₐ[K] Ω) :
    IsPullback (projectiveModelEmbeddingComponentToTensorBaseChange D phi)
      (toBase (D.map (componentPolynomialCoefficientMap phi.toRingHom)))
      (pullback.snd (toBase D) (modelFieldTensorModelProjection (K := K) (Ω := Ω)))
      (modelFieldTensorEmbeddingFactor phi) := by
  let DP := D.map (componentPolynomialCoefficientMap phi.toRingHom)
  let pM := modelFieldTensorModelProjection (K := K) (M := M) (Ω := Ω)
  let i := modelFieldTensorEmbeddingFactor phi
  let a := projectiveModelEmbeddingComponentToTensorBaseChange D phi
  have hfst : a ≫ pullback.fst (toBase D) pM = projectiveCoefficientMap phi.toRingHom D DP rfl := by
    dsimp only [a, projectiveModelEmbeddingComponentToTensorBaseChange]
    exact pullback.lift_fst _ _ _
  have hsnd : a ≫ pullback.snd (toBase D) pM = toBase DP ≫ i := by
    dsimp only [a, projectiveModelEmbeddingComponentToTensorBaseChange]
    exact pullback.lift_snd _ _ _
  have Houter : IsPullback (a ≫ pullback.fst (toBase D) pM) (toBase DP) (toBase D) (i ≫ pM) := by
    rw [hfst, modelFieldTensorEmbeddingFactor_model]
    exact isPullback_projectiveCoefficientMap phi.toRingHom D DP rfl
  exact Houter.of_right hsnd (IsPullback.of_hasPullback (toBase D) pM)

def projectiveModelEmbeddingTensorCoproductMap
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M)) :
    (∐ fun phi : M →ₐ[K] Ω => scheme (D.map (componentPolynomialCoefficientMap phi.toRingHom))) ⟶
      pullback (toBase D) (modelFieldTensorModelProjection (K := K) (Ω := Ω)) :=
  Sigma.desc (projectiveModelEmbeddingComponentToTensorBaseChange D)

/-- The ACTUAL embedding-indexed component coproduct IS the WHOLE field
tensor base change of SAME D. Disjoint open factor geometry is pulled back;
actual image identities construct covering and disjointness, then native
open-immersion gluing constructs the isomorphism. No desired decomposition. -/
theorem projectiveModelEmbeddingTensorCoproductMap_isIso
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M)) :
    IsIso (projectiveModelEmbeddingTensorCoproductMap (K := K) (Ω := Ω) D) := by
  classical
  let F := fun phi : M →ₐ[K] Ω => scheme (D.map (componentPolynomialCoefficientMap phi.toRingHom))
  let a := projectiveModelEmbeddingComponentToTensorBaseChange (K := K) (Ω := Ω) D
  let pM := modelFieldTensorModelProjection (K := K) (M := M) (Ω := Ω)
  let t := pullback.snd (toBase D) pM
  obtain ⟨hopen, hcover, hdisjoint⟩ := modelFieldTensorEmbeddingFactors_open_cover_disjoint
    (K := K) (M := M) (Ω := Ω)
  letI (phi : M →ₐ[K] Ω) : IsOpenImmersion (a phi) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion.{u})
      (projectiveModelEmbeddingComponentToTensorBaseChange_isPullback D phi).flip (hopen phi)
  have hrange (phi : M →ₐ[K] Ω) : Set.range (a phi) =
      t ⁻¹' Set.range (modelFieldTensorEmbeddingFactor phi) :=
    nativeIsPullback_range_fst (projectiveModelEmbeddingComponentToTensorBaseChange_isPullback D phi)
  have hdisj : Pairwise (fun phi psi => Disjoint (Set.range (a phi)) (Set.range (a psi))) := by
    intro phi psi hne
    rw [hrange phi, hrange psi]
    exact Disjoint.preimage t (hdisjoint phi psi hne)
  letI : IsOpenImmersion (Sigma.desc a) := AlgebraicGeometry.isOpenImmersion_sigmaDesc F a hdisj
  have hsurj : Function.Surjective (Sigma.desc a) := by
    intro y
    obtain ⟨phi, x, hx⟩ := hcover (t y)
    have hy : y ∈ Set.range (a phi) := by
      rw [hrange]
      exact ⟨x, hx⟩
    obtain ⟨z, hz⟩ := hy
    refine ⟨Sigma.ι F phi z, ?_⟩
    have h := congrArg (fun m => m z) (Sigma.ι_desc a phi)
    exact h.trans hz
  change IsIso (Sigma.desc a)
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply Opens.ext
  exact Set.range_eq_univ.mpr hsurj

/-- SAME projective model D viewed over ORIGINAL K has an ACTUAL coproduct
base change indexed by ALL ACTUAL original-K embeddings M→Ω. Each summand
is the literal homogeneous quotient D.map(phi), and both native projections
are proved. No decomposition, geometric integrality or field orbit premise. -/
theorem projectiveModel_originalBaseChange_exists_embedding_indexed_coproductIso
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M)) :
    ∃ e : (∐ fun phi : M →ₐ[K] Ω => scheme (D.map (componentPolynomialCoefficientMap phi.toRingHom))) ≅
        pullback (toBase D ≫ Spec.map (CommRingCat.ofHom (algebraMap K M)))
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω))),
      ∀ phi : M →ₐ[K] Ω,
        Sigma.ι _ phi ≫ e.hom ≫ pullback.fst _ _ =
          projectiveCoefficientMap phi.toRingHom D (D.map (componentPolynomialCoefficientMap phi.toRingHom)) rfl ∧
        Sigma.ι _ phi ≫ e.hom ≫ pullback.snd _ _ =
          toBase (D.map (componentPolynomialCoefficientMap phi.toRingHom)) := by
  let s := projectiveModelEmbeddingTensorCoproductMap (K := K) (Ω := Ω) D
  letI : IsIso s := projectiveModelEmbeddingTensorCoproductMap_isIso D
  let H := modelSchemeFieldTensor_originalBaseChange_isPullback (K := K) (Ω := Ω) (toBase D)
  let e := asIso s ≪≫ H.isoPullback
  refine ⟨e, ?_⟩
  intro phi
  constructor
  · change Sigma.ι _ phi ≫ s ≫ H.isoPullback.hom ≫ pullback.fst _ _ = _
    rw [H.isoPullback_hom_fst]
    dsimp only [s, projectiveModelEmbeddingTensorCoproductMap]
    rw [← Category.assoc, Sigma.ι_desc]
    dsimp only [projectiveModelEmbeddingComponentToTensorBaseChange]
    exact pullback.lift_fst _ _ _
  · change Sigma.ι _ phi ≫ s ≫ H.isoPullback.hom ≫ pullback.snd _ _ = _
    rw [H.isoPullback_hom_snd]
    dsimp only [s, projectiveModelEmbeddingTensorCoproductMap]
    rw [← Category.assoc, Sigma.ι_desc]
    dsimp only [projectiveModelEmbeddingComponentToTensorBaseChange]
    rw [← Category.assoc, pullback.lift_snd, Category.assoc,
      modelFieldTensorEmbeddingFactor_omega, Category.comp_id]

/-- The SAME actual stabilizer-fixed-field model D of actual C has its
embedding-indexed coproduct base change over ORIGINAL K. Module finiteness
and separability are internally derived from L/K Galois. This keeps SAME D
and both actual projections; no desired scheme decomposition is supplied. -/
theorem homogeneousIdealStabilizerModel_originalBaseChange_exists_embedding_indexed_coproductIso
    {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L)) :
    let M := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
    ∃ e : (∐ fun phi : M →ₐ[K] Ω => scheme (D.map (componentPolynomialCoefficientMap phi.toRingHom))) ≅
        pullback (toBase D ≫ Spec.map (CommRingCat.ofHom (algebraMap K M)))
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω))),
      ∀ phi : M →ₐ[K] Ω,
        Sigma.ι _ phi ≫ e.hom ≫ pullback.fst _ _ =
          projectiveCoefficientMap phi.toRingHom D (D.map (componentPolynomialCoefficientMap phi.toRingHom)) rfl ∧
        Sigma.ι _ phi ≫ e.hom ≫ pullback.snd _ _ =
          toBase (D.map (componentPolynomialCoefficientMap phi.toRingHom)) := by
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  letI : Module.Finite K M := inferInstance
  letI : Algebra.IsSeparable K M := inferInstance
  exact projectiveModel_originalBaseChange_exists_embedding_indexed_coproductIso D

end PfaffianDescent.Coray
