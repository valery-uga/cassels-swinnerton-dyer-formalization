import PfaffianDescent.CorayLiteralIncidenceGeometricFiber
import PfaffianDescent.CorayModelProjectiveEmbeddingCoproduct
import PfaffianDescent.CorayStabilizerModelEmbeddingComponentBijection

/-! Source only: native rank of SAME entire incidence counts SAME geometric
components containing the ACTUAL original-point lift. Pending genuine
construction dependencies are recorded separately. No point transitivity. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A native scheme coproduct with closed-immersion summand maps has one
fibre point for each incident summand. This bounded structural helper uses
injectivity of each ACTUAL summand map, never point-orbit transitivity. -/
theorem nativeClosedImmersionCoproduct_fiberEquiv_incidentIndices
    {ι : Type u} (X : ι → Scheme.{u}) {W T : Scheme.{u}}
    (e : (∐ X) ≅ W) (F : W ⟶ T)
    (hclosed : ∀ i, IsClosedImmersion (Sigma.ι X i ≫ e.hom ≫ F)) (x : T.carrier) :
    Nonempty ({y : W.carrier | F y = x} ≃ {i : ι | x ∈ Set.range (Sigma.ι X i ≫ e.hom ≫ F)}) := by
  classical
  let E : (Σ i, (X i).carrier) ≃ W.carrier := (AlgebraicGeometry.sigmaMk X).toEquiv.trans e.hom.homeomorph.toEquiv
  let j : ∀ i, X i ⟶ T := fun i => Sigma.ι X i ≫ e.hom ≫ F
  have hE (s : Σ i, (X i).carrier) : F (E s) = j s.1 s.2 := by
    rcases s with ⟨i, z⟩
    change F (e.hom (AlgebraicGeometry.sigmaMk X ⟨i, z⟩)) = (Sigma.ι X i ≫ e.hom ≫ F) z
    rw [AlgebraicGeometry.sigmaMk_mk]
    rfl
  let A := {s : Σ i, (X i).carrier | j s.1 s.2 = x}
  let B := {i : ι | x ∈ Set.range (j i)}
  let g : A → B := fun s => ⟨s.1.1, s.1.2, s.2⟩
  have hinj : Function.Injective g := by
    rintro ⟨⟨i, z⟩, hz⟩ ⟨⟨k, w⟩, hw⟩ h
    have hik : i = k := congrArg Subtype.val h
    subst k
    letI : IsClosedImmersion (j i) := hclosed i
    have hzw : z = w := (j i).isClosedEmbedding.injective (hz.trans hw.symm)
    subst w
    rfl
  have hsurj : Function.Surjective g := by
    rintro ⟨i, hi⟩
    obtain ⟨z, hz⟩ := hi
    exact ⟨⟨⟨i, z⟩, hz⟩, rfl⟩
  let e1 : A ≃ {y : W.carrier | F y = x} := E.subtypeEquiv (fun s => by
    change j s.1 s.2 = x ↔ F (E s) = x
    rw [hE])
  let e2 : A ≃ B := Equiv.ofBijective g ⟨hinj, hsurj⟩
  exact ⟨e1.symm.trans e2⟩

variable {K M Ω : Type u} [Field K] [Field M] [Field Ω]
  [Algebra K M] [Module.Finite K M] [Algebra.IsSeparable K M]
  [Algebra K Ω] [IsAlgClosed Ω]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual containment for the canonical embedding-component quotient.
The whole original-map square producer constructs it, rather than accepting
an incidence-image or desired component certificate. -/
def modelEmbeddingOriginalContainment
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (phi : M →ₐ[K] Ω) :
    (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal ≤
      (D.map (componentPolynomialCoefficientMap phi.toRingHom)).toIdeal :=
  Classical.choose (modelEmbeddingComponent_originalMap_closedImmersion_square I D hID phi)

def modelEmbeddingComponentToGeometricOriginal
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (phi : M →ₐ[K] Ω) :
    scheme (D.map (componentPolynomialCoefficientMap phi.toRingHom)) ⟶
      scheme (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))) :=
  schemeQuotientMap _ _ (modelEmbeddingOriginalContainment I D hID phi)

/-- CONSTRUCT the actual embedding-indexed coproduct of SAME D over original
K with its actual map to SAME I_Omega. Every summand map is PROVED equal to
its canonical quotient closed immersion, by BOTH native pullback projections.
No coproduct, component-image equality, GI or fibre count is supplied. -/
theorem modelOriginalBaseChange_exists_embeddingCoproduct_canonicalImageMap
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal) :
    let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
    let f := coefficientComponentToOriginal I D hID
    let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let iO := projectiveBaseChangeIso (algebraMap K Ω) I IO rfl
    let F := nativeOriginalBaseChangeMap f (toBase I) b ≫ iO.inv
    ∃ e : (∐ fun phi : M →ₐ[K] Ω => scheme (D.map (componentPolynomialCoefficientMap phi.toRingHom))) ≅
        pullback (f ≫ toBase I) b,
      ∀ phi : M →ₐ[K] Ω,
        IsClosedImmersion (modelEmbeddingComponentToGeometricOriginal I D hID phi) ∧
          Sigma.ι _ phi ≫ e.hom ≫ F = modelEmbeddingComponentToGeometricOriginal I D hID phi := by
  let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
  let f := coefficientComponentToOriginal I D hID
  let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let bM := Spec.map (CommRingCat.ofHom (algebraMap K M))
  let iO := projectiveBaseChangeIso (algebraMap K Ω) I IO rfl
  let F0 := nativeOriginalBaseChangeMap f (toBase I) b
  let F := F0 ≫ iO.inv
  obtain ⟨e0, he0⟩ := projectiveModel_originalBaseChange_exists_embedding_indexed_coproductIso
    (K := K) (Ω := Ω) D
  have hcoeff : f ≫ toBase I = toBase D ≫ bM :=
    (coefficientComponentToOriginal_finite_and_toBase I D hID).2
  let eW := pullback.congrHom hcoeff.symm (rfl : b = b)
  let e := e0 ≪≫ eW
  have hefst (phi : M →ₐ[K] Ω) : Sigma.ι _ phi ≫ e.hom ≫ pullback.fst (f ≫ toBase I) b =
      projectiveCoefficientMap phi.toRingHom D (D.map (componentPolynomialCoefficientMap phi.toRingHom)) rfl := by
    simp only [e, Iso.trans_hom, Category.assoc, eW, pullback.congrHom_hom,
      pullback.map, pullback.lift_fst, Category.comp_id]
    exact (he0 phi).1
  have hesnd (phi : M →ₐ[K] Ω) : Sigma.ι _ phi ≫ e.hom ≫ pullback.snd (f ≫ toBase I) b =
      toBase (D.map (componentPolynomialCoefficientMap phi.toRingHom)) := by
    simp only [e, Iso.trans_hom, Category.assoc, eW, pullback.congrHom_hom,
      pullback.map, pullback.lift_snd, Category.comp_id]
    exact (he0 phi).2
  refine ⟨e, ?_⟩
  intro phi
  let DP := D.map (componentPolynomialCoefficientMap phi.toRingHom)
  let j := modelEmbeddingComponentToGeometricOriginal I D hID phi
  have hj := Classical.choose_spec (modelEmbeddingComponent_originalMap_closedImmersion_square I D hID phi)
  letI : IsClosedImmersion j := hj.1
  refine ⟨inferInstance, ?_⟩
  apply (cancel_mono iO.hom).mp
  change (Sigma.ι _ phi ≫ e.hom ≫ F) ≫ iO.hom = j ≫ iO.hom
  simp only [F, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · calc
      (Sigma.ι _ phi ≫ e.hom ≫ F0) ≫ pullback.fst (toBase I) b =
          (Sigma.ι _ phi ≫ e.hom ≫ pullback.fst (f ≫ toBase I) b) ≫ f := by
        simp only [Category.assoc, show F0 ≫ pullback.fst (toBase I) b =
          pullback.fst (f ≫ toBase I) b ≫ f from pullback.lift_fst _ _ _]
      _ = projectiveCoefficientMap phi.toRingHom D DP rfl ≫ f := by rw [hefst]
      _ = j ≫ projectiveCoefficientMap (algebraMap K Ω) I IO rfl := hj.2.symm
      _ = (j ≫ iO.hom) ≫ pullback.fst (toBase I) b := by
        rw [Category.assoc, projectiveBaseChangeIso_hom_fst]
  · calc
      (Sigma.ι _ phi ≫ e.hom ≫ F0) ≫ pullback.snd (toBase I) b =
          Sigma.ι _ phi ≫ e.hom ≫ pullback.snd (f ≫ toBase I) b := by
        simp only [Category.assoc, show F0 ≫ pullback.snd (toBase I) b =
          pullback.snd (f ≫ toBase I) b from pullback.lift_snd _ _ _]
      _ = toBase DP := hesnd phi
      _ = j ≫ toBase IO := (schemeQuotientMap_toBase IO DP
        (modelEmbeddingOriginalContainment I D hID phi)).symm
      _ = (j ≫ iO.hom) ≫ pullback.snd (toBase I) b := by
        rw [Category.assoc, projectiveBaseChangeIso_hom_snd]

/-- The SAME literal incidence's native residue rank equals the number of
ACTUAL embeddings whose canonical geometric component image contains the
ACTUAL geometric lift of SAME original P. The coproduct and image maps are
constructed in root2, not assumed in this arithmetic/geometric join. -/
theorem originalPointModelIncidence_residueRank_eq_incidentEmbeddingCard
    [CharZero K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (P : closedPoints (scheme I))
    (psi : letI := pointAlgebra (toBase I) P.1; (scheme I).residueField P.1 →ₐ[K] Ω) :
    let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
    let ep := (scheme I).fromSpecResidueField P.1
    let f := coefficientComponentToOriginal I D hID
    let c := pullback.fst ep f
    let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    letI := pointAlgebra (toBase I) P.1
    let v := Spec.map (CommRingCat.ofHom psi.toRingHom)
    let iO := projectiveBaseChangeIso (algebraMap K Ω) I IO rfl
    ∃ hfinite : IsFinite c, ∃ hv : v ≫ ep ≫ toBase I = b,
      letI := hfinite
      let q := nativeOriginalPointGeometricLift ep (toBase I) b v hv ≫ iO.inv
      finiteSchemeRank c = Nat.card {phi : M →ₐ[K] Ω |
        q (IsLocalRing.closedPoint Ω) ∈ Set.range (modelEmbeddingComponentToGeometricOriginal I D hID phi)} := by
  let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
  let ep := (scheme I).fromSpecResidueField P.1
  let f := coefficientComponentToOriginal I D hID
  let c := pullback.fst ep f
  let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  letI := pointAlgebra (toBase I) P.1
  let v := Spec.map (CommRingCat.ofHom psi.toRingHom)
  let iO := projectiveBaseChangeIso (algebraMap K Ω) I IO rfl
  let F0 := nativeOriginalBaseChangeMap f (toBase I) b
  let F := F0 ≫ iO.inv
  obtain ⟨hfinite, hv, hrank⟩ := originalPointModelIncidence_residueRank_eq_geometricFiberCard I D hID P psi
  letI : IsFinite c := hfinite
  let q0 := nativeOriginalPointGeometricLift ep (toBase I) b v hv
  let q := q0 ≫ iO.inv
  let x := q (IsLocalRing.closedPoint Ω)
  obtain ⟨e, he⟩ := modelOriginalBaseChange_exists_embeddingCoproduct_canonicalImageMap
    (Ω := Ω) I D hID
  let X := fun phi : M →ₐ[K] Ω => scheme (D.map (componentPolynomialCoefficientMap phi.toRingHom))
  have hclosed (phi : M →ₐ[K] Ω) : IsClosedImmersion (Sigma.ι X phi ≫ e.hom ≫ F) := by
    rw [(he phi).2]
    exact (he phi).1
  let e1 : {y : (pullback (f ≫ toBase I) b).carrier | F0 y = q0 (IsLocalRing.closedPoint Ω)} ≃
      {y : (pullback (f ≫ toBase I) b).carrier | F y = x} :=
    (Equiv.refl _).subtypeEquiv (fun y => by
      change F0 y = q0 (IsLocalRing.closedPoint Ω) ↔
        iO.inv (F0 y) = iO.inv (q0 (IsLocalRing.closedPoint Ω))
      constructor
      · exact congrArg iO.inv
      · intro hy
        apply iO.inv.homeomorph.injective
        simpa only [Scheme.Hom.homeomorph_apply] using hy)
  obtain ⟨e2⟩ := nativeClosedImmersionCoproduct_fiberEquiv_incidentIndices X e F hclosed x
  let e3 : {phi : M →ₐ[K] Ω | x ∈ Set.range (Sigma.ι X phi ≫ e.hom ≫ F)} ≃
      {phi : M →ₐ[K] Ω | x ∈ Set.range (modelEmbeddingComponentToGeometricOriginal I D hID phi)} :=
    (Equiv.refl _).subtypeEquiv (fun phi => by
      change x ∈ Set.range (Sigma.ι X phi ≫ e.hom ≫ F) ↔
        x ∈ Set.range (modelEmbeddingComponentToGeometricOriginal I D hID phi)
      rw [(he phi).2])
  refine ⟨hfinite, hv, ?_⟩
  exact hrank.trans (Nat.card_congr (e1.trans (e2.trans e3)))

/-- SAME actual whole-stabilizer model's native entire-incidence rank counts
ALL native geometric components of SAME I_Omega containing SAME original-P
lift. The embedding/component equivalence and exact canonical images are
constructed from actual C, not supplied as a count/decomposition premise. -/
theorem stabilizerModel_originalPointIncidence_residueRank_eq_incidentComponentCard
    [CharZero K] [IsGalois K Ω]
    {L : Type u} [Field L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
    [FiniteDimensional K L] [IsGalois K L]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ I)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L))
    (hC : C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes)
    (hCO : (C.toIdeal.map (MvPolynomial.map (algebraMap L Ω))).IsPrime)
    (P : closedPoints (scheme I))
    (psi : letI := pointAlgebra (toBase I) P.1; (scheme I).residueField P.1 →ₐ[K] Ω) :
    let M := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
    let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
    let ep := (scheme I).fromSpecResidueField P.1
    let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    letI := pointAlgebra (toBase I) P.1
    let v := Spec.map (CommRingCat.ofHom psi.toRingHom)
    let iO := projectiveBaseChangeIso (algebraMap K Ω) I IO rfl
    ∃ hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal,
    ∃ hfinite : IsFinite (pullback.fst ep (coefficientComponentToOriginal I D hID)),
    ∃ hv : v ≫ ep ≫ toBase I = b,
      letI := hfinite
      let q := nativeOriginalPointGeometricLift ep (toBase I) b v hv ≫ iO.inv
      finiteSchemeRank (pullback.fst ep (coefficientComponentToOriginal I D hID)) =
        Nat.card {T : irreducibleComponents (scheme IO) | q (IsLocalRing.closedPoint Ω) ∈ T.1} := by
  letI : C.toIdeal.IsPrime := hC.isPrime
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
  letI : Module.Finite K M := inferInstance
  letI : Algebra.IsSeparable K M := inferInstance
  have hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal :=
    (stabilizerModel_minimalPrime_over_originalExtension I C hC).le
  obtain ⟨hfinite, hv, hrank⟩ := originalPointModelIncidence_residueRank_eq_incidentEmbeddingCard I D hID P psi
  obtain ⟨e, he⟩ := stabilizerModel_exists_embedding_projectiveComponentEquiv I hIrel C hC hCO
  let ep := (scheme I).fromSpecResidueField P.1
  let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  letI := pointAlgebra (toBase I) P.1
  let v := Spec.map (CommRingCat.ofHom psi.toRingHom)
  let iO := projectiveBaseChangeIso (algebraMap K Ω) I IO rfl
  let q := nativeOriginalPointGeometricLift ep (toBase I) b v hv ≫ iO.inv
  let x := q (IsLocalRing.closedPoint Ω)
  have himage (phi : M →ₐ[K] Ω) :
      (e phi).1 = Set.range (modelEmbeddingComponentToGeometricOriginal I D hID phi) := he phi
  let e' : {phi : M →ₐ[K] Ω | x ∈ Set.range (modelEmbeddingComponentToGeometricOriginal I D hID phi)} ≃
      {T : irreducibleComponents (scheme IO) | x ∈ T.1} :=
    e.subtypeEquiv (fun phi => by
      change x ∈ Set.range (modelEmbeddingComponentToGeometricOriginal I D hID phi) ↔
        x ∈ (e phi).1
      rw [himage phi])
  exact ⟨hID, hfinite, hv, hrank.trans (Nat.card_congr e')⟩

/-- Ordinary SAME original prime I, SAME geometric minimal component G and
SAME original P construct ONCE the joint stabilizer model and its ENTIRE
incidence. Its native residue rank is the ACTUAL number of native geometric
components through the literal P-lift. Extension primeness is DERIVED from
G; no GI, splitting, component bijection, count or transitivity premise. -/
theorem originalGeometricMinimalPrime_exists_jointModel_entireIncidence_componentCount
    [CharZero K] [IsGalois K Ω]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ I)
    (G : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) Ω))
    (hG : G.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes)
    (P : closedPoints (scheme I))
    (psi : letI := pointAlgebra (toBase I) P.1; (scheme I).residueField P.1 →ₐ[K] Ω) :
    ∃ (L : FiniteGaloisIntermediateField K Ω)
      (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L)),
      ∃ hC : C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes,
      ∃ hCG : C.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = G.toIdeal,
      let M := homogeneousIdealStabilizerFixedField (K := K) C
      let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
      let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
      let ep := (scheme I).fromSpecResidueField P.1
      let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
      letI := pointAlgebra (toBase I) P.1
      let v := Spec.map (CommRingCat.ofHom psi.toRingHom)
      let iO := projectiveBaseChangeIso (algebraMap K Ω) I IO rfl
      ∃ hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal,
      ∃ hfinite : IsFinite (pullback.fst ep (coefficientComponentToOriginal I D hID)),
      ∃ hv : v ≫ ep ≫ toBase I = b,
        letI := hfinite
        let q := nativeOriginalPointGeometricLift ep (toBase I) b v hv ≫ iO.inv
        GeometricallyIntegral (toBase D) ∧
          finiteSchemeRank (pullback.fst ep (coefficientComponentToOriginal I D hID)) =
            Nat.card {T : irreducibleComponents (scheme IO) | q (IsLocalRing.closedPoint Ω) ∈ T.1} := by
  obtain ⟨L, C, hC, hCG, _hDprime, _hDL, _hfield, hGI, _hall⟩ :=
    originalGeometricMinimalPrime_exists_jointStabilizerModel I hIrel G.toIdeal hG
  have hCO : (C.toIdeal.map (MvPolynomial.map (algebraMap L Ω))).IsPrime := hCG.symm ▸ hG.isPrime
  obtain ⟨hID, hfinite, hv, hcount⟩ :=
    stabilizerModel_originalPointIncidence_residueRank_eq_incidentComponentCard I hIrel C hC hCO P psi
  exact ⟨L, C, hC, hCG, hID, hfinite, hv, hGI, hcount⟩

end PfaffianDescent.Coray
