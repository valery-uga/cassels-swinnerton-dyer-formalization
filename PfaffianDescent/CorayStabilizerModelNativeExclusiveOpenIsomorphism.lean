import PfaffianDescent.CorayNativeReducedComponentExclusiveOpen
import PfaffianDescent.CorayLiteralIncidenceComponentCount
import PfaffianDescent.CorayOriginalPrimeCoefficientReducedUnion

/-! SAME original I, WHOLE stabilizer model M/D, actual native Ω-base-change
map: generic component opens are CONSTRUCTED isomorphism loci. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial

/-- For the WHOLE stabilizer model, the actual Ω-base change of f is an
isomorphism on every component-exclusive open. All native coproduct maps,
component images, target reducedness and finite components are constructed.
No birationality, unit-isomorphism, finite support or point bound is supplied. -/
theorem stabilizerModel_originalBaseChange_exists_componentExclusiveOpen_wholeMap_isIso001
    {K L Ω : Type u} [Field K] [CharZero K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [FiniteDimensional K L] [IsGalois K L] [IsAlgClosed Ω] [IsGalois K Ω]
    [Algebra.IsAlgebraic K Ω]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ I)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) L))
    (hC : C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes)
    (hCO : (C.toIdeal.map (MvPolynomial.map (algebraMap L Ω))).IsPrime) :
    let M := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
    let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
    ∃ hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal,
      let f := coefficientComponentToOriginal I D hID
      let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
      let iO := projectiveBaseChangeIso (algebraMap K Ω) I IO rfl
      let F := nativeOriginalBaseChangeMap f (toBase I) b ≫ iO.inv
      ∀ phi : M →ₐ[K] Ω, ∃ U : (scheme IO).Opens,
        (U : Set (scheme IO)) =
          (⋃₀ (irreducibleComponents (scheme IO) \ {Set.range (modelEmbeddingComponentToGeometricOriginal I D hID phi)}))ᶜ ∧
        closure (U : Set (scheme IO)) =
          Set.range (modelEmbeddingComponentToGeometricOriginal I D hID phi) ∧
        (U : Set (scheme IO)).Nonempty ∧ IsIso (F ∣_ U) := by
  letI : C.toIdeal.IsPrime := hC.isPrime
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
  letI : Module.Finite K M := inferInstance
  letI : Algebra.IsSeparable K M := inferInstance
  have hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal :=
    (stabilizerModel_minimalPrime_over_originalExtension I C hC).le
  let f := coefficientComponentToOriginal I D hID
  let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let iO := projectiveBaseChangeIso (algebraMap K Ω) I IO rfl
  let F := nativeOriginalBaseChangeMap f (toBase I) b ≫ iO.inv
  let X := fun phi : M →ₐ[K] Ω =>
    scheme (D.map (componentPolynomialCoefficientMap phi.toRingHom))
  have hRadical : IO.toIdeal.IsRadical :=
    polynomialPrime_perfectAlgebraicCoefficientExtension_isRadical001 I.toIdeal
  letI : IsReduced (scheme IO) := scheme_isReduced_of_isRadical IO hRadical
  letI : IsLocallyNoetherian (scheme IO) :=
    LocallyOfFiniteType.isLocallyNoetherian (toBase IO)
  letI : CompactSpace (scheme IO) :=
    QuasiCompact.compactSpace_of_compactSpace (toBase IO)
  letI : IsNoetherian (scheme IO) := ⟨⟩
  have hFinite : (irreducibleComponents (scheme IO)).Finite :=
    NoetherianSpace.finite_irreducibleComponents
  obtain ⟨e, he⟩ := modelOriginalBaseChange_exists_embeddingCoproduct_canonicalImageMap
    (Ω := Ω) I D hID
  obtain ⟨c, hc⟩ := stabilizerModel_exists_embedding_projectiveComponentEquiv I hIrel C hC hCO
  have hClosed (phi : M →ₐ[K] Ω) :
      IsClosedImmersion ((Sigma.ι X phi ≫ e.hom) ≫ F) := by
    rw [Category.assoc, (he phi).2]
    exact (he phi).1
  have hc' (phi : M →ₐ[K] Ω) :
      (c phi).1 = Set.range ((Sigma.ι X phi ≫ e.hom) ≫ F) := by
    rw [Category.assoc, (he phi).2]
    exact hc phi
  refine ⟨hID, ?_⟩
  dsimp only
  intro phi
  obtain ⟨U, hU, hClosure, hNonempty, hIso⟩ :=
    nativeReducedComponentCoproduct_exists_exclusiveOpen_wholeMap_isIso001
      X e F hClosed c hc' hFinite phi
  have hMap : (Sigma.ι X phi ≫ e.hom) ≫ F =
      modelEmbeddingComponentToGeometricOriginal I D hID phi := by
    rw [Category.assoc]
    exact (he phi).2
  rw [hMap] at hU hClosure
  exact ⟨U, hU, hClosure, hNonempty, hIso⟩

end PfaffianDescent.Coray
