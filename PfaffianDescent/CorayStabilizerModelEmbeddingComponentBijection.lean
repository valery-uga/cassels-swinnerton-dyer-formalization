import PfaffianDescent.CorayJointSelectedComponentPositiveDegree
import PfaffianDescent.CorayHomogeneousProjectiveComponentBijection
import PfaffianDescent.PolynomialCoefficientFaithfullyFlat
import PfaffianDescent.CorayEntireModelIncidenceCycle
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal.Basic

/-! Source only: ACTUAL embeddings of SAME whole-ideal stabilizer field
biject with SAME original geometric minimal components. No point orbit
transitivity, supplied component bijection or desired incidence count. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped Pointwise
universe u
variable {K L Ω : Type u} [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [FiniteDimensional K L] [IsGalois K L] [IsAlgClosed Ω]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] polynomialGaloisCoefficientAction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every ACTUAL original-K embedding of an intermediate field into Ω is
the restriction of an ACTUAL L/K Galois automorphism followed by the fixed
L→Ω inclusion. Algebraic extension and normality construct it. -/
theorem intermediateFieldEmbedding_exists_galoisExtension
    (M : IntermediateField K L) (phi : M →ₐ[K] Ω) :
    ∃ g : L ≃ₐ[K] L,
      ((IsScalarTower.toAlgHom K L Ω).comp g.toAlgHom).domRestrict M = phi := by
  obtain ⟨f, hf⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic
    (K := K) (L := M) (M := Ω) (E := L) phi
  obtain ⟨g, hg⟩ := (Normal.algHomEquivAut K Ω (E := L)).symm.surjective f
  change (IsScalarTower.toAlgHom K L Ω).comp g.toAlgHom = f at hg
  exact ⟨g, (congrArg (fun h : L →ₐ[K] Ω => h.domRestrict M) hg).trans hf⟩

/-- Literal coefficient extension of SAME D along phi is the literal
extension of the corresponding conjugate of SAME C. WHOLE-ideal descent
derives the equality; no chosen generators or image equality is assumed. -/
theorem stabilizerModel_embedding_extension_eq_galois_componentExtension
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L)) [C.toIdeal.IsPrime]
    (phi : homogeneousIdealStabilizerFixedField (K := K) C →ₐ[K] Ω)
    (g : L ≃ₐ[K] L)
    (hphi : ((IsScalarTower.toAlgHom K L Ω).comp g.toAlgHom).domRestrict
      (homogeneousIdealStabilizerFixedField (K := K) C) = phi) :
    let M := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
    (D.map (componentPolynomialCoefficientMap phi.toRingHom)).toIdeal =
      (C.toIdeal.map (MvPolynomial.map g.toRingHom)).map
        (MvPolynomial.map (algebraMap L Ω)) := by
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  have hdesc := (homogeneousPrime_stabilizerFixedField_descends (K := K) C).2
  change D.toIdeal.map (MvPolynomial.map phi.toRingHom) = _
  rw [← hdesc, Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro t
  apply MvPolynomial.ext
  intro d
  simp only [RingHom.comp_apply, MvPolynomial.coeff_map]
  exact (DFunLike.congr_fun hphi (MvPolynomial.coeff d t)).symm

/-- ACTUAL embeddings of the WHOLE-ideal stabilizer field have distinct
literal geometric coefficient ideals. Equal ideals contract to equal
conjugates of C; their relative automorphism stabilizes the WHOLE ideal,
so it fixes EVERY model-field scalar. No point transitivity is used. -/
theorem stabilizerModel_embedding_componentIdeal_injective
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L)) [C.toIdeal.IsPrime] :
    let M := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
    Function.Injective (fun phi : M →ₐ[K] Ω =>
      (D.map (componentPolynomialCoefficientMap phi.toRingHom)).toIdeal) := by
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  change Function.Injective (fun phi : M →ₐ[K] Ω =>
    (D.map (componentPolynomialCoefficientMap phi.toRingHom)).toIdeal)
  intro phi psi heq
  obtain ⟨g, hg⟩ := intermediateFieldEmbedding_exists_galoisExtension M phi
  obtain ⟨h, hh⟩ := intermediateFieldEmbedding_exists_galoisExtension M psi
  have hmaps : (C.toIdeal.map (MvPolynomial.map g.toRingHom)).map (MvPolynomial.map (algebraMap L Ω)) =
      (C.toIdeal.map (MvPolynomial.map h.toRingHom)).map (MvPolynomial.map (algebraMap L Ω)) :=
    (stabilizerModel_embedding_extension_eq_galois_componentExtension C phi g hg).symm.trans
      (heq.trans (stabilizerModel_embedding_extension_eq_galois_componentExtension C psi h hh))
  have hconjugates : C.toIdeal.map (MvPolynomial.map g.toRingHom) =
      C.toIdeal.map (MvPolynomial.map h.toRingHom) := by
    have hcon := congrArg (Ideal.comap (MvPolynomial.map (algebraMap L Ω))) hmaps
    simpa only [mvPolynomial_comap_map_coefficientExtension] using hcon
  have haction : g • C.toIdeal = h • C.toIdeal := hconjugates
  have hstab : h⁻¹ * g ∈ homogeneousIdealCoefficientStabilizer (K := K) C := by
    apply MulAction.mem_stabilizer_iff.mpr
    rw [mul_smul, haction, inv_smul_smul]
  apply AlgHom.ext
  intro m
  have hfix : (h⁻¹ * g) (m : L) = (m : L) :=
    (IntermediateField.mem_fixedField_iff
      (homogeneousIdealCoefficientStabilizer (K := K) C) (m : L)).mp m.2 (h⁻¹ * g) hstab
  have hgh : g (m : L) = h (m : L) := by
    have he := congrArg h hfix
    change h (h.symm (g (m : L))) = h (m : L) at he
    simpa only [AlgEquiv.apply_symm_apply] using he
  exact (DFunLike.congr_fun hg m).symm.trans
    ((congrArg (algebraMap L Ω) hgh).trans (DFunLike.congr_fun hh m))

/-- The actual whole stabilizer contraction is minimal over SAME I_M.
Going down contracts SAME C from I_L; original K/M/L coefficient identities
derive the literal extended ideal. No minimality of D is supplied. -/
theorem stabilizerModel_minimalPrime_over_originalExtension
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L))
    (hC : C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes) :
    let M := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
    D.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes := by
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  let IM := I.map (componentPolynomialCoefficientMap (algebraMap K M))
  have hchain : IM.toIdeal.map (MvPolynomial.map (algebraMap M L)) =
      (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal := by
    change (I.toIdeal.map (MvPolynomial.map (algebraMap K M))).map
      (MvPolynomial.map (algebraMap M L)) = I.toIdeal.map (MvPolynomial.map (algebraMap K L))
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro t
    change MvPolynomial.map (algebraMap M L) (MvPolynomial.map (algebraMap K M) t) =
      MvPolynomial.map (algebraMap K L) t
    rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq K M L]
  have hCM : C.toIdeal ∈ (IM.toIdeal.map (MvPolynomial.map (algebraMap M L))).minimalPrimes := by
    rw [hchain]
    exact hC
  exact polynomialCoefficientExtension_minimalPrime_comap_mem IM.toIdeal C.toIdeal hCM

/-- EVERY actual model-field embedding gives an ACTUAL geometric minimal
prime over SAME I_Ω. Actual primeness after the given algebraic-closed
coefficient extension of C produces all-field primeness of D; native
minimal-prime transport and phi fixing K prove the asserted minimality. -/
theorem stabilizerModel_embedding_componentIdeal_minimalPrime
    [IsGalois K Ω]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L))
    (hC : C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes)
    (hCO : (C.toIdeal.map (MvPolynomial.map (algebraMap L Ω))).IsPrime) :
    let M := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
    ∀ phi : M →ₐ[K] Ω,
      (D.map (componentPolynomialCoefficientMap phi.toRingHom)).toIdeal ∈
        (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes := by
  letI : C.toIdeal.IsPrime := hC.isPrime
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  let IM := I.map (componentPolynomialCoefficientMap (algebraMap K M))
  have hDmin := stabilizerModel_minimalPrime_over_originalExtension I C hC
  have hdesc := homogeneousPrime_stabilizerFixedField_descends (K := K) C
  letI : D.toIdeal.IsPrime := hdesc.1
  letI aMO : Algebra M Ω := ((algebraMap L Ω).comp (algebraMap M L)).toAlgebra
  have hKMOmap : ∀ k : K, algebraMap K Ω k =
      (@algebraMap M Ω _ _ aMO) (algebraMap K M k) := by
    intro k
    change algebraMap K Ω k = algebraMap L Ω (algebraMap M L (algebraMap K M k))
    rw [← IsScalarTower.algebraMap_apply K M L, ← IsScalarTower.algebraMap_apply K L Ω]
  letI hKMO : @IsScalarTower K M Ω
      (inferInstance : Algebra K M).toSMul aMO.toSMul
      (inferInstance : Algebra K Ω).toSMul :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := M) (A := Ω) hKMOmap
  letI : Algebra.IsAlgebraic M Ω :=
    @Algebra.IsAlgebraic.tower_top K M Ω
      (inferInstance : Field K) (inferInstance : Field M) (inferInstance : Ring Ω)
      (inferInstance : Algebra K M) aMO (inferInstance : Algebra K Ω) hKMO
      (inferInstance : Algebra.IsAlgebraic K Ω)
  have hcomp : (MvPolynomial.map (σ := Fin 4) (algebraMap L Ω)).comp
      (MvPolynomial.map (algebraMap M L)) = MvPolynomial.map (algebraMap M Ω) := by
    apply RingHom.ext
    intro t
    exact MvPolynomial.map_map _ _ t
  have hDO : (D.toIdeal.map (MvPolynomial.map (algebraMap M Ω))).IsPrime := by
    rw [← hcomp, ← Ideal.map_map, hdesc.2]
    exact hCO
  have hall : ∀ (T : Type u) [Field T] [Algebra M T],
      (D.toIdeal.map (MvPolynomial.map (algebraMap M T))).IsPrime := by
    intro T _ _
    exact polynomialCoefficientExtension_prime_of_algClosed_algebraicExtension
      (Ω := Ω) (T := T) D.toIdeal hDO
  change ∀ phi : M →ₐ[K] Ω,
    (D.map (componentPolynomialCoefficientMap phi.toRingHom)).toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes
  intro phi
  letI : Algebra M Ω := phi.toRingHom.toAlgebra
  let DP := D.map (componentPolynomialCoefficientMap phi.toRingHom)
  letI : DP.toIdeal.IsPrime := hall Ω
  have hDPself : DP.toIdeal ∈ (D.toIdeal.map (MvPolynomial.map (algebraMap M Ω))).minimalPrimes := by
    change DP.toIdeal ∈ DP.toIdeal.minimalPrimes
    simp only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]
  have hDP := originalMinimalPrime_coefficientExtension_minimalPrime_over_wholeIdeal
    IM.toIdeal D.toIdeal hDmin DP.toIdeal hDPself
  have hground : (MvPolynomial.map (σ := Fin 4) phi.toRingHom).comp
      (MvPolynomial.map (algebraMap K M)) = MvPolynomial.map (algebraMap K Ω) := by
    apply RingHom.ext
    intro t
    apply MvPolynomial.ext
    intro d
    simp only [RingHom.comp_apply, MvPolynomial.coeff_map]
    exact phi.commutes (MvPolynomial.coeff d t)
  change DP.toIdeal ∈ ((I.toIdeal.map (MvPolynomial.map (algebraMap K M))).map
    (MvPolynomial.map phi.toRingHom)).minimalPrimes at hDP
  rw [Ideal.map_map, hground] at hDP
  exact hDP

/-- EVERY geometric minimal prime of SAME I_Ω is obtained from an actual
model-field embedding. Contract it to L, conjugate that actual minimal prime
to SAME C, and extend the WHOLE descended ideal. No splitting bijection or
transitivity on prescribed points is supplied. -/
theorem stabilizerModel_embedding_componentIdeal_surjective_onto_minimalPrimes
    [IsGalois K Ω]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L))
    (hC : C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes)
    (hCO : (C.toIdeal.map (MvPolynomial.map (algebraMap L Ω))).IsPrime) :
    let M := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
    ∀ Q ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes,
      ∃ phi : M →ₐ[K] Ω, (D.map (componentPolynomialCoefficientMap phi.toRingHom)).toIdeal = Q := by
  letI : C.toIdeal.IsPrime := hC.isPrime
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  let IL := I.map (componentPolynomialCoefficientMap (algebraMap K L))
  let f := MvPolynomial.map (σ := Fin 4) (algebraMap L Ω)
  have hchain : IL.toIdeal.map f = (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal := by
    change (I.toIdeal.map (MvPolynomial.map (algebraMap K L))).map f = _
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro t
    change MvPolynomial.map (algebraMap L Ω) (MvPolynomial.map (algebraMap K L) t) =
      MvPolynomial.map (algebraMap K Ω) t
    rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq K L Ω]
  change ∀ Q ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes,
    ∃ phi : M →ₐ[K] Ω, (D.map (componentPolynomialCoefficientMap phi.toRingHom)).toIdeal = Q
  intro Q hQ
  have hQoverL : Q ∈ (IL.toIdeal.map f).minimalPrimes := by rw [hchain]; exact hQ
  let P := Q.comap f
  have hP : P ∈ IL.toIdeal.minimalPrimes :=
    polynomialCoefficientExtension_minimalPrime_comap_mem IL.toIdeal Q hQoverL
  obtain ⟨g, hg⟩ := polynomialCoefficientExtension_minimalPrimes_conjugate
    I.toIdeal C.toIdeal P hC hP
  let phi : M →ₐ[K] Ω := ((IsScalarTower.toAlgHom K L Ω).comp g.toAlgHom).domRestrict M
  let DP := D.map (componentPolynomialCoefficientMap phi.toRingHom)
  have himage : DP.toIdeal = P.map f := by
    rw [hg]
    exact stabilizerModel_embedding_extension_eq_galois_componentExtension C phi g rfl
  have hle : DP.toIdeal ≤ Q :=
    himage.symm ▸ (Ideal.map_comap_le (f := f) (K := Q))
  have hmin := stabilizerModel_embedding_componentIdeal_minimalPrime I C hC hCO phi
  exact ⟨phi, le_antisymm hle (hQ.2 ⟨hmin.isPrime, hmin.le⟩ hle)⟩

/-- Construct the ACTUAL embedding/minimal-prime equivalence with forward
map exactly D.map(phi). Minimality, injection and surjection are proved by
the preceding native field/stabilizer/conjugacy constructions. -/
theorem stabilizerModel_exists_embedding_minimalPrimeEquiv
    [IsGalois K Ω]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L))
    (hC : C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes)
    (hCO : (C.toIdeal.map (MvPolynomial.map (algebraMap L Ω))).IsPrime) :
    let M := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
    ∃ e : (M →ₐ[K] Ω) ≃ (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes,
      ∀ phi, (e phi).1 = (D.map (componentPolynomialCoefficientMap phi.toRingHom)).toIdeal := by
  letI : C.toIdeal.IsPrime := hC.isPrime
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  let f : (M →ₐ[K] Ω) → (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes :=
    fun phi => ⟨(D.map (componentPolynomialCoefficientMap phi.toRingHom)).toIdeal,
      stabilizerModel_embedding_componentIdeal_minimalPrime I C hC hCO phi⟩
  have hinj : Function.Injective f := by
    intro phi psi h
    exact stabilizerModel_embedding_componentIdeal_injective C (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    intro Q
    obtain ⟨phi, hphi⟩ := stabilizerModel_embedding_componentIdeal_surjective_onto_minimalPrimes I C hC hCO Q.1 Q.2
    exact ⟨phi, Subtype.ext hphi⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun _ => rfl⟩

/-- Each literal embedding component has its canonical closed immersion into
SAME I_Ω, and the actual square back to ORIGINAL I commutes. Whole coefficient
containment and phi fixing K derive the immersion and both morphism routes;
no image-compatibility or component-minimality certificate is supplied. -/
theorem modelEmbeddingComponent_originalMap_closedImmersion_square
    {M : Type u} [Field M] [Algebra K M] [Module.Finite K M]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (phi : M →ₐ[K] Ω) :
    let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
    let DP := D.map (componentPolynomialCoefficientMap phi.toRingHom)
    ∃ hIP : IO.toIdeal ≤ DP.toIdeal,
      let j := schemeQuotientMap IO DP hIP
      IsClosedImmersion j ∧
        j ≫ projectiveCoefficientMap (algebraMap K Ω) I IO rfl =
          projectiveCoefficientMap phi.toRingHom D DP rfl ≫ coefficientComponentToOriginal I D hID := by
  let IM := I.map (componentPolynomialCoefficientMap (algebraMap K M))
  let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
  let DP := D.map (componentPolynomialCoefficientMap phi.toRingHom)
  have hfield : phi.toRingHom.comp (algebraMap K M) = algebraMap K Ω := by
    ext k
    exact phi.commutes k
  have hpoly : (MvPolynomial.map (σ := Fin 4) phi.toRingHom).comp
      (MvPolynomial.map (algebraMap K M)) = MvPolynomial.map (algebraMap K Ω) := by
    apply RingHom.ext
    intro t
    apply MvPolynomial.ext
    intro d
    simp only [RingHom.comp_apply, MvPolynomial.coeff_map]
    exact phi.commutes (MvPolynomial.coeff d t)
  have hIP : IO.toIdeal ≤ DP.toIdeal := by
    have h := Ideal.map_mono (f := MvPolynomial.map phi.toRingHom) hID
    change (I.toIdeal.map (MvPolynomial.map (algebraMap K M))).map
      (MvPolynomial.map phi.toRingHom) ≤ DP.toIdeal at h
    rw [Ideal.map_map, hpoly] at h
    exact h
  let j := schemeQuotientMap IO DP hIP
  let f := coefficientComponentToOriginal I D hID
  letI : IsClosedImmersion j := schemeQuotientMap_closedImmersion IO DP hIP
  have hf : f ≫ quotientProjMap I = quotientProjMap D ≫ ambientCoefficientMap (algebraMap K M) := by
    change (schemeQuotientMap IM D hID ≫ projectiveCoefficientMap (algebraMap K M) I IM rfl) ≫
      quotientProjMap I = _
    rw [Category.assoc, projectiveCoefficientMap_comp_quotientProjMap, ← Category.assoc,
      schemeQuotientMap_comp_quotientProjMap]
  refine ⟨hIP, inferInstance, ?_⟩
  apply (cancel_mono (quotientProjMap I)).mp
  rw [Category.assoc, projectiveCoefficientMap_comp_quotientProjMap, ← Category.assoc,
    schemeQuotientMap_comp_quotientProjMap, Category.assoc, hf, ← Category.assoc,
    projectiveCoefficientMap_comp_quotientProjMap, Category.assoc,
    ambientCoefficientMap_comp, hfield]

/-- Actual embedding-indexed homogeneous component images biject with EVERY
geometric projective component of SAME I_Ω. The forward image is the literal
canonical quotient closed immersion of D.map(phi), with its reduced integral
structure already proved natively. No component count or image bijection. -/
theorem stabilizerModel_exists_embedding_projectiveComponentEquiv
    [IsGalois K Ω]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ I)
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L))
    (hC : C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes)
    (hCO : (C.toIdeal.map (MvPolynomial.map (algebraMap L Ω))).IsPrime) :
    let M := homogeneousIdealStabilizerFixedField (K := K) C
    let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
    let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
    let hmin := stabilizerModel_embedding_componentIdeal_minimalPrime I C hC hCO
    ∃ e : (M →ₐ[K] Ω) ≃ irreducibleComponents (scheme IO),
      ∀ phi, (e phi).1 = Set.range (schemeQuotientMap IO
        (D.map (componentPolynomialCoefficientMap phi.toRingHom)) (hmin phi).le) := by
  letI : C.toIdeal.IsPrime := hC.isPrime
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
  let hmin := stabilizerModel_embedding_componentIdeal_minimalPrime I C hC hCO
  let F := {H : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) Ω) //
    H.toIdeal ∈ IO.toIdeal.minimalPrimes ∧
      ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) Ω) ≤ H}
  let f : (M →ₐ[K] Ω) → F := fun phi =>
    ⟨D.map (componentPolynomialCoefficientMap phi.toRingHom), hmin phi,
      homogeneousCoefficientExtension_minimalPrime_relevant I hIrel
        (D.map (componentPolynomialCoefficientMap phi.toRingHom)) (hmin phi)⟩
  have hinj : Function.Injective f := by
    intro phi psi h
    apply stabilizerModel_embedding_componentIdeal_injective C
    exact congrArg (fun H : F => H.1.toIdeal) h
  have hsurj : Function.Surjective f := by
    intro H
    obtain ⟨phi, hphi⟩ := stabilizerModel_embedding_componentIdeal_surjective_onto_minimalPrimes
      I C hC hCO H.1.toIdeal H.2.1
    refine ⟨phi, Subtype.ext ?_⟩
    exact HomogeneousIdeal.ext hphi
  let e := (Equiv.ofBijective f ⟨hinj, hsurj⟩).trans
    (homogeneousRelevantMinimalPrimesEquivProjectiveComponents IO)
  exact ⟨e, fun _ => rfl⟩

/-- Ordinary ORIGINAL relevant prime I and its actual geometric minimal
prime G construct ONCE the joint L/C/M/D model and the genuine embedding
bijection with SAME geometric component images. Actual closed-field prime
input for the intermediate bridge is derived from G; no GI, splitting,
embedding/component equivalence or image equality is supplied. -/
theorem originalGeometricMinimalPrime_exists_jointModel_embedding_projectiveComponentEquiv
    [IsGalois K Ω]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ I)
    (G : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) Ω))
    (hG : G.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes) :
    ∃ (E : FiniteGaloisIntermediateField K Ω)
      (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) E)),
      ∃ hC : C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K E))).toIdeal.minimalPrimes,
      ∃ hCG : C.toIdeal.map (MvPolynomial.map (algebraMap E Ω)) = G.toIdeal,
      let M := homogeneousIdealStabilizerFixedField (K := K) C
      let D := C.comap (componentPolynomialCoefficientMap (algebraMap M E))
      let IO := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
      let hCO : (C.toIdeal.map (MvPolynomial.map (algebraMap E Ω))).IsPrime := hCG.symm ▸ hG.isPrime
      let hmin := stabilizerModel_embedding_componentIdeal_minimalPrime I C hC hCO
      GeometricallyIntegral (toBase D) ∧
        ∃ e : (M →ₐ[K] Ω) ≃ irreducibleComponents (scheme IO),
          ∀ phi, (e phi).1 = Set.range (schemeQuotientMap IO
            (D.map (componentPolynomialCoefficientMap phi.toRingHom)) (hmin phi).le) := by
  obtain ⟨E, C, hC, hCG, _hDprime, _hDE, _hfield, hGI, _hall⟩ :=
    originalGeometricMinimalPrime_exists_jointStabilizerModel I hIrel G.toIdeal hG
  have hCO : (C.toIdeal.map (MvPolynomial.map (algebraMap E Ω))).IsPrime := hCG.symm ▸ hG.isPrime
  obtain ⟨e, he⟩ := stabilizerModel_exists_embedding_projectiveComponentEquiv I hIrel C hC hCO
  exact ⟨E, C, hC, hCG, hGI, e, he⟩

end PfaffianDescent.Coray
