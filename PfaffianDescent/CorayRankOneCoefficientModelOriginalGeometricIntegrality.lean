import PfaffianDescent.CorayEntireModelIncidenceCycle
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! Degree-one coefficient models identify the SAME original prime scheme.
No regularity, constants rank, support, section, genus or chosen-point outcome
is used. Source only; ordinary checks and root acceptance remain required. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M] [Module.Finite K M]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- The actual structural map Spec M→Spec K is an isomorphism when the
original-K field degree is one; no inverse or scheme Iso is supplied. -/
theorem coefficientFieldSpectrum_isIso_of_finrank_one001
    (hOne : Module.finrank K M = 1) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap K M))) := by
  have hBij : Function.Bijective (algebraMap K M) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hOne
  let e := RingEquiv.ofBijective (algebraMap K M) hBij
  letI : IsIso (CommRingCat.ofHom (algebraMap K M)) := by
    change IsIso e.toCommRingCatIso.hom
    infer_instance
  infer_instance

/-- Actual rank-one coefficient extension of the ORIGINAL prime is prime,
so its SAME minimal component D is exactly that extension, not a radical
replacement or a separately selected existential model. -/
theorem coefficientMinimalComponent_eq_originalExtension_of_finrank_one001
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) M))
    (hDmin : D.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes)
    (hOne : Module.finrank K M = 1) :
    D = I.map (componentPolynomialCoefficientMap (algebraMap K M)) := by
  let IM := I.map (componentPolynomialCoefficientMap (algebraMap K M))
  have hBij : Function.Bijective (algebraMap K M) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hOne
  have hInj : Function.Injective (MvPolynomial.map (σ := Fin 4) (algebraMap K M)) :=
    MvPolynomial.map_injective _ hBij.1
  have hSurj : Function.Surjective (MvPolynomial.map (σ := Fin 4) (algebraMap K M)) :=
    MvPolynomial.map_surjective _ hBij.2
  have hKer : RingHom.ker (MvPolynomial.map (σ := Fin 4) (algebraMap K M)) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hInj
  letI : IM.toIdeal.IsPrime := by
    change (I.toIdeal.map (MvPolynomial.map (algebraMap K M))).IsPrime
    exact Ideal.map_isPrime_of_surjective hSurj (by rw [hKer]; exact bot_le)
  change D.toIdeal ∈ IM.toIdeal.minimalPrimes at hDmin
  rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hDmin
  exact HomogeneousIdeal.ext hDmin

/-- The SAME native coefficient-component map to ORIGINAL I is an
isomorphism, derived from rank-one field change and actual minimality. -/
theorem coefficientComponentToOriginal_isIso_of_finrank_one001
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) M))
    (hDmin : D.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes)
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (hOne : Module.finrank K M = 1) :
    IsIso (coefficientComponentToOriginal I D hID) := by
  have hD := coefficientMinimalComponent_eq_originalExtension_of_finrank_one001 I D hDmin hOne
  subst D
  let IM := I.map (componentPolynomialCoefficientMap (algebraMap K M))
  letI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap K M))) :=
    coefficientFieldSpectrum_isIso_of_finrank_one001 hOne
  letI : IsIso (projectiveCoefficientMap (algebraMap K M) I IM rfl) :=
    (isPullback_projectiveCoefficientMap (algebraMap K M) I IM rfl).isIso_fst_of_isIso
  have hSelf : schemeQuotientMap IM IM hID = 𝟙 (scheme IM) := by
    apply (cancel_mono (quotientProjMap IM)).mp
    rw [schemeQuotientMap_comp_quotientProjMap, Category.id_comp]
  letI : IsIso (schemeQuotientMap IM IM hID) := by
    rw [hSelf]
    infer_instance
  change IsIso (schemeQuotientMap IM IM hID ≫
    projectiveCoefficientMap (algebraMap K M) I IM rfl)
  infer_instance

/-- Geometric integrality of the actual rank-one SAME model D/M implies
geometric integrality of ORIGINAL I/K through its literal structural square.
No GI or normalization constants hypothesis on I is supplied. -/
theorem originalPrime_geometricallyIntegral_of_rank_one_coefficientMinimalModel001
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) M))
    (hDmin : D.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes)
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (hOne : Module.finrank K M = 1)
    (hGI : GeometricallyIntegral (toBase D)) : GeometricallyIntegral (toBase I) := by
  let f := coefficientComponentToOriginal I D hID
  let b := Spec.map (CommRingCat.ofHom (algebraMap K M))
  letI : IsIso b := coefficientFieldSpectrum_isIso_of_finrank_one001 hOne
  letI : IsIso f := coefficientComponentToOriginal_isIso_of_finrank_one001 I D hDmin hID hOne
  have hSquare : f ≫ toBase I = toBase D ≫ b :=
    (coefficientComponentToOriginal_finite_and_toBase I D hID).2
  letI : MorphismProperty.RespectsIso
      (@GeometricallyIntegral : MorphismProperty Scheme.{u}) := by
    rw [GeometricallyIntegral.eq_geometrically]
    infer_instance
  have hComp : GeometricallyIntegral (toBase D ≫ b) :=
    (MorphismProperty.cancel_right_of_respectsIso
      (@GeometricallyIntegral : MorphismProperty Scheme.{u}) (toBase D) b).mpr hGI
  have hLeft : GeometricallyIntegral (f ≫ toBase I) := hSquare.symm ▸ hComp
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@GeometricallyIntegral : MorphismProperty Scheme.{u}) f (toBase I)).mp hLeft

end PfaffianDescent.Coray
