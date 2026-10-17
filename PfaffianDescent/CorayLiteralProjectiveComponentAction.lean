import PfaffianDescent.CorayHomogeneousProjectiveComponentBijection
import PfaffianDescent.CorayMinimalPrimeOrbitCount

/-!
# Literal projective coefficient transport of the same component images

The original extended curve's coefficient invariance is derived. The native
projective coefficient morphism transports canonical reduced-component images
by preimage, and its actual fixed-component condition is equivalent to the
WHOLE ideal coefficient stabilizer. No equivariance/stabilizer certificate is
supplied. Scheme coefficient maps are contravariant: preimage under g is the
covariant g action (equivalently image under the inverse scheme map).
SOURCE ONLY / UNVERIFIED: root alone compiles and audits.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped Pointwise
universe u
variable {K E : Type u} [Field K] [Field E] [Algebra K E]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] polynomialGaloisCoefficientAction

/-- The literal original homogeneous coefficient extension is invariant under
actual coefficient automorphisms fixing ORIGINAL K; no invariance premise. -/
theorem originalHomogeneousExtension_coefficient_stable
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (g : E ≃ₐ[K] E) :
    let J := I.map (componentPolynomialCoefficientMap (algebraMap K E))
    J.toIdeal.map (MvPolynomial.map g.toRingHom) = J.toIdeal := by
  let f := MvPolynomial.map (σ := Fin 4) (algebraMap K E)
  let a := MvPolynomial.map (σ := Fin 4) g.toRingHom
  have hcomp : a.comp f = f := by
    apply RingHom.ext
    intro q
    apply MvPolynomial.ext
    intro d
    dsimp only [a, f]
    simp only [RingHom.comp_apply, MvPolynomial.coeff_map]
    exact g.commutes (MvPolynomial.coeff d q)
  change (I.toIdeal.map f).map a = I.toIdeal.map f
  rw [Ideal.map_map, hcomp]

/-- The ACTUAL ambient projective coefficient map pulls back the ACTUAL zero
locus to the zero locus of the literal coefficient-extension ideal. The raw
ProjectiveSpectrum view avoids replacing the native scheme carrier. -/
theorem ambientCoefficientMap_preimage_homogeneousZeroLocus
    (f : E →+* E) (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E)) :
    let a : ProjectiveSpectrum (homogeneousSubmodule (Fin 4) E) →
        ProjectiveSpectrum (homogeneousSubmodule (Fin 4) E) :=
      fun x => ambientCoefficientMap (σ := Fin 4) f x
    a ⁻¹' ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) E) C.toIdeal =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) E)
        (C.map (componentPolynomialCoefficientMap f)).toIdeal := by
  ext x
  change C.toIdeal ≤ x.asHomogeneousIdeal.toIdeal.comap (MvPolynomial.map f) ↔
    C.toIdeal.map (MvPolynomial.map f) ≤ x.asHomogeneousIdeal.toIdeal
  exact Ideal.map_le_iff_le_comap.symm

/-- Literal projective coefficient preimage of the SAME canonical component
image is the canonical image of the WHOLE conjugate homogeneous ideal.
Invariance of the original curve and containment of the conjugate are derived.
This set transport is valid before imposing any component-count hypothesis. -/
theorem originalCurveCoefficient_preimage_componentRange
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E))
    (hC : C.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K E))).toIdeal.minimalPrimes)
    (g : E ≃ₐ[K] E) :
    let J := I.map (componentPolynomialCoefficientMap (algebraMap K E))
    let hJ := originalHomogeneousExtension_coefficient_stable I g
    let a := projectiveCoefficientMap g.toRingHom J J hJ
    let D := C.map (componentPolynomialCoefficientMap g.toRingHom)
    let hJD : J.toIdeal ≤ D.toIdeal := by
      rw [← hJ]
      exact Ideal.map_mono hC.1.2
    a ⁻¹' Set.range (schemeQuotientMap J C hC.1.2) =
      Set.range (schemeQuotientMap J D hJD) := by
  let J := I.map (componentPolynomialCoefficientMap (algebraMap K E))
  let hJ := originalHomogeneousExtension_coefficient_stable I g
  let a := projectiveCoefficientMap g.toRingHom J J hJ
  let D := C.map (componentPolynomialCoefficientMap g.toRingHom)
  have hJD : J.toIdeal ≤ D.toIdeal := by
    rw [← hJ]
    exact Ideal.map_mono hC.1.2
  let j := quotientProjMap J
  let jRaw : scheme J → ProjectiveSpectrum (homogeneousSubmodule (Fin 4) E) := fun x => j x
  have hjRaw : Topology.IsClosedEmbedding jRaw := j.isClosedEmbedding
  let bRaw : ProjectiveSpectrum (homogeneousSubmodule (Fin 4) E) →
      ProjectiveSpectrum (homogeneousSubmodule (Fin 4) E) :=
    fun x => ambientCoefficientMap (σ := Fin 4) g.toRingHom x
  have hImage (H : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E))
      (hJH : J.toIdeal ≤ H.toIdeal) :
      jRaw '' Set.range (schemeQuotientMap J H hJH) =
        ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) E) H.toIdeal := by
    change j '' Set.range (schemeQuotientMap J H hJH) = _
    rw [← Set.range_comp]
    change Set.range (schemeQuotientMap J H hJH ≫ j) = _
    rw [schemeQuotientMap_comp_quotientProjMap, range_quotientProjMap]
  have hpre (H : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E))
      (hJH : J.toIdeal ≤ H.toIdeal) :
      Set.range (schemeQuotientMap J H hJH) =
        jRaw ⁻¹' ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) E) H.toIdeal := by
    rw [← hImage H hJH, Set.preimage_image_eq _ hjRaw.injective]
  have hnat (x : scheme J) : jRaw (a x) = bRaw (jRaw x) := by
    exact congrArg (fun m : scheme J ⟶ Proj (homogeneousSubmodule (Fin 4) E) => m x)
      (projectiveCoefficientMap_comp_quotientProjMap g.toRingHom J J hJ)
  ext x
  change a x ∈ Set.range (schemeQuotientMap J C hC.1.2) ↔
    x ∈ Set.range (schemeQuotientMap J D hJD)
  rw [hpre C hC.1.2, hpre D hJD]
  change jRaw (a x) ∈ ProjectiveSpectrum.zeroLocus
    (homogeneousSubmodule (Fin 4) E) C.toIdeal ↔
      jRaw x ∈ ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 4) E) D.toIdeal
  rw [hnat]
  change jRaw x ∈ bRaw ⁻¹' ProjectiveSpectrum.zeroLocus
    (homogeneousSubmodule (Fin 4) E) C.toIdeal ↔ _
  rw [ambientCoefficientMap_preimage_homogeneousZeroLocus]

/-- The actual whole-ideal stabilizer is precisely the fixed-component
condition for the native projective coefficient morphism on the SAME reduced
component image. Component identification/injectivity is the accepted013
constructed bijection, and conjugate minimality/relevance are derived. -/
theorem originalCurveCoefficient_component_stabilizer_iff
    [FiniteDimensional K E] [IsGalois K E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ I)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E))
    (hC : C.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K E))).toIdeal.minimalPrimes)
    (g : E ≃ₐ[K] E) :
    let J := I.map (componentPolynomialCoefficientMap (algebraMap K E))
    let hJ := originalHomogeneousExtension_coefficient_stable I g
    let a := projectiveCoefficientMap g.toRingHom J J hJ
    g ∈ homogeneousIdealCoefficientStabilizer (K := K) C ↔
      a ⁻¹' Set.range (schemeQuotientMap J C hC.1.2) =
        Set.range (schemeQuotientMap J C hC.1.2) := by
  dsimp only
  let J := I.map (componentPolynomialCoefficientMap (algebraMap K E))
  let D := C.map (componentPolynomialCoefficientMap g.toRingHom)
  have hDmin : D.toIdeal ∈ J.toIdeal.minimalPrimes := by
    change g • C.toIdeal ∈ (I.toIdeal.map (MvPolynomial.map (algebraMap K E))).minimalPrimes
    rw [← polynomialCoefficientExtension_minimalPrimes_eq_orbit I.toIdeal C.toIdeal hC]
    exact ⟨g, rfl⟩
  have hCrel := homogeneousCoefficientExtension_minimalPrime_relevant I hIrel C hC
  have hDrel := homogeneousCoefficientExtension_minimalPrime_relevant I hIrel D hDmin
  rw [originalCurveCoefficient_preimage_componentRange I C hC g]
  have hiff : g ∈ homogeneousIdealCoefficientStabilizer (K := K) C ↔ D = C := by
    change g ∈ MulAction.stabilizer (E ≃ₐ[K] E) C.toIdeal ↔ D = C
    rw [MulAction.mem_stabilizer_iff]
    change D.toIdeal = C.toIdeal ↔ D = C
    exact ⟨HomogeneousIdeal.ext, congrArg HomogeneousIdeal.toIdeal⟩
  rw [hiff]
  constructor
  · intro h
    have hEq :
        (⟨D, hDmin, hDrel⟩ :
          {H : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E) //
            H.toIdeal ∈ J.toIdeal.minimalPrimes ∧
              ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) E) ≤ H}) =
          ⟨C, hC, hCrel⟩ := Subtype.ext h
    exact congrArg Subtype.val
      (congrArg (homogeneousRelevantMinimalPrimesEquivProjectiveComponents J) hEq)
  · intro h
    have hEq :
        homogeneousRelevantMinimalPrimesEquivProjectiveComponents J ⟨D, hDmin, hDrel⟩ =
          homogeneousRelevantMinimalPrimesEquivProjectiveComponents J ⟨C, hC, hCrel⟩ :=
      Subtype.ext h
    exact congrArg Subtype.val
      ((homogeneousRelevantMinimalPrimesEquivProjectiveComponents J).injective hEq)

end PfaffianDescent.Coray
