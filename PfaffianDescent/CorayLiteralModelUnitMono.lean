import PfaffianDescent.CorayModelIncidencePositive
import PfaffianDescent.CorayHomogeneousPrimeComponentGeometry
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! The SAME finite coefficient-model map has an injective structure-sheaf
unit and its LITERAL cokernel sequence is short exact. No normalization map,
unit-injectivity, short exactness, birationality or gluing bound is supplied. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Dominance over a reduced target and quasi-compactness imply native
unit injectivity through the installed genuine section-injectivity theorem. -/
theorem schemeUnitToPushforwardUnit_mono_of_reduced_dominant
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsReduced X] [IsDominant f] [QuasiCompact f] :
    Mono (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  letI : IsSchemeTheoreticallyDominant f :=
    IsSchemeTheoreticallyDominant.of_isDominant f
  apply (Scheme.Modules.toPresheafOfModules X).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  change Function.Injective
    ((SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val.app U)
  intro a b hab
  apply f.app_injective U.unop
  change (f.app U.unop a) = (f.app U.unop b) at hab
  exact hab

/-- Original prime/relevance and actual minimality over I_M derive native
unit mono for exactly coefficientComponentToOriginal I D hDmin.le. -/
theorem originalPrime_minimalCoefficientComponent_unitToPushforwardUnit_mono
    {K M : Type u} [Field K] [Field M] [Algebra K M] [Module.Finite K M]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ I)
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hDmin : D.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes) :
    let f := coefficientComponentToOriginal I D hDmin.le
    Mono (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  let f := coefficientComponentToOriginal I D hDmin.le
  let etaAmbient : ProjectiveSpectrum
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    ⟨I, inferInstance, hIrel⟩
  obtain ⟨x, _hx⟩ :=
    (quotientProjMap_mem_range_iff I etaAmbient).mpr (le_refl I.toIdeal)
  letI : IsIntegral (scheme I) :=
    homogeneousPrime_projectiveScheme_isIntegral I inferInstance x
  letI : IsFinite f :=
    (coefficientComponentToOriginal_finite_and_toBase I D hDmin.le).1
  have hSurj : Function.Surjective f :=
    originalPrime_minimalCoefficientComponentToOriginal_surjective I hIrel D hDmin
  letI : IsDominant f := ⟨hSurj.denseRange⟩
  exact schemeUnitToPushforwardUnit_mono_of_reduced_dominant f

/-- The actual coefficient map's structure-sheaf unit, pushforward unit
and SAME categorical cokernel give an internally proved exact sequence. -/
theorem originalPrime_minimalCoefficientComponent_unitCokernelSequence_shortExact
    {K M : Type u} [Field K] [Field M] [Algebra K M] [Module.Finite K M]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ I)
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hDmin : D.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes) :
    let f := coefficientComponentToOriginal I D hDmin.le
    (ShortComplex.cokernelSequence (C := (scheme I).Modules)
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).ShortExact := by
  let f := coefficientComponentToOriginal I D hDmin.le
  let a := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  letI : Mono a :=
    originalPrime_minimalCoefficientComponent_unitToPushforwardUnit_mono I hIrel D hDmin
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact a)
    (by change Mono a; infer_instance) (by infer_instance)

end PfaffianDescent.Coray
