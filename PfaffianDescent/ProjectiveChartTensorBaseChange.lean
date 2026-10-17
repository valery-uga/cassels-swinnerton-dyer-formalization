import PfaffianDescent.ProjectiveChartQuotientCoefficientNaturality
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Tensor presentation of projective chart coefficient change

The categorical chart pushout is identified with the algebraic tensor
product over the coefficient ring.
-/

namespace PfaffianDescent

open CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An actual projective chart after coefficient change is the tensor
product of the original chart with the new coefficient ring. -/
noncomputable def chartCoefficientTensorEquiv
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (j : Fin 4) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
    letI : SMul R (ChartRing I j) := Algebra.toSMul
    letI : Module R (ChartRing I j) := Algebra.toModule
    S ⊗[R] ChartRing I j ≃+*
      ChartRing (coefficientChangedHomogeneousIdeal f I) j := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul R (ChartRing I j) := Algebra.toSMul
  letI : Module R (ChartRing I j) := Algebra.toModule
  exact ((CommRingCat.isPushout_tensorProduct R S (ChartRing I j)).flip.isoIsPushout
    _ _ (isPushout_chartCoefficientMap f I
      (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal_toIdeal f I) j)).commRingCatIsoToRingEquiv

/-- The tensor-chart equivalence sends an original-chart element to its
coefficient-changed image. -/
theorem chartCoefficientTensorEquiv_includeRight
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (j : Fin 4) (x : ChartRing I j) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
    letI : SMul R (ChartRing I j) := Algebra.toSMul
    letI : Module R (ChartRing I j) := Algebra.toModule
    chartCoefficientTensorEquiv f I j (1 ⊗ₜ[R] x) =
      chartCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
        (coefficientChangedHomogeneousIdeal_toIdeal f I) j x := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul R (ChartRing I j) := Algebra.toSMul
  letI : Module R (ChartRing I j) := Algebra.toModule
  let H := isPushout_chartCoefficientMap f I
    (coefficientChangedHomogeneousIdeal f I)
    (coefficientChangedHomogeneousIdeal_toIdeal f I) j
  have he : (chartCoefficientTensorEquiv f I j).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom =
      chartCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
        (coefficientChangedHomogeneousIdeal_toIdeal f I) j := by
    apply RingHom.ext
    intro y
    exact congrArg
      (fun m : CommRingCat.of (ChartRing I j) ⟶
          CommRingCat.of (ChartRing (coefficientChangedHomogeneousIdeal f I) j) => m y)
      ((CommRingCat.isPushout_tensorProduct R S (ChartRing I j)).flip.inl_isoIsPushout_hom
        _ _ H)
  exact DFunLike.congr_fun he x

/-- The tensor-chart equivalence sends a new coefficient to the base-map
image of that coefficient on the changed chart. -/
theorem chartCoefficientTensorEquiv_includeLeft
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (j : Fin 4) (s : S) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
    letI : SMul R (ChartRing I j) := Algebra.toSMul
    letI : Module R (ChartRing I j) := Algebra.toModule
    chartCoefficientTensorEquiv f I j (s ⊗ₜ[R] 1) =
      chartBaseMap (coefficientChangedHomogeneousIdeal f I) j s := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul R (ChartRing I j) := Algebra.toSMul
  letI : Module R (ChartRing I j) := Algebra.toModule
  let H := isPushout_chartCoefficientMap f I
    (coefficientChangedHomogeneousIdeal f I)
    (coefficientChangedHomogeneousIdeal_toIdeal f I) j
  have he : (chartCoefficientTensorEquiv f I j).toRingHom.comp
      Algebra.TensorProduct.includeLeftRingHom =
      chartBaseMap (coefficientChangedHomogeneousIdeal f I) j := by
    apply RingHom.ext
    intro y
    exact congrArg
      (fun m : CommRingCat.of S ⟶
          CommRingCat.of (ChartRing (coefficientChangedHomogeneousIdeal f I) j) => m y)
      ((CommRingCat.isPushout_tensorProduct R S (ChartRing I j)).flip.inr_isoIsPushout_hom
        _ _ H)
  exact DFunLike.congr_fun he s

/-- The tensor-chart equivalence on a pure tensor is multiplication of
the new coefficient and the changed old-chart element. -/
theorem chartCoefficientTensorEquiv_tmul
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (j : Fin 4) (s : S) (x : ChartRing I j) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
    letI : SMul R (ChartRing I j) := Algebra.toSMul
    letI : Module R (ChartRing I j) := Algebra.toModule
    chartCoefficientTensorEquiv f I j (s ⊗ₜ[R] x) =
      chartBaseMap (coefficientChangedHomogeneousIdeal f I) j s *
        chartCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
          (coefficientChangedHomogeneousIdeal_toIdeal f I) j x := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul R (ChartRing I j) := Algebra.toSMul
  letI : Module R (ChartRing I j) := Algebra.toModule
  calc
    chartCoefficientTensorEquiv f I j (s ⊗ₜ[R] x) =
        chartCoefficientTensorEquiv f I j
          ((s ⊗ₜ[R] 1) * (1 ⊗ₜ[R] x)) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    _ = chartCoefficientTensorEquiv f I j (s ⊗ₜ[R] 1) *
        chartCoefficientTensorEquiv f I j (1 ⊗ₜ[R] x) := map_mul _ _ _
    _ = _ := by
      rw [chartCoefficientTensorEquiv_includeLeft,
        chartCoefficientTensorEquiv_includeRight]

end PfaffianDescent
