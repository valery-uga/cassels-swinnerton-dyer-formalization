import PfaffianDescent.ProjectiveChartTensorQuotientNaturality
import PfaffianDescent.RelativeTensorMapKernelComparison

/-!
# Relative ideal base change on projective quotient charts

When a quotient projective chart is flat over its parameter ring, the
ideal on every coefficient-changed chart is additively equivalent to the
tensor extension of the original chart ideal. No flatness is required
of the coefficient change.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ideal of the actual coefficient-changed quotient chart is the
base-changed original chart ideal, for any coefficient map, provided
its quotient chart is relatively flat. -/
noncomputable def chartQuotientMap_changedKernelTensorAddEquiv_of_flat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4)
    (hflat : ((chartQuotientMap I J hIJ j).comp (chartBaseMap I j)).Flat) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
    letI : SMul R (ChartRing I j) := Algebra.toSMul
    letI : Module R (ChartRing I j) := Algebra.toModule
    letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
    letI : SMul R (ChartRing J j) := Algebra.toSMul
    letI : Module R (ChartRing J j) := Algebra.toModule
    S ⊗[R] ((RingHom.ker (chartQuotientMap I J hIJ j)).restrictScalars R) ≃+
      RingHom.ker (chartQuotientMap (coefficientChangedHomogeneousIdeal f I)
        (coefficientChangedHomogeneousIdeal f J)
        (coefficientChangedHomogeneousIdeal_mono f I J hIJ) j) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul R (ChartRing I j) := Algebra.toSMul
  letI : Module R (ChartRing I j) := Algebra.toModule
  letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
  letI : SMul R (ChartRing J j) := Algebra.toSMul
  letI : Module R (ChartRing J j) := Algebra.toModule
  haveI : Module.Flat R (ChartRing J j) := by
    rw [chartQuotientMap_chartBaseMap I J hIJ j] at hflat
    exact hflat
  exact (relativeSurjectiveAlgebraHom_ringTensorKernelEquiv (S := S)
    (chartQuotientAlgHom I J hIJ j)
    (chartQuotientMap_surjective I J hIJ j)).symm.toAddEquiv.trans
      (chartQuotientMap_tensorKernelAddEquiv_changedKernel f I J hIJ j)

/-- The chart ideal comparison is canonical on pure tensors: a changed
coefficient multiplies the image of an original ideal element. -/
theorem chartQuotientMap_changedKernelTensorAddEquiv_tmul
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4)
    (hflat : ((chartQuotientMap I J hIJ j).comp (chartBaseMap I j)).Flat)
    (s : S) (x : RingHom.ker (chartQuotientMap I J hIJ j)) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
    letI : SMul R (ChartRing I j) := Algebra.toSMul
    letI : Module R (ChartRing I j) := Algebra.toModule
    letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
    letI : SMul R (ChartRing J j) := Algebra.toSMul
    letI : Module R (ChartRing J j) := Algebra.toModule
    ((chartQuotientMap_changedKernelTensorAddEquiv_of_flat f I J hIJ j hflat
      (s ⊗ₜ[R] (x : (RingHom.ker (chartQuotientMap I J hIJ j)).restrictScalars R)) :
        ChartRing (coefficientChangedHomogeneousIdeal f I) j) =
      chartBaseMap (coefficientChangedHomogeneousIdeal f I) j s *
        chartCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
          (coefficientChangedHomogeneousIdeal_toIdeal f I) j x.1) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul R (ChartRing I j) := Algebra.toSMul
  letI : Module R (ChartRing I j) := Algebra.toModule
  letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
  letI : SMul R (ChartRing J j) := Algebra.toSMul
  letI : Module R (ChartRing J j) := Algebra.toModule
  haveI : Module.Flat R (ChartRing J j) := by
    rw [chartQuotientMap_chartBaseMap I J hIJ j] at hflat
    exact hflat
  change chartCoefficientTensorEquiv f I j
      (((relativeSurjectiveAlgebraHom_ringTensorKernelEquiv (S := S)
        (chartQuotientAlgHom I J hIJ j)
        (chartQuotientMap_surjective I J hIJ j)).symm
        (s ⊗ₜ[R] (x : (RingHom.ker (chartQuotientMap I J hIJ j)).restrictScalars R))) :
          RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R S)
            (chartQuotientAlgHom I J hIJ j)).toRingHom).1 = _
  have htmul := relativeSurjectiveAlgebraHom_ringTensorKernelEquiv_symm_tmul
    (S := S) (chartQuotientAlgHom I J hIJ j)
    (chartQuotientMap_surjective I J hIJ j) s
    (x : (RingHom.ker (chartQuotientMap I J hIJ j)).restrictScalars R)
  rw [htmul, chartCoefficientTensorEquiv_tmul]

/-- The canonical chart-ideal base-change equivalence is linear over the
new coefficient ring. -/
noncomputable def chartQuotientMap_changedKernelTensorLinearEquiv_of_flat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4)
    (hflat : ((chartQuotientMap I J hIJ j).comp (chartBaseMap I j)).Flat) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
    letI : SMul R (ChartRing I j) := Algebra.toSMul
    letI : Module R (ChartRing I j) := Algebra.toModule
    letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
    letI : SMul R (ChartRing J j) := Algebra.toSMul
    letI : Module R (ChartRing J j) := Algebra.toModule
    letI : Module S (RingHom.ker (chartQuotientMap
        (coefficientChangedHomogeneousIdeal f I)
        (coefficientChangedHomogeneousIdeal f J)
        (coefficientChangedHomogeneousIdeal_mono f I J hIJ) j)) :=
      Module.compHom _ (chartBaseMap (coefficientChangedHomogeneousIdeal f I) j)
    S ⊗[R] ((RingHom.ker (chartQuotientMap I J hIJ j)).restrictScalars R) ≃ₗ[S]
      RingHom.ker (chartQuotientMap (coefficientChangedHomogeneousIdeal f I)
        (coefficientChangedHomogeneousIdeal f J)
        (coefficientChangedHomogeneousIdeal_mono f I J hIJ) j) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul R (ChartRing I j) := Algebra.toSMul
  letI : Module R (ChartRing I j) := Algebra.toModule
  letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
  letI : SMul R (ChartRing J j) := Algebra.toSMul
  letI : Module R (ChartRing J j) := Algebra.toModule
  letI : Module S (RingHom.ker (chartQuotientMap
      (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal f J)
      (coefficientChangedHomogeneousIdeal_mono f I J hIJ) j)) :=
    Module.compHom _ (chartBaseMap (coefficientChangedHomogeneousIdeal f I) j)
  let e := chartQuotientMap_changedKernelTensorAddEquiv_of_flat f I J hIJ j hflat
  apply e.toLinearEquiv
  intro t z
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
      apply Subtype.ext
      change (e ((t * s) ⊗ₜ[R] x)).1 =
        chartBaseMap (coefficientChangedHomogeneousIdeal f I) j t *
          (e (s ⊗ₜ[R] x)).1
      calc
        (e ((t * s) ⊗ₜ[R] x)).1 =
            chartBaseMap (coefficientChangedHomogeneousIdeal f I) j (t * s) *
              chartCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
                (coefficientChangedHomogeneousIdeal_toIdeal f I) j x.1 := by
          exact chartQuotientMap_changedKernelTensorAddEquiv_tmul
            f I J hIJ j hflat (t * s) x
        _ = chartBaseMap (coefficientChangedHomogeneousIdeal f I) j t *
            (chartBaseMap (coefficientChangedHomogeneousIdeal f I) j s *
              chartCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
                (coefficientChangedHomogeneousIdeal_toIdeal f I) j x.1) := by
          rw [map_mul, mul_assoc]
        _ = chartBaseMap (coefficientChangedHomogeneousIdeal f I) j t *
            (e (s ⊗ₜ[R] x)).1 := by
          exact congrArg
            (fun y => chartBaseMap (coefficientChangedHomogeneousIdeal f I) j t * y)
            (chartQuotientMap_changedKernelTensorAddEquiv_tmul
              f I J hIJ j hflat s x).symm
  | add x y hx hy => simpa only [smul_add, map_add] using congrArg₂ (· + ·) hx hy

end PfaffianDescent
