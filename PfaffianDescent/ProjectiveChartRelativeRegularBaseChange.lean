import PfaffianDescent.RelativeRegularBaseChange
import PfaffianDescent.ProjectiveChartTensorBaseChange
import PfaffianDescent.ProjectiveChartKernelTensorExact

/-!
# Regularity of a projective chart equation after relative base change

The actual coefficient-changed projective chart is the tensor product
of the original chart with the new coefficient ring. Relative flatness
of the principal quotient therefore keeps its equation regular under
arbitrary coefficient change.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct nonZeroDivisors

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- If the original chart equation is regular and its quotient is flat
over the coefficient ring, its image is regular on every actual
coefficient-changed chart. The coefficient map need not be flat. -/
theorem chartCoefficientMap_regular_of_flat_principal_quotient
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (j : Fin 4) (z : ChartRing I j) (hz : IsRegular z)
    (hflat :
      letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
      Module.Flat R (ChartRing I j ⧸ Ideal.span ({z} : Set (ChartRing I j)))) :
    IsRegular
      (chartCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
        (coefficientChangedHomogeneousIdeal_toIdeal f I) j z) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul R (ChartRing I j) := Algebra.toSMul
  letI : Module R (ChartRing I j) := Algebra.toModule
  letI : Module.Flat R
      (ChartRing I j ⧸ Ideal.span ({z} : Set (ChartRing I j))) := hflat
  let e := chartCoefficientTensorEquiv f I j
  have ht : IsRegular (1 ⊗ₜ[R] z : S ⊗[R] ChartRing I j) :=
    tensor_regular_of_flat_principal_quotient z hz
  have he : IsRegular (e (1 ⊗ₜ[R] z : S ⊗[R] ChartRing I j)) := by
    apply isRegular_iff_mem_nonZeroDivisors.mpr
    have h := isRegular_iff_mem_nonZeroDivisors.mp ht
    have h' := mem_nonZeroDivisors_of_injective
      (f := e.symm.toRingHom) (x := e (1 ⊗ₜ[R] z : S ⊗[R] ChartRing I j))
      e.symm.injective (by
        change e.symm (e (1 ⊗ₜ[R] z : S ⊗[R] ChartRing I j)) ∈
          nonZeroDivisors (S ⊗[R] ChartRing I j)
        simpa only [e.symm_apply_apply] using h)
    exact h'
  rw [chartCoefficientTensorEquiv_includeRight] at he
  exact he

/-- Relative flatness of the actual quotient chart makes a regular
principal chart equation regular after every coefficient change. -/
theorem chartCoefficientMap_regular_of_flat_quotientChart
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4)
    (z : ChartRing I j) (hz : IsRegular z)
    (hker : RingHom.ker (chartQuotientMap I J hIJ j) =
      Ideal.span ({z} : Set (ChartRing I j)))
    (hflat : ((chartQuotientMap I J hIJ j).comp (chartBaseMap I j)).Flat) :
    IsRegular
      (chartCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
        (coefficientChangedHomogeneousIdeal_toIdeal f I) j z) := by
  letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul R (ChartRing I j) := Algebra.toSMul
  letI : Module R (ChartRing I j) := Algebra.toModule
  letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
  letI : SMul R (ChartRing J j) := Algebra.toSMul
  letI : Module R (ChartRing J j) := Algebra.toModule
  haveI : Module.Flat R (ChartRing J j) := by
    rw [chartQuotientMap_chartBaseMap I J hIJ j] at hflat
    exact hflat
  have hq : Module.Flat R
      (ChartRing I j ⧸ RingHom.ker (chartQuotientMap I J hIJ j)) :=
    relativeSurjectiveAlgebraHom_quotientKer_flat
      (chartQuotientAlgHom I J hIJ j)
      (chartQuotientMap_surjective I J hIJ j)
  have hp : Module.Flat R
      (ChartRing I j ⧸ Ideal.span ({z} : Set (ChartRing I j))) := by
    rw [← hker]
    exact hq
  exact chartCoefficientMap_regular_of_flat_principal_quotient
    f I j z hz hp

end PfaffianDescent
