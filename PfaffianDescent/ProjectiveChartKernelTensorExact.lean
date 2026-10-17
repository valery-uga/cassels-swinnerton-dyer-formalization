import PfaffianDescent.RelativeIdealTensorExact
import PfaffianDescent.HomogeneousQuotientMap

/-!
# Exact parameter base change for projective quotient-chart kernels

A quotient of homogeneous ideals induces a surjection on every standard
projective chart. If the target chart is flat over the parameter ring, its
kernel remains embedded after arbitrary tensor change of parameters. In
particular, no flatness hypothesis is imposed on the new parameter algebra.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable {T B : Type u} [CommRing T] [AddCommGroup B] [Module T B]

/-- The quotient chart map as a morphism of algebras over the parameter
ring, with scalar actions selected from the respective structure maps. -/
noncomputable def chartQuotientAlgHom
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4) :
    letI : Algebra T (ChartRing I j) := (chartBaseMap I j).toAlgebra
    letI : SMul T (ChartRing I j) := Algebra.toSMul
    letI : Module T (ChartRing I j) := Algebra.toModule
    letI : Algebra T (ChartRing J j) := (chartBaseMap J j).toAlgebra
    letI : SMul T (ChartRing J j) := Algebra.toSMul
    letI : Module T (ChartRing J j) := Algebra.toModule
    ChartRing I j →ₐ[T] ChartRing J j := by
  letI : Algebra T (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul T (ChartRing I j) := Algebra.toSMul
  letI : Module T (ChartRing I j) := Algebra.toModule
  letI : Algebra T (ChartRing J j) := (chartBaseMap J j).toAlgebra
  letI : SMul T (ChartRing J j) := Algebra.toSMul
  letI : Module T (ChartRing J j) := Algebra.toModule
  exact { toRingHom := chartQuotientMap I J hIJ j
          commutes' := fun t => DFunLike.congr_fun
            (chartQuotientMap_chartBaseMap I J hIJ j) t }

/-- A relatively flat projective quotient-chart map has a kernel that stays
embedded after arbitrary parameter tensor change. The explicit instances
select the scalar action of the chart's structure map. -/
theorem chartQuotientMap_kernel_lTensor_injective_of_flat
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4)
    (hflat : ((chartQuotientMap I J hIJ j).comp (chartBaseMap I j)).Flat) :
    letI : Algebra T (ChartRing I j) := (chartBaseMap I j).toAlgebra
    letI : SMul T (ChartRing I j) := Algebra.toSMul
    letI : Module T (ChartRing I j) := Algebra.toModule
    Function.Injective
      ((((RingHom.ker (chartQuotientMap I J hIJ j)).restrictScalars T).subtype).lTensor B) := by
  letI : Algebra T (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul T (ChartRing I j) := Algebra.toSMul
  letI : Module T (ChartRing I j) := Algebra.toModule
  letI : Algebra T (ChartRing J j) := (chartBaseMap J j).toAlgebra
  letI : SMul T (ChartRing J j) := Algebra.toSMul
  letI : Module T (ChartRing J j) := Algebra.toModule
  let f : ChartRing I j →ₐ[T] ChartRing J j :=
    { toRingHom := chartQuotientMap I J hIJ j
      commutes' := fun t => DFunLike.congr_fun
        (chartQuotientMap_chartBaseMap I J hIJ j) t }
  haveI : Module.Flat T (ChartRing J j) := by
    rw [chartQuotientMap_chartBaseMap I J hIJ j] at hflat
    exact hflat
  exact relativeSurjectiveAlgebraHom_kernel_lTensor_injective
    f (chartQuotientMap_surjective I J hIJ j)

/-- The entire kernel of the tensor-changed quotient on a flat target chart
is the tensor extension of the original chart ideal. -/
noncomputable def chartQuotientMap_tensorKernelEquiv_of_flat
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4)
    (hflat : ((chartQuotientMap I J hIJ j).comp (chartBaseMap I j)).Flat) :
    letI : Algebra T (ChartRing I j) := (chartBaseMap I j).toAlgebra
    letI : SMul T (ChartRing I j) := Algebra.toSMul
    letI : Module T (ChartRing I j) := Algebra.toModule
    LinearMap.ker
        ((((RingHom.ker (chartQuotientMap I J hIJ j)).restrictScalars T).mkQ).lTensor B) ≃ₗ[T]
      B ⊗[T] ((RingHom.ker (chartQuotientMap I J hIJ j)).restrictScalars T) := by
  letI : Algebra T (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul T (ChartRing I j) := Algebra.toSMul
  letI : Module T (ChartRing I j) := Algebra.toModule
  letI : Algebra T (ChartRing J j) := (chartBaseMap J j).toAlgebra
  letI : SMul T (ChartRing J j) := Algebra.toSMul
  letI : Module T (ChartRing J j) := Algebra.toModule
  let f : ChartRing I j →ₐ[T] ChartRing J j :=
    { toRingHom := chartQuotientMap I J hIJ j
      commutes' := fun t => DFunLike.congr_fun
        (chartQuotientMap_chartBaseMap I J hIJ j) t }
  haveI : Module.Flat T (ChartRing J j) := by
    rw [chartQuotientMap_chartBaseMap I J hIJ j] at hflat
    exact hflat
  exact relativeSurjectiveAlgebraHom_tensorKernelEquiv
    f (chartQuotientMap_surjective I J hIJ j)

/-- This version uses the actual quotient chart algebra map in the target
kernel, avoiding passage through its canonical quotient presentation. -/
noncomputable def chartQuotientMap_actualTensorKernelEquiv_of_flat
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4)
    (hflat : ((chartQuotientMap I J hIJ j).comp (chartBaseMap I j)).Flat) :
    letI : Algebra T (ChartRing I j) := (chartBaseMap I j).toAlgebra
    letI : SMul T (ChartRing I j) := Algebra.toSMul
    letI : Module T (ChartRing I j) := Algebra.toModule
    letI : Algebra T (ChartRing J j) := (chartBaseMap J j).toAlgebra
    letI : SMul T (ChartRing J j) := Algebra.toSMul
    letI : Module T (ChartRing J j) := Algebra.toModule
    let f := chartQuotientAlgHom I J hIJ j
    LinearMap.ker (f.toLinearMap.lTensor B) ≃ₗ[T]
      B ⊗[T] ((RingHom.ker (chartQuotientMap I J hIJ j)).restrictScalars T) := by
  letI : Algebra T (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul T (ChartRing I j) := Algebra.toSMul
  letI : Module T (ChartRing I j) := Algebra.toModule
  letI : Algebra T (ChartRing J j) := (chartBaseMap J j).toAlgebra
  letI : SMul T (ChartRing J j) := Algebra.toSMul
  letI : Module T (ChartRing J j) := Algebra.toModule
  haveI : Module.Flat T (ChartRing J j) := by
    rw [chartQuotientMap_chartBaseMap I J hIJ j] at hflat
    exact hflat
  exact relativeSurjectiveAlgebraHom_actualTensorKernelEquiv
    (chartQuotientAlgHom I J hIJ j)
    (chartQuotientMap_surjective I J hIJ j)

end PfaffianDescent
