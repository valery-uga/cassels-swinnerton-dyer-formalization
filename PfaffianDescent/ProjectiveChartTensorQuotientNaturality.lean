import PfaffianDescent.ProjectiveChartTensorBaseChange
import PfaffianDescent.ProjectiveChartKernelTensorExact
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Quotient maps under tensor presentation of projective charts

The tensor-changed quotient map agrees with the quotient map of the
coefficient-changed homogeneous ideals under the canonical chart
base-change equivalences.
-/

namespace PfaffianDescent

open CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The square between tensor-changed and actual coefficient-changed
projective quotient charts commutes. -/
theorem chartCoefficientTensorEquiv_quotient_comm
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
    letI : SMul R (ChartRing I j) := Algebra.toSMul
    letI : Module R (ChartRing I j) := Algebra.toModule
    letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
    letI : SMul R (ChartRing J j) := Algebra.toSMul
    letI : Module R (ChartRing J j) := Algebra.toModule
    (chartQuotientMap (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal f J)
      (coefficientChangedHomogeneousIdeal_mono f I J hIJ) j).comp
      (chartCoefficientTensorEquiv f I j).toRingHom =
    (chartCoefficientTensorEquiv f J j).toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R S)
        (chartQuotientAlgHom I J hIJ j)).toRingHom := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul R (ChartRing I j) := Algebra.toSMul
  letI : Module R (ChartRing I j) := Algebra.toModule
  letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
  letI : SMul R (ChartRing J j) := Algebra.toSMul
  letI : Module R (ChartRing J j) := Algebra.toModule
  apply RingHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s a =>
      change chartQuotientMap (coefficientChangedHomogeneousIdeal f I)
          (coefficientChangedHomogeneousIdeal f J)
          (coefficientChangedHomogeneousIdeal_mono f I J hIJ) j
          (chartCoefficientTensorEquiv f I j (s ⊗ₜ[R] a)) =
        chartCoefficientTensorEquiv f J j
          ((Algebra.TensorProduct.map (AlgHom.id R S)
            (chartQuotientAlgHom I J hIJ j)) (s ⊗ₜ[R] a))
      rw [chartCoefficientTensorEquiv_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        chartCoefficientTensorEquiv_tmul, map_mul]
      rw [show chartQuotientMap (coefficientChangedHomogeneousIdeal f I)
          (coefficientChangedHomogeneousIdeal f J)
          (coefficientChangedHomogeneousIdeal_mono f I J hIJ) j
          (chartBaseMap (coefficientChangedHomogeneousIdeal f I) j s) =
          chartBaseMap (coefficientChangedHomogeneousIdeal f J) j s from
        DFunLike.congr_fun (chartQuotientMap_chartBaseMap
          (coefficientChangedHomogeneousIdeal f I)
          (coefficientChangedHomogeneousIdeal f J)
          (coefficientChangedHomogeneousIdeal_mono f I J hIJ) j) s]
      change chartBaseMap (coefficientChangedHomogeneousIdeal f J) j s *
          chartQuotientMap (coefficientChangedHomogeneousIdeal f I)
            (coefficientChangedHomogeneousIdeal f J)
            (coefficientChangedHomogeneousIdeal_mono f I J hIJ) j
            (chartCoefficientMap f I (coefficientChangedHomogeneousIdeal f I)
              (coefficientChangedHomogeneousIdeal_toIdeal f I) j a) =
        chartBaseMap (coefficientChangedHomogeneousIdeal f J) j s *
          chartCoefficientMap f J (coefficientChangedHomogeneousIdeal f J)
            (coefficientChangedHomogeneousIdeal_toIdeal f J) j
            (chartQuotientMap I J hIJ j a)
      have hcomm := DFunLike.congr_fun
        (chartQuotientMap_coefficientChanged_comm f I J hIJ j) a
      simpa only [RingHom.comp_apply] using congrArg
        (fun y => chartBaseMap (coefficientChangedHomogeneousIdeal f J) j s * y) hcomm
  | add x y hx hy =>
      simp only [RingHom.comp_apply, map_add]
      simpa only [RingHom.comp_apply] using congrArg₂ (· + ·) hx hy

/-- A commuting square with ring equivalences carries the source kernel
onto the target kernel. -/
private theorem ker_eq_map_ker_of_equiv_square
    {A A' C C' : Type u}
    [CommRing A] [CommRing A'] [CommRing C] [CommRing C']
    (eA : A ≃+* A') (eC : C ≃+* C')
    (q : A →+* C) (q' : A' →+* C')
    (h : q'.comp eA.toRingHom = eC.toRingHom.comp q) :
    RingHom.ker q' = (RingHom.ker q).map eA.toRingHom := by
  ext b
  rw [Ideal.mem_map_iff_of_surjective eA.toRingHom eA.surjective]
  constructor
  · intro hb
    change q' b = 0 at hb
    refine ⟨eA.symm b, ?_, by simp⟩
    have hc : eC.toRingHom (q (eA.symm b)) = 0 := by
      have hh := DFunLike.congr_fun h (eA.symm b)
      calc
        eC.toRingHom (q (eA.symm b)) = q' (eA.toRingHom (eA.symm b)) := by
          simpa only [RingHom.comp_apply] using hh.symm
        _ = q' b := by simp
        _ = 0 := hb
    apply eC.injective
    change eC.toRingHom (q (eA.symm b)) = eC.toRingHom 0
    simpa only [map_zero] using hc
  · rintro ⟨a, ha, rfl⟩
    change q a = 0 at ha
    have hh := DFunLike.congr_fun h a
    change q' (eA a) = 0
    rw [show q' (eA a) = eC (q a) from hh]
    simp [ha]

/-- The kernel ideal on the actual coefficient-changed chart is the image
of the kernel of the tensor-changed quotient chart map. -/
theorem chartQuotientMap_changed_ker_eq_tensorKer_map
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
    letI : SMul R (ChartRing I j) := Algebra.toSMul
    letI : Module R (ChartRing I j) := Algebra.toModule
    letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
    letI : SMul R (ChartRing J j) := Algebra.toSMul
    letI : Module R (ChartRing J j) := Algebra.toModule
    RingHom.ker (chartQuotientMap (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal f J)
      (coefficientChangedHomogeneousIdeal_mono f I J hIJ) j) =
    (RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R S)
      (chartQuotientAlgHom I J hIJ j)).toRingHom).map
        (chartCoefficientTensorEquiv f I j).toRingHom := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : SMul R (ChartRing I j) := Algebra.toSMul
  letI : Module R (ChartRing I j) := Algebra.toModule
  letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
  letI : SMul R (ChartRing J j) := Algebra.toSMul
  letI : Module R (ChartRing J j) := Algebra.toModule
  exact ker_eq_map_ker_of_equiv_square
    (chartCoefficientTensorEquiv f I j)
    (chartCoefficientTensorEquiv f J j)
    (Algebra.TensorProduct.map (AlgHom.id R S)
      (chartQuotientAlgHom I J hIJ j)).toRingHom
    (chartQuotientMap (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal f J)
      (coefficientChangedHomogeneousIdeal_mono f I J hIJ) j)
    (chartCoefficientTensorEquiv_quotient_comm f I J hIJ j)

/-- A commuting square of ring equivalences restricts to an additive
equivalence of its kernel ideals. -/
private def kerAddEquiv_of_equiv_square
    {A A' C C' : Type u}
    [CommRing A] [CommRing A'] [CommRing C] [CommRing C']
    (eA : A ≃+* A') (eC : C ≃+* C')
    (q : A →+* C) (q' : A' →+* C')
    (h : q'.comp eA.toRingHom = eC.toRingHom.comp q) :
    RingHom.ker q ≃+ RingHom.ker q' where
  toFun x := ⟨eA x.1, by
    change q' (eA x.1) = 0
    have hh := DFunLike.congr_fun h x.1
    rw [show q' (eA x.1) = eC (q x.1) from hh]
    have hx : q x.1 = 0 := x.property
    simp [hx]⟩
  invFun y := ⟨eA.symm y.1, by
    change q (eA.symm y.1) = 0
    apply eC.injective
    change eC.toRingHom (q (eA.symm y.1)) = eC.toRingHom 0
    have hh := DFunLike.congr_fun h (eA.symm y.1)
    have hy : q' y.1 = 0 := y.property
    simpa only [RingHom.comp_apply, map_zero] using hh.symm.trans (by simpa using hy)⟩
  left_inv x := Subtype.ext (eA.symm_apply_apply x.1)
  right_inv y := Subtype.ext (eA.apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add eA x.1 y.1)

/-- The kernel ideals of the tensor-changed quotient map and the actual
coefficient-changed quotient chart map are canonically additively
equivalent. -/
noncomputable def chartQuotientMap_tensorKernelAddEquiv_changedKernel
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : Fin 4) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (ChartRing I j) := (chartBaseMap I j).toAlgebra
    letI : SMul R (ChartRing I j) := Algebra.toSMul
    letI : Module R (ChartRing I j) := Algebra.toModule
    letI : Algebra R (ChartRing J j) := (chartBaseMap J j).toAlgebra
    letI : SMul R (ChartRing J j) := Algebra.toSMul
    letI : Module R (ChartRing J j) := Algebra.toModule
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R S)
      (chartQuotientAlgHom I J hIJ j)).toRingHom ≃+
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
  exact kerAddEquiv_of_equiv_square
    (chartCoefficientTensorEquiv f I j)
    (chartCoefficientTensorEquiv f J j)
    (Algebra.TensorProduct.map (AlgHom.id R S)
      (chartQuotientAlgHom I J hIJ j)).toRingHom
    (chartQuotientMap (coefficientChangedHomogeneousIdeal f I)
      (coefficientChangedHomogeneousIdeal f J)
      (coefficientChangedHomogeneousIdeal_mono f I J hIJ) j)
    (chartCoefficientTensorEquiv_quotient_comm f I J hIJ j)

end PfaffianDescent
