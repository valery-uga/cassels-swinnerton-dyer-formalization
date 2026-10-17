import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualLocalFlat

/-! # Actual finite surface fibre coordinates give a flat local zero algebra -/
noncomputable section
namespace PfaffianDescent
open IsLocalRing RingTheory.Sequence
open scoped Pointwise
universe u v
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_pair_quotient_flat_of_regular_surface_fibre
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hdR : ringKrullDim R = 1) (t : R) (ht : maximalIdeal R = Ideal.span {t})
    (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra R A] [IsLocalHom (algebraMap R A)] [Module.Flat R A]
    [IsRegularLocalRing (A ⧸ Ideal.span {algebraMap R A t})]
    (hdA : ringKrullDim (A ⧸ Ideal.span {algebraMap R A t}) = 2)
    (a b : A) (ha : a ∈ maximalIdeal A) (hb : b ∈ maximalIdeal A)
    [IsArtinianRing ((A ⧸ Ideal.span {algebraMap R A t}) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.span {algebraMap R A t}) a,
        Ideal.Quotient.mk (Ideal.span {algebraMap R A t}) b} :
        Set (A ⧸ Ideal.span {algebraMap R A t})))] :
    Module.Flat R (A ⧸ Ideal.span ({a, b} : Set A)) := by
  letI := AllCharacteristics.isDomain_of_regularLocal_dim_one hdR
  have ht₀ : t ≠ 0 := by
    intro hzero
    have hm : maximalIdeal R = ⊥ := by simpa [hzero] using ht
    have hsf : (maximalIdeal R).spanFinrank = 0 := by rw [hm]; simp
    have he := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hsf, hdR] at he
    norm_num at he
  have htm : t ∈ maximalIdeal R := ht ▸ Ideal.subset_span (by simp)
  have hT : algebraMap R A t ∈ maximalIdeal A :=
    map_nonunit (algebraMap R A) t htm
  have htr : IsSMulRegular A (algebraMap R A t) := by
    apply (isSMulRegular_algebraMap_iff A).mpr
    apply (isSMulRegular_iff_right_eq_zero_of_smul).mpr
    intro x hx
    exact (smul_eq_zero.mp hx).resolve_left ht₀

  let B := A ⧸ Ideal.span {algebraMap R A t}
  let f := Ideal.Quotient.mk (Ideal.span {algebraMap R A t})
  letI : IsLocalHom f := IsLocalHom.of_surjective f Ideal.Quotient.mk_surjective
  have hregB := cubicClosedPointSerreFiniteZeroResidual_regular_pair_of_artinian_quotient
    B hdA (f a) (f b)
      (map_nonunit f a ha) (map_nonunit f b hb)
  have hregA : IsWeaklyRegular (R := A) B [a, b] := by
    apply (isWeaklyRegular_map_algebraMap_iff B B [a, b]).mp
    exact hregB.toIsWeaklyRegular
  have hquot := cubicClosedPointSerreFiniteZeroResidual_parameter_regular_on_pair_quotient
    A (algebraMap R A t) a b hT ha hb htr hregA
  have hquotR : IsSMulRegular (A ⧸ Ideal.span ({a, b} : Set A)) t := by
    exact (isSMulRegular_algebraMap_iff A).mp hquot
  exact cubicClosedPointSerreFiniteZeroResidual_flat_of_parameter_regular
    R hdR t ht (A ⧸ Ideal.span ({a, b} : Set A)) hquotR

end PfaffianDescent
