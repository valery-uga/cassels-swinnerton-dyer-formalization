import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualRegularPair
import AllCharacteristics.RegularLocalLowDimension
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Local flatness from the regular finite surface fibre -/
noncomputable section
namespace PfaffianDescent
open IsLocalRing RingTheory.Sequence
open scoped Pointwise
universe u v
set_option backward.isDefEq.respectTransparency false

/-- Over an actual one-dimensional regular local ring, injectivity of its
maximal generator on a module implies flatness. -/
theorem cubicClosedPointSerreFiniteZeroResidual_flat_of_parameter_regular
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hd : ringKrullDim R = 1) (t : R) (ht : maximalIdeal R = Ideal.span {t})
    (M : Type v) [AddCommGroup M] [Module R M] (hreg : IsSMulRegular M t) :
    Module.Flat R M := by
  letI := AllCharacteristics.isDomain_of_regularLocal_dim_one hd
  letI := AllCharacteristics.valuationRing_of_regularLocal_dim_one hd
  have htf : Module.IsTorsionFree R M := Module.IsTorsionFree.of_smul_eq_zero (by
    intro r m hrm
    by_cases hr : r = 0
    · exact Or.inl hr
    · obtain ⟨n, w, hw, he⟩ :=
        AllCharacteristics.exists_pow_mul_unit_of_principal_maximalIdeal t ht r hr
      have hrreg : IsSMulRegular M r := by
        rw [he]
        exact (hreg.pow n).mul (hw.isSMulRegular M)
      exact Or.inr (hrreg.right_eq_zero_of_smul hrm))
  exact (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout (R := R) (M := M)).mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp htf)

/-- The residue-fibre pair may be moved before the base parameter in the
actual local Koszul sequence, making that parameter regular on the zero quotient. -/
theorem cubicClosedPointSerreFiniteZeroResidual_parameter_regular_on_pair_quotient
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (t a b : A) (ht : t ∈ maximalIdeal A) (ha : a ∈ maximalIdeal A)
    (hb : b ∈ maximalIdeal A) (htr : IsSMulRegular A t)
    (hab : IsWeaklyRegular (R := A) (A ⧸ Ideal.span {t}) [a, b]) :
    IsSMulRegular (A ⧸ Ideal.span ({a, b} : Set A)) t := by
  have heq : t • (⊤ : Submodule A A) = Ideal.span {t} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop t A ≃ₗ[A] A ⧸ Ideal.span {t} := Submodule.quotEquivOfEq _ _ heq
  have htab : IsWeaklyRegular A [t, a, b] :=
    ((e.isWeaklyRegular_congr [a, b]).mpr hab).cons htr
  have hreg : IsRegular A [t, a, b] :=
    IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal A (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact ht
      · exact ha
      · exact hb) htab
  have hperm : ([t, a, b] : List A).Perm [a, b, t] := by
    exact (List.Perm.swap t a [b]).symm.trans (List.Perm.cons a (List.Perm.swap t b []).symm)
  have habt := (IsLocalRing.isRegular_of_perm hreg hperm).toIsWeaklyRegular
  have htail := (isWeaklyRegular_append_iff A [a, b] [t]).mp habt
  have hI : Ideal.ofList [a, b] • (⊤ : Submodule A A) =
      Ideal.span ({a, b} : Set A) := by
    rw [smul_eq_mul, Ideal.mul_top, Ideal.ofList_cons, Ideal.ofList_singleton,
      ← Ideal.span_union, Set.singleton_union]
  let e' : (A ⧸ (Ideal.ofList [a, b] • (⊤ : Submodule A A))) ≃ₗ[A]
      A ⧸ Ideal.span ({a, b} : Set A) := Submodule.quotEquivOfEq _ _ hI
  exact (e'.isSMulRegular_congr t).mp
    ((isWeaklyRegular_singleton_iff _ t).mp htail.2)

end PfaffianDescent
