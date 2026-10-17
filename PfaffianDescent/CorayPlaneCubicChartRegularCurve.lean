import AllCharacteristics.ProjectiveHypersurfaceClosedDimension
import AllCharacteristics.SmoothRegularity
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import PfaffianDescent.HomogeneousQuotientMap

/-! SOURCE ONLY / UNCOMPILED156. Actual native Fin3 plane hypersurface chart
regularity, domain, and dimension≤1; no tangent-rank or local PID premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open scoped nonZeroDivisors
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every coordinate survives a nonzero degree-three equation; its actual
chart is a domain when the literal cubic ideal is prime. -/
theorem planeCubic_chartRing_isDomain
    (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 3) K))).IsPrime)
    (j : Fin 3) : IsDomain (ChartRing (equationIdeal p hp) j) := by
  let I := equationIdeal p hp
  letI : IsDomain (CoordinateRing I) :=
    (Ideal.Quotient.isDomain_iff_prime I.toIdeal).mpr hprime
  have hz : coordinate I j ≠ 0 := by
    intro hzero
    have hmem : X j ∈ I.toIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    have hdiv : p ∣ X j := Ideal.mem_span_singleton.mp hmem
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv (X_ne_zero j)
    rw [hp.totalDegree hp0, MvPolynomial.totalDegree_X] at hle
    omega
  let M := Submonoid.powers (coordinate I j)
  have hM : M ≤ nonZeroDivisors (CoordinateRing I) := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hz)
  letI : IsDomain (Localization M) := IsLocalization.isDomain_localization hM
  exact (HomogeneousLocalization.val_injective M).isDomain
    (algebraMap (ChartRing I j) (Localization M))

/-- Smoothness of the actual cubic restricts to its actual standard chart,
then native smooth-algebra regularity applies over the same coefficient field. -/
theorem planeCubic_chartRing_isRegularRing
    (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] (j : Fin 3) :
    IsRegularRing (ChartRing (equationIdeal p hp) j) := by
  let I := equationIdeal p hp
  letI : Smooth (toBase I) := inferInstanceAs (Smooth (hypersurfaceToBase p hp))
  have hc : Smooth (chartι I j ≫ toBase I) := by infer_instance
  rw [chartι_toBase] at hc
  have hmap : (chartBaseMap I j).Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth.{u})).mp hc
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  letI : Algebra.Smooth K (ChartRing I j) := RingHom.smooth_algebraMap.mp hmap
  exact AllCharacteristics.isRegularRing_of_smooth K (ChartRing I j)

/-- The literal actual chart is a nonzero principal quotient of a two-variable
polynomial algebra, so its Krull dimension is at most one. -/
theorem planeCubic_chartRing_ringKrullDim_le_one
    (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (j : Fin 3) : ringKrullDim (ChartRing (equationIdeal p hp) j) ≤ 1 := by
  classical
  let σ := {i : Fin 3 // i ≠ j}
  let F : MvPolynomial σ K := coordinateOneEvaluation j p
  let A := MvPolynomial σ K ⧸ Ideal.span ({F} : Set (MvPolynomial σ K))
  have hF0 : F ≠ 0 :=
    AllCharacteristics.HomogeneousProjective.coordinateOneEvaluation_ne_zero_of_homogeneous j p hp hp0
  let eC := (chartPresentationEquiv (equationIdeal p hp) j).symm
  have eC' : ChartRing (equationIdeal p hp) j ≃+*
      (MvPolynomial (Fin 3) K ⧸ (Ideal.span {p} ⊔ coordinateOneIdeal j)) := eC
  let e : ChartRing (equationIdeal p hp) j ≃+* A :=
    eC'.trans (coordinateOneHypersurfaceQuotientEquiv j p).toRingEquiv
  have hcard : Fintype.card σ = 2 := by
    change Fintype.card {i : Fin 3 // i ≠ j} = 2
    simpa using Fintype.card_subtype_compl (fun i : Fin 3 => i = j)
  have hreg : F ∈ (MvPolynomial σ K)⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hF0
  have hsucc : ringKrullDim A + 1 ≤ (1 : WithBot ℕ∞) + 1 := by
    have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hreg
    have htwo : ringKrullDim A + 1 ≤ (2 : WithBot ℕ∞) := by
      simpa [A, MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card, hcard,
        zero_add, WithBot.coe_ofNat] using h
    convert htwo using 1 <;> norm_num
  have hdim : ringKrullDim A ≤ 1 := ENat.WithBot.add_le_add_one_right_iff.mp hsucc
  rw [ringKrullDim_eq_of_ringEquiv e]
  exact hdim

/-- Every actual prime localization has dimension at most one. -/
theorem planeCubic_chartLocal_ringKrullDim_le_one
    (p : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (j : Fin 3) (Q : Ideal (ChartRing (equationIdeal p hp) j)) [Q.IsPrime] :
    ringKrullDim (Localization.AtPrime Q) ≤ 1 := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)]
  exact (Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top' (I := Q))).trans
    (planeCubic_chartRing_ringKrullDim_le_one p hp hp0 j)

end PfaffianDescent.Coray
