import AllCharacteristics.RegularPairDimension
import Mathlib.RingTheory.Regular.Free
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
Elementary syzygy freeness on regular local rings of dimension two.
The ideal need not be a complete intersection, radical, or of finite
colength. Identification of the presentation minors with ideal generators
is established separately in the Hilbert--Burch cofactor construction.
-/

open scoped Pointwise nonZeroDivisors

namespace AllCharacteristics.HilbertSurfaceDraft

section Reduction

variable {R F N : Type*} [CommRing R]
    [AddCommGroup F] [Module R F] [AddCommGroup N] [Module R N]

/-- The reduction of a kernel embeds in the reduction of the ambient module
when the target has no `x`-torsion.  Surjectivity of `f` is unnecessary. -/
theorem quotSMulTop_ker_subtype_injective
    (f : F →ₗ[R] N) (x : R) (hx : IsSMulRegular N x) :
    Function.Injective (QuotSMulTop.map x (LinearMap.ker f).subtype) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm ?_ bot_le
  intro q hq
  obtain ⟨k, rfl⟩ := (Submodule.mkQ_surjective
    (x • (⊤ : Submodule R (LinearMap.ker f)))) q
  have hkval : (k : F) ∈ x • (⊤ : Submodule R F) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact LinearMap.mem_ker.mp hq
  obtain ⟨v, _, hv⟩ :=
    (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hkval
  have hfv : f v = 0 := by
    apply hx.right_eq_zero_of_smul
    calc
      x • f v = f (x • v) := (f.map_smul x v).symm
      _ = f k := congrArg f hv
      _ = 0 := k.property
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  exact ⟨⟨v, hfv⟩, trivial, Subtype.ext hv⟩

/-- A regular parameter with PID quotient makes every such kernel free.
The hypotheses on the quotient are independent of the desired conclusion. -/
theorem free_ker_of_regular_parameter_pid_quotient
    [IsNoetherianRing R] [Module.Finite R F] [Module.Free R F]
    (f : F →ₗ[R] N) (x : R)
    (hxjac : x ∈ (⊥ : Ideal R).jacobson)
    (hxF : IsSMulRegular F x) (hxN : IsSMulRegular N x)
    [IsDomain (R ⧸ Ideal.span {x})]
    [IsPrincipalIdealRing (R ⧸ Ideal.span {x})] :
    Module.Free R (LinearMap.ker f) := by
  let K := LinearMap.ker f
  let Q := R ⧸ Ideal.span {x}
  letI : Module.Finite R K := inferInstance
  letI : Module.FinitePresentation R K := Module.finitePresentation_of_finite R K
  letI : Module.Finite Q (QuotSMulTop x K) :=
    Module.Finite.of_restrictScalars_finite R Q (QuotSMulTop x K)
  let j : QuotSMulTop x K →ₗ[Q] QuotSMulTop x F :=
    (QuotSMulTop.map x K.subtype).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  have hj : Function.Injective j :=
    quotSMulTop_ker_subtype_injective f x hxN
  letI : Module.IsTorsionFree Q (QuotSMulTop x K) :=
    hj.moduleIsTorsionFree j (fun r m ↦ j.map_smul r m)
  letI : Module.Free Q (QuotSMulTop x K) :=
    Module.free_of_finite_type_torsion_free'
  exact (Module.free_quotSMulTop_iff_free R K hxjac (IsSMulRegular.submodule K x hxF)).mp
    inferInstance

end Reduction

section RegularLocal

variable {R F : Type*} [CommRing R] [IsRegularLocalRing R]
    [AddCommGroup F] [Module R F] [Module.Finite R F] [Module.Free R F]

/-- Every kernel of a finite free presentation of an ideal on a regular
local surface is free.  There is no lci hypothesis on the ideal. -/
theorem free_ker_to_ideal_regularLocal_dim_two
    (hdim : ringKrullDim R = 2) (I : Ideal R) (f : F →ₗ[R] I) :
    Module.Free R (LinearMap.ker f) := by
  have hdim0 : ringKrullDim R ≠ 0 := by
    rw [hdim]
    norm_num
  obtain ⟨x, hx, hx2, _⟩ :=
    exists_parameter_avoiding_minimal_primes hdim0
  let Q := R ⧸ Ideal.span {x}
  letI : IsRegularLocalRing Q :=
    isRegularLocalRing_quotient_parameter x hx hx2
  letI : IsDomain R := isDomain_of_regularLocalRing R
  letI : IsDomain Q := isDomain_of_regularLocalRing Q
  have hqdim : ringKrullDim Q = 1 := by
    apply (ENat.WithBot.add_natCast_cancel
      (a := ringKrullDim Q) (b := 1) (c := 1)).mp
    simpa only [Nat.cast_one, Q, hdim,
      show (1 : WithBot ℕ∞) + 1 = 2 by norm_num] using
      ringKrullDim_quotient_parameter_add_one x hx hx2
  letI : IsPrincipalIdealRing Q :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain Q).out 4 0).mp
      (maximalIdeal_isPrincipal_of_regularLocal_dim_one hqdim)
  have hx0 : x ≠ 0 := by
    intro heq
    apply hx2
    simpa [heq] using (IsLocalRing.maximalIdeal R ^ 2).zero_mem
  have hxreg : x ∈ R⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hx0
  have hxR : IsSMulRegular R x :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors hxreg
  apply free_ker_of_regular_parameter_pid_quotient f x
    ((IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R)) hx)
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hxreg)
    (IsSMulRegular.submodule I x hxR)

end RegularLocal

/-- A finite free resolution of every ideal in a two-dimensional regular
local ring.  This is the genuine syzygy construction, before the separate
Hilbert--Burch determinantal identification. -/
theorem exists_finite_free_ideal_presentation
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) (I : Ideal R) :
    ∃ (n m : ℕ) (f : (Fin n → R) →ₗ[R] I)
      (g : (Fin m → R) →ₗ[R] (Fin n → R)),
      Function.Surjective f ∧ Function.Injective g ∧
      LinearMap.range g = LinearMap.ker f := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R I
  let K := LinearMap.ker f
  letI : Module.Free R K := free_ker_to_ideal_regularLocal_dim_two hdim I f
  let b := Module.finBasis R K
  let g : (Fin (Module.finrank R K) → R) →ₗ[R] (Fin n → R) :=
    K.subtype.comp b.equivFun.symm.toLinearMap
  refine ⟨n, Module.finrank R K, f, g, hf, ?_, ?_⟩
  · exact K.subtype_injective.comp b.equivFun.symm.injective
  · change LinearMap.range (K.subtype.comp b.equivFun.symm.toLinearMap) = K
    rw [LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr b.equivFun.symm.surjective)]
    exact K.range_subtype

/-- Rank one of a nonzero ideal and domain rank-nullity fix the rectangular
shape of a finite free presentation. -/
theorem finrank_ker_add_one_of_surjective_to_nonzero_ideal
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {n : ℕ} (I : Ideal R) (hI : I ≠ ⊥)
    (f : (Fin n → R) →ₗ[R] I) (hf : Function.Surjective f) :
    Module.finrank R (LinearMap.ker f) + 1 = n := by
  have hIle : Module.finrank R I ≤ 1 := by
    simpa using I.finrank_le
  have hIpos : 0 < Module.finrank R I := by
    obtain ⟨a, ha0⟩ :=
      Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hI)
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨a, ha0⟩
  have hIone : Module.finrank R I = 1 := by omega
  have hnull := (LinearMap.ker f).finrank_quotient_add_finrank
  rw [(f.quotKerEquivOfSurjective hf).finrank_eq, hIone] at hnull
  have hamb : Module.finrank R (Fin n → R) = n := by simp
  omega

/-- The finite free presentation has precisely the Hilbert--Burch matrix
shape for a nonzero ideal.  The determinantal identification is still separate. -/
theorem exists_successor_finite_free_ideal_presentation
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) (I : Ideal R) (hI : I ≠ ⊥) :
    ∃ (m : ℕ) (f : (Fin (m + 1) → R) →ₗ[R] I)
      (g : (Fin m → R) →ₗ[R] (Fin (m + 1) → R)),
      Function.Surjective f ∧ Function.Injective g ∧
      LinearMap.range g = LinearMap.ker f := by
  letI : IsDomain R := isDomain_of_regularLocalRing R
  obtain ⟨n, m, f, g, hf, hg, hgf⟩ :=
    exists_finite_free_ideal_presentation hdim I
  have hm : Module.finrank R (LinearMap.ker f) = m := by
    rw [← hgf, g.finrank_range_of_inj hg]
    simp
  have hnm : n = m + 1 := by
    have h := finrank_ker_add_one_of_surjective_to_nonzero_ideal I hI f hf
    omega
  subst n
  exact ⟨m, f, g, hf, hg, hgf⟩

/-- A regular pair contained in an ideal makes every linear functional on
that ideal multiplication by a scalar.  This is the elementary duality step
in the signed-maximal-minor identification. -/
theorem ideal_linearMap_eq_mul_of_regular_pair
    {R : Type*} [CommRing R] (I : Ideal R)
    (a b : R) (haI : a ∈ I) (hbI : b ∈ I)
    (ha : IsSMulRegular R a)
    (hb : IsSMulRegular (R ⧸ Ideal.span {a}) b)
    (φ : I →ₗ[R] R) :
    ∃ c : R, ∀ z : I, φ z = c * (z : R) := by
  let aI : I := ⟨a, haI⟩
  let bI : I := ⟨b, hbI⟩
  have hcomm (u v : I) : (u : R) * φ v = (v : R) * φ u := by
    have huv : (u : R) • v = (v : R) • u := by
      apply Subtype.ext
      exact mul_comm (u : R) (v : R)
    simpa only [map_smul, smul_eq_mul] using congrArg φ huv
  have hφa : φ aI ∈ Ideal.span ({a} : Set R) := by
    apply mem_of_isSMulRegular_quotient_of_smul_mem hb
    change b * φ aI ∈ Ideal.span ({a} : Set R)
    rw [← hcomm aI bI]
    exact Ideal.mem_span_singleton.mpr ⟨φ bI, rfl⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hφa
  refine ⟨c, fun z ↦ ?_⟩
  apply ha
  change a * φ z = a * (c * (z : R))
  calc
    a * φ z = (z : R) * φ aI := hcomm aI z
    _ = a * (c * (z : R)) := by rw [hc]; ring

end AllCharacteristics.HilbertSurfaceDraft
