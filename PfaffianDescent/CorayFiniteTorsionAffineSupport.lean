import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Actual finite affine torsion defects and finite support

A genuine finite torsion module over a domain of dimension at most one has an
actual common nonzero annihilator. Its actual annihilator quotient has all
primes maximal. This proves finite support and, over an actual finite-type
field algebra, finite ground dimension. No finite-support/dimension certificate.

STATUS: UNVERIFIED source only. Root owns compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open Module PrimeSpectrum
open scoped nonZeroDivisors

/-- The actual annihilator quotient of an actual finite torsion module has
actual dimension zero, proved using its actual common nonzero annihilator. -/
theorem finiteTorsion_annihilatorQuotient_krullDimLE_zero
    (R N : Type*) [CommRing R] [IsDomain R] [Ring.DimensionLEOne R]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (htorsion : Module.IsTorsion R N) :
    Ring.KrullDimLE 0 (R ⧸ Module.annihilator R N) := by
  obtain ⟨a, ha, hregular⟩ := Submodule.annihilator_top_inter_nonZeroDivisors htorsion
  rw [Submodule.annihilator_top] at ha
  have hane : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hregular
  apply Ring.KrullDimLE.mk₀
  intro J hJ
  have hprime : (J.comap (Ideal.Quotient.mk (Module.annihilator R N))).IsPrime := hJ.comap _
  have hamem : a ∈ J.comap (Ideal.Quotient.mk (Module.annihilator R N)) := by
    change Ideal.Quotient.mk (Module.annihilator R N) a ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact J.zero_mem
  have hnonzero : J.comap (Ideal.Quotient.mk (Module.annihilator R N)) ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.mem_bot] at hamem
    exact hane hamem
  have hmax := hprime.isMaximal hnonzero
  have hmap := Ideal.map_eq_top_or_isMaximal_of_surjective
    (Ideal.Quotient.mk (Module.annihilator R N)) Ideal.Quotient.mk_surjective hmax
  rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective J] at hmap
  exact hmap.resolve_left hJ.ne_top

/-- Actual finite torsion over a Noetherian curve-domain is supported at an
actual finite set of prime points; support is the actual module support. -/
theorem finiteTorsion_support_finite
    (R N : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.DimensionLEOne R] [AddCommGroup N] [Module R N] [Module.Finite R N]
    (htorsion : Module.IsTorsion R N) : (Module.support R N).Finite := by
  letI : Ring.KrullDimLE 0 (R ⧸ Module.annihilator R N) :=
    finiteTorsion_annihilatorQuotient_krullDimLE_zero R N htorsion
  letI : IsArtinianRing (R ⧸ Module.annihilator R N) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  have hfinite : (Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (Module.annihilator R N)))).Finite := Set.finite_range _
  rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker] at hfinite
  rwa [Module.support_eq_zeroLocus]

/-- Actual finite torsion over an actual finite-type curve-domain has actual
finite dimension over the ground field. Dimension zero of its annihilator
quotient constructs the finite ground algebra, not a certificate premise. -/
theorem finiteTorsion_finite_over_ground
    (K R N : Type*) [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    [Algebra.FiniteType K R] [Ring.DimensionLEOne R]
    [AddCommGroup N] [Module R N] [Module K N] [IsScalarTower K R N]
    [Module.Finite R N] (htorsion : Module.IsTorsion R N) : Module.Finite K N := by
  let I := Module.annihilator R N
  letI : Ring.KrullDimLE 0 (R ⧸ I) :=
    finiteTorsion_annihilatorQuotient_krullDimLE_zero R N htorsion
  letI : Algebra.FiniteType K (R ⧸ I) := Algebra.FiniteType.of_surjective
    (IsScalarTower.toAlgHom K R (R ⧸ I)) Ideal.Quotient.mk_surjective
  letI : Module.Finite K (R ⧸ I) := (Module.finite_iff_krullDimLE_zero K (R ⧸ I)).mpr
    inferInstance
  have hkill : Module.IsTorsionBySet R N I := by
    simpa only [I, Submodule.annihilator_top] using Module.isTorsionBySet_annihilator_top R N
  letI : Module (R ⧸ I) N := hkill.module
  letI : IsScalarTower R (R ⧸ I) N := hkill.isScalarTower
  letI : IsScalarTower K (R ⧸ I) N := hkill.isScalarTower
  letI : Module.Finite (R ⧸ I) N := Module.Finite.of_restrictScalars_finite R (R ⧸ I) N
  exact Module.Finite.trans (R ⧸ I) N

end PfaffianDescent.Coray
