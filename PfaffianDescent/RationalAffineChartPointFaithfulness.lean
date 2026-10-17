import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! A rational affine point is determined by its underlying prime together
with the actual coefficient map. This is used to recover vertex residues
from the support of a supplied nonreduced double point. -/

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

theorem fieldValueRingHom_eq_of_same_kernel
    {K R : Type u} [Field K] [CommRing R]
    (c : K →+* R) (f g : R →+* K)
    (hf : f.comp c = RingHom.id K) (hg : g.comp c = RingHom.id K)
    (hker : RingHom.ker f = RingHom.ker g) : f = g := by
  apply RingHom.ext
  intro a
  have hfa : f (a - c (f a)) = 0 := by
    rw [map_sub, show f (c (f a)) = f a from DFunLike.congr_fun hf (f a)]
    exact sub_self _
  have hga : g (a - c (f a)) = 0 := by
    apply RingHom.mem_ker.mp
    rw [← hker]
    exact RingHom.mem_ker.mpr hfa
  rw [map_sub, show g (c (f a)) = f a from DFunLike.congr_fun hg (f a)] at hga
  exact (sub_eq_zero.mp hga).symm

theorem fieldValueRingHom_eq_of_same_prime_point
    {K R : Type u} [Field K] [CommRing R]
    (c : K →+* R) (f g : R →+* K)
    (hf : f.comp c = RingHom.id K) (hg : g.comp c = RingHom.id K)
    (hpoint : PrimeSpectrum.comap f (IsLocalRing.closedPoint K) =
      PrimeSpectrum.comap g (IsLocalRing.closedPoint K)) : f = g := by
  have hker := congrArg PrimeSpectrum.asIdeal hpoint
  change Ideal.comap f (IsLocalRing.maximalIdeal K) =
    Ideal.comap g (IsLocalRing.maximalIdeal K) at hker
  rw [IsLocalRing.maximalIdeal_eq_bot] at hker
  exact fieldValueRingHom_eq_of_same_kernel c f g hf hg hker

theorem fieldValueRingHom_eq_of_same_spec_point
    {K R : Type u} [Field K] [CommRing R]
    (c : K →+* R) (f g : R →+* K)
    (hf : f.comp c = RingHom.id K) (hg : g.comp c = RingHom.id K)
    (hpoint : Spec.map (CommRingCat.ofHom f) (IsLocalRing.closedPoint K) =
      Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint K)) : f = g := by
  exact fieldValueRingHom_eq_of_same_prime_point c f g hf hg hpoint

end PfaffianDescent
