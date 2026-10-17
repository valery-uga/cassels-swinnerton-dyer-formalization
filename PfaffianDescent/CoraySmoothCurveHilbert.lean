import PfaffianDescent.CorayHomogeneousCurveChoice
import PfaffianDescent.CorayCurveHilbertComplex
import PfaffianDescent.CubicFiniteSubschemeHyperplane

/-!
# The actual selected curve on a smooth cubic satisfies its Hilbert identity

SOURCE DRAFT / UNVERIFIED.

Smoothness supplies irreducibility of the surface equation. The equation
selected by the finite-algebra argument is therefore relatively prime to
that surface equation, so the actual Koszul/Hilbert calculation applies.
No curve primeness, normalization, genus or effectivity certificate is
introduced as an input.
-/

namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u

/-- Smoothness and nonmembership supply the regularity needed by the
degreewise Koszul proof. -/
theorem isRelPrime_of_smooth_cubic_and_not_mem
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) :
    IsRelPrime p q := by
  have hirr := irreducible_of_smooth_homogeneous_cubic_of_field p hp hp0
  apply hirr.isRelPrime_iff_not_dvd.mpr
  intro hdiv
  exact hnot (Ideal.mem_span_singleton.mpr hdiv)

/-- The equation through finite coordinates is constructed internally, and
its actual homogeneous quotient has the complete-intersection Hilbert
identity in every sufficiently large degree. This is a prerequisite to the
arithmetic-genus calculation, not an assumed arithmetic-genus conclusion. -/
theorem exists_homogeneous_curve_with_hilbert_identity
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (n : ℕ) (x : Fin 4 → A)
    (hsize : finrank K A < (n + 3).choose 3 - n.choose 3) :
    ∃ q : MvPolynomial (Fin 4) K,
      q.IsHomogeneous n ∧ q.eval₂ (algebraMap K A) x = 0 ∧
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      (∀ d : ℕ,
        finrank K (curveComponent p q (d + n + 3)) +
          ((d + n + 3).choose 3 + (d + 6).choose 3) =
          (d + n + 6).choose 3 + (d + 3).choose 3) := by
  obtain ⟨q, hq, hzero, hnot⟩ := exists_homogeneous_curve_equation p hp hp0 n x hsize
  have hrel := isRelPrime_of_smooth_cubic_and_not_mem p q hp hp0 hnot
  exact ⟨q, hq, hzero, hnot, fun d => curve_hilbert_choose_identity p q hp hq hp0 hrel d⟩

end PfaffianDescent.Coray
