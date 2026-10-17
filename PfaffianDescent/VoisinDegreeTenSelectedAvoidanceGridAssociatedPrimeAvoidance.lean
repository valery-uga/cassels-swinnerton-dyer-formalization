import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceFixedCurve
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridNativeCurveAvoidance

/-! The native no-fixed-height-two-curve endpoint supplies the literal
associated-prime avoidance needed to select the second residual cubic. -/
noncomputable section
open AlgebraicGeometry MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_cubicKernel_associatedPrimeAvoidance_of_noFixedHeightTwoPrime
    {K A : Type u} [Field K] [Infinite K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (x : Fin 4 → A)
    (hno : ¬ ∃ C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K),
      C.toIdeal.IsPrime ∧ C.toIdeal.height = 2 ∧ p ∈ C.toIdeal ∧
      (∀ s : homogeneousSubmodule (Fin 4) K 3,
        s ∈ LinearMap.ker (homogeneousSectionRestriction x 3) → s.1 ∈ C.toIdeal))
    (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 3) (hrel : IsRelPrime p q) :
    ∀ P ∈ associatedPrimes
        (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set _))
        (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set _)),
      ∃ r ∈ homogeneousVanishingPolynomialSubmodule
          (K := K) (A := A) (sigma := Fin 4) x 3,
        Ideal.Quotient.mk (Ideal.span ({p, q} : Set _)) r ∉ P := by
  by_contra hfailure
  obtain ⟨C, hCp, hCprime, _, hCheight, _, hW, _, _⟩ :=
    voisinDegreeTenSelectedAvoidance_exists_fixedCurve_of_failure p hp hp0 x q hq hrel hfailure
  apply hno
  refine ⟨C, hCprime, hCheight, hCp, ?_⟩
  intro s hs
  apply hW
  exact (mem_homogeneousVanishingPolynomialSubmodule_iff
    (K := K) (A := A) (sigma := Fin 4) x 3 s.1).mpr
      ⟨s.2, LinearMap.mem_ker.mp hs⟩

end PfaffianDescent
