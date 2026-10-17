import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridClosedPointReduction
import AllCharacteristics.VoisinDegreeTenReduction
import PfaffianDescent.SectionCycles
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_effectiveDegreeFourFactory_of_closedEleven_effectiveEight
    {K : Type u} [Field K] [CharZero K]
    (hMiddle : ∀ (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3),
      p ≠ 0 → Smooth (hypersurfaceToBase p hp) →
      (¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
        s ≫ hypersurfaceToBase p hp = 𝟙 _) →
      ∀ x : closedPoints (hypersurface p hp),
        (hypersurfaceToBase p hp).residueDegree x.1 = 11 →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 8) :
    VoisinDegreeTenEffectiveDegreeFourFor K := by
  intro p hp hp0 hsmooth x hx
  letI : Smooth (hypersurfaceToBase p hp) := hsmooth
  by_cases hsection : ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _
  · obtain ⟨s, hs⟩ := hsection
    exact effective_cycle_of_section (hypersurfaceToBase p hp) s hs 4
  · rcases voisinDegreeTenSelectedAvoidance_effectiveFour_or_closedEleven_of_closedTen
        p hp hp0 x hx hsection with hfour | ⟨y, hy⟩
    · exact hfour
    · obtain ⟨z, hz⟩ := hMiddle p hp hp0 hsmooth hsection y hy
      rcases section_or_effectiveDegreeFour_of_effectiveDegreeEight p hp hp0 z hz with hs | hf
      · exact False.elim (hsection hs)
      · exact hf
end PfaffianDescent
