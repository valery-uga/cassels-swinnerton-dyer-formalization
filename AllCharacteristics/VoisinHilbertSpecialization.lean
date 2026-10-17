import AllCharacteristics.FiniteSubschemeParameterSpecialization
import AllCharacteristics.VoisinDegreeTenReduction

/-!
# Hilbert-style specialization for Voisin's degree-ten branch

For the rational-point theorem, Voisin's degree-ten branch only has to
produce an effective degree-four cycle.  This file connects that minimal
target to the generic finite-subscheme specialization package.  It does not
assert Hilbert representability: the parameter space, universal family, and
generic residual point remain explicit geometric data.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace PfaffianDescent

namespace AllCharacteristics
namespace HomogeneousProjective

universe u

/-- A packaged generic rank-four residual specializes to a degree-four cycle
and hence to a rational point on a cubic surface in characteristic zero. -/
theorem hypersurface_section_of_rankFourGenericSpecializationData
    {k : Type u} [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (data : FiniteSubschemeGenericSpecializationData
      (hypersurfaceToBase p hp) 4) :
    ∃ q : Spec (.of k) ⟶ hypersurface p hp,
      q ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨z₄, hz₄⟩ := data.exists_effectiveCycle
  exact hypersurface_section_of_effective_degree_four p hp z₄ hz₄

/-- Supplying a packaged generic rank-four residual for every degree-ten
closed point gives exactly the minimal Voisin input used by the paper. -/
theorem voisinDegreeTenEffectiveDegreeFourFor_of_genericSpecializationData
    {k : Type u} [Field k] [CharZero k]
    (data : ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3),
      p ≠ 0 → Smooth (hypersurfaceToBase p hp) →
        ∀ x : closedPoints (hypersurface p hp),
          (hypersurfaceToBase p hp).residueDegree x.1 = 10 →
          FiniteSubschemeGenericSpecializationData
            (hypersurfaceToBase p hp) 4) :
    VoisinDegreeTenEffectiveDegreeFourFor k := by
  intro p hp hne hs x hx
  exact (data p hp hne hs x hx).exists_effectiveCycle

/-- Coray's theorem and packaged generic rank-four residuals imply the
rational-section conclusion directly, without a Chow specialization axiom. -/
theorem cubic_section_of_zeroCycle_degree_one_of_coray_and_genericSpecializationData
    {k : Type u} [Field k] [CharZero k]
    (coray : CorayDegreeOneFourOrTenFor k)
    (data : ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3),
      p ≠ 0 → Smooth (hypersurfaceToBase p hp) →
        ∀ x : closedPoints (hypersurface p hp),
          (hypersurfaceToBase p hp).residueDegree x.1 = 10 →
          FiniteSubschemeGenericSpecializationData
            (hypersurfaceToBase p hp) 4)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ q : Spec (.of k) ⟶ hypersurface p hp,
      q ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  cubic_section_of_zeroCycle_degree_one_of_coray_and_effectiveDegreeFour
    coray
      (voisinDegreeTenEffectiveDegreeFourFor_of_genericSpecializationData data)
    p hp hne z hz

end HomogeneousProjective
end AllCharacteristics
