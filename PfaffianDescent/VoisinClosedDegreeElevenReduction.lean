import PfaffianDescent.VoisinGenericDegreeTenSpecialization

/-! # Retaining the original degree-eleven field point

The arithmetic reduction supplies one closed field point, rather than an
arbitrary finite etale subscheme. The degree-eight alternative is already
handled by the quadratic residual construction.
-/

open AlgebraicGeometry CategoryTheory
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An effective degree-eleven cycle supplies a rational point, an effective
degree-four cycle, or an original closed point of residue degree eleven. -/
theorem section_or_effectiveDegreeFour_or_closedPointDegreeEleven_of_effectiveDegreeEleven
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 11) :
    (∃ a : Spec (.of K) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
    (∃ z₄ : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₄ = 4) ∨
    (∃ x : closedPoints (hypersurface p hp),
      (hypersurfaceToBase p hp).residueDegree x.1 = 11) := by
  rcases cubic_section_or_closedPoint_degree_eight_or_eleven_of_effective_degree_eleven
      p hp hp0 z hz with hsection | ⟨x, h8 | h11⟩
  · exact Or.inl hsection
  · let D₈ := finiteSubschemeDatumOfClosedPointOfResidueDegree
      (hypersurfaceToBase p hp) x 8 h8
    letI : Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) :=
      finiteSubschemeDatumOfClosedPointOfResidueDegree_toBase_etale
        (hypersurfaceToBase p hp) x 8 h8
    exact Or.inr (Or.inl
      (exists_effectiveDegreeFourCycle_of_smoothCubic_and_etaleDegreeEight p hp hp0 D₈))
  · exact Or.inr (Or.inr ⟨x, h11⟩)

end PfaffianDescent
