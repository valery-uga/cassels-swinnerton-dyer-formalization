import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridSpecializedComplementCycle
import PfaffianDescent.VoisinClosedDegreeElevenReduction
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_effectiveFour_or_closedEleven_of_closedTen
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    (∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4) ∨
    (∃ y : closedPoints (hypersurface p hp),
      (hypersurfaceToBase p hp).residueDegree y.1 = 11) := by
  let D := finiteSubschemeDatumOfClosedPointOfResidueDegree
    (hypersurfaceToBase p hp) x 10 hx
  letI : Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) :=
    finiteSubschemeDatumOfClosedPointOfResidueDegree_toBase_etale
      (hypersurfaceToBase p hp) x 10 hx
  obtain ⟨z, hz⟩ := voisinDegreeTenSelectedAvoidance_exists_effectiveDegreeEleven_of_etaleTen
    p hp D hno
  rcases section_or_effectiveDegreeFour_or_closedPointDegreeEleven_of_effectiveDegreeEleven
    p hp hp0 z hz with hsection | hnext
  · exact False.elim (hno hsection)
  · exact hnext

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_section_or_effectiveFour_or_closedEleven_of_closedTen
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 10) :
    (∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
    (∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4) ∨
    (∃ y : closedPoints (hypersurface p hp),
      (hypersurfaceToBase p hp).residueDegree y.1 = 11) := by
  by_cases hsection : ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _
  · exact Or.inl hsection
  · exact Or.inr (voisinDegreeTenSelectedAvoidance_effectiveFour_or_closedEleven_of_closedTen
      p hp hp0 x hx hsection)
end PfaffianDescent
