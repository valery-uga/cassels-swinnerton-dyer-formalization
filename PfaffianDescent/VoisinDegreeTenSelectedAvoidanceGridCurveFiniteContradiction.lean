import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridCurveNotFinite
import PfaffianDescent.VoisinDegreeEightFixedCurveSections
import PfaffianDescent.HomogeneousQuotientMap
import AllCharacteristics.ProjectiveBaseChange

/-! A literal finite homogeneous triple excludes any containing height-two
prime curve, over arbitrary coefficient fields. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_heightTwoPrime_not_finite
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCprime : C.toIdeal.IsPrime) (hCheight : C.toIdeal.height = 2) :
    ¬ IsFinite (toBase C) := by
  intro hfinite
  letI : IsFinite (toBase C) := hfinite
  let L := AlgebraicClosure K
  let f := algebraMap K L
  let J := HomogeneousIdeal.map (ambientCoefficientGradedRingHom f) C
  have hJ : C.toIdeal.map (MvPolynomial.map f) = J.toIdeal := rfl
  let e := projectiveBaseChangeIso f C J hJ
  letI : IsFinite (toBase J) := by
    rw [← projectiveBaseChangeIso_hom_snd f C J hJ]
    infer_instance
  obtain ⟨P, hPprime, _, hPheight, hJP⟩ :=
    exists_algebraicClosure_homogeneousPrime_over_height_two C hCprime hCheight
  letI : IsClosedImmersion (schemeQuotientMap J P hJP) :=
    schemeQuotientMap_closedImmersion J P hJP
  haveI : IsFinite (toBase P) := by
    rw [← schemeQuotientMap_toBase J P hJP]
    infer_instance
  exact voisinDegreeTenSelectedAvoidance_heightTwoPrime_not_finite_algClosed
    P hPprime hPheight inferInstance

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_finiteTriple_not_contained_in_heightTwoPrime
    {K : Type u} [Field K] {a b c : ℕ}
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCprime : C.toIdeal.IsPrime) (hCheight : C.toIdeal.height = 2) :
    ¬ (p ∈ C.toIdeal ∧ q ∈ C.toIdeal ∧ r ∈ C.toIdeal) := by
  rintro ⟨hpC, hqC, hrC⟩
  let J := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  have hJC : J ≤ C := by
    change Ideal.span ({p, q, r} : Set _) ≤ C.toIdeal
    apply Ideal.span_le.mpr
    rintro z (rfl | rfl | rfl)
    · exact hpC
    · exact hqC
    · exact hrC
  letI : IsClosedImmersion (schemeQuotientMap J C hJC) :=
    schemeQuotientMap_closedImmersion J C hJC
  haveI : IsFinite (toBase C) := by
    rw [← schemeQuotientMap_toBase J C hJC]
    infer_instance
  exact voisinDegreeTenSelectedAvoidance_heightTwoPrime_not_finite C hCprime hCheight inferInstance

end PfaffianDescent
