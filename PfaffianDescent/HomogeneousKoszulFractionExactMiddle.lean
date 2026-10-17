import PfaffianDescent.HomogeneousKoszulFractionExactLast
import AllCharacteristics.SectionFour

/-! SOURCE ONLY / UNVERIFIED. Exactness of actual homogeneous fraction
Koszul first/middle maps, and both exactness assertions internally derived
for genuine finite nonempty triple. No actual stalk exactness certificate. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K
variable (p : Ideal (MvPolynomial (Fin 4) K)) [p.IsPrime]
local notation "L" => Localization p.primeCompl

theorem homogeneousKoszulFraction_exact_middle
    (t : PS 1) (ht : t.val ∈ p.primeCompl) (f g h : PS 2)
    (hg0 : g.val ≠ 0) (hf0 : f.val ≠ 0) (hrel : IsRelPrime f.val g.val) :
    LinearMap.range (homogeneousKoszulFractionFirst p f g h) =
      LinearMap.ker (homogeneousKoszulFractionMiddle p f g h) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact LinearMap.congr_fun (homogeneousKoszulFraction_middle_first_zero p f g h) x
  · intro x hx
    obtain ⟨d, hd, A, D, hD, hx0, hx1, hx2⟩ :=
      negativeTwistFraction_common_denominator_three p t ht 4 x
    have hc0 := congrArg (fun v : _ × _ × _ => v.1.val) hx
    have hc1 := congrArg (fun v : _ × _ × _ => v.2.1.val) hx
    have hc2 := congrArg (fun v : _ × _ × _ => v.2.2.val) hx
    change -(algebraMap (MvPolynomial (Fin 4) K) L g.val * x.1.val) -
      algebraMap (MvPolynomial (Fin 4) K) L h.val * x.2.1.val = 0 at hc0
    change algebraMap (MvPolynomial (Fin 4) K) L f.val * x.1.val -
      algebraMap (MvPolynomial (Fin 4) K) L h.val * x.2.2.val = 0 at hc1
    change algebraMap (MvPolynomial (Fin 4) K) L f.val * x.2.1.val +
      algebraMap (MvPolynomial (Fin 4) K) L g.val * x.2.2.val = 0 at hc2
    rw [hx0, hx1, polynomialPrimeFraction_mul p _ _ D.val hD,
      polynomialPrimeFraction_mul p _ _ D.val hD,
      Localization.neg_mk, polynomialPrimeFraction_sub p _ _ D.val hD] at hc0
    rw [hx0, hx2, polynomialPrimeFraction_mul p _ _ D.val hD,
      polynomialPrimeFraction_mul p _ _ D.val hD,
      polynomialPrimeFraction_sub p _ _ D.val hD] at hc1
    rw [hx1, hx2, polynomialPrimeFraction_mul p _ _ D.val hD,
      polynomialPrimeFraction_mul p _ _ D.val hD,
      polynomialPrimeFraction_add p _ _ D.val hD] at hc2
    have hp0 : -g.val * A.1.val - h.val * A.2.1.val = 0 := by
      simpa only [neg_mul] using (polynomialPrimeFraction_eq_zero_iff p _ D.val hD).mp hc0
    have hp1 : f.val * A.1.val - h.val * A.2.2.val = 0 :=
      (polynomialPrimeFraction_eq_zero_iff p _ D.val hD).mp hc1
    have hp2 : f.val * A.2.1.val + g.val * A.2.2.val = 0 :=
      (polynomialPrimeFraction_eq_zero_iff p _ D.val hD).mp hc2
    let n := d - 2
    have hn : n + 2 = d := by dsimp [n]; omega
    let A' : PS (n + 2) × PS (n + 2) × PS (n + 2) :=
      (⟨A.1.val, by simpa only [hn] using A.1.property⟩,
        ⟨A.2.1.val, by simpa only [hn] using A.2.1.property⟩,
        ⟨A.2.2.val, by simpa only [hn] using A.2.2.property⟩)
    have hpcycle : A' ∈ LinearMap.ker
        (threeGeneratorGradedMiddle f.val g.val h.val f.property g.property h.property n) := by
      apply Prod.ext
      · exact Subtype.ext hp0
      · exact Prod.ext (Subtype.ext hp1) (Subtype.ext hp2)
    rw [← threeGeneratorGraded_exact_middle f.val g.val h.val f.property g.property h.property
      hg0 hf0 hrel n] at hpcycle
    obtain ⟨r, hr⟩ := hpcycle
    let D' : PS (n + 6) := ⟨D.val, by
      simpa only [← hn, Nat.add_assoc] using D.property⟩
    let z : stalkSubmodule PS p 6 := ⟨Localization.mk r.val ⟨D.val, hD⟩,
      Or.inr ⟨n, r, D', hD, rfl⟩⟩
    have hr0 : h.val * r.val = A.1.val :=
      congrArg (fun v : _ × _ × _ => v.1.val) hr
    have hr1 : -(g.val * r.val) = A.2.1.val := by
      have he := congrArg (fun v : _ × _ × _ => v.2.1.val) hr
      change -g.val * r.val = A.2.1.val at he
      simpa only [neg_mul] using he
    have hr2 : f.val * r.val = A.2.2.val :=
      congrArg (fun v : _ × _ × _ => v.2.2.val) hr
    refine ⟨z, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change algebraMap (MvPolynomial (Fin 4) K) L h.val *
        Localization.mk r.val ⟨D.val, hD⟩ = x.1.val
      rw [polynomialPrimeFraction_mul p _ _ D.val hD, hr0, ← hx0]
    · apply Prod.ext
      · apply Subtype.ext
        change -(algebraMap (MvPolynomial (Fin 4) K) L g.val *
          Localization.mk r.val ⟨D.val, hD⟩) = x.2.1.val
        rw [polynomialPrimeFraction_mul p _ _ D.val hD, Localization.neg_mk, hr1, ← hx1]
      · apply Subtype.ext
        change algebraMap (MvPolynomial (Fin 4) K) L f.val *
          Localization.mk r.val ⟨D.val, hD⟩ = x.2.2.val
        rw [polynomialPrimeFraction_mul p _ _ D.val hD, hr2, ← hx2]

/-- Both genuine homogeneous-fraction exactness statements for an actual
finite nonempty triple, with regularity INTERNALLY derived. The geometric
stalk caller will internally choose t=Xj outside its actual Proj prime. -/
theorem homogeneousKoszulFraction_exact_of_finite
    (t : PS 1) (ht : t.val ∈ p.primeCompl) (f g h : PS 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property))]
    (hT : Nonempty (scheme (tripleCompleteIntersectionHomogeneousIdeal
      f.val g.val h.val f.property g.property h.property))) :
    LinearMap.range (homogeneousKoszulFractionFirst p f g h) =
      LinearMap.ker (homogeneousKoszulFractionMiddle p f g h) ∧
    LinearMap.range (homogeneousKoszulFractionMiddle p f g h) =
      LinearMap.ker (homogeneousKoszulFractionLast p f g h) := by
  have hseq := AllCharacteristics.sectionFour_triple_quadrics_isRegular_of_finite_of_nonempty
    f.val g.val h.val f.property g.property h.property hT
  obtain ⟨hf0, hgreg, hhreg⟩ :=
    (triple_quadrics_isRegular_iff_sequential_regular
      f.val g.val h.val f.property g.property h.property).mp hseq
  have hg0 := right_ne_zero_of_regular_mod_span_singleton
    (homogeneous_not_isUnit_of_pos_degree f.property (by decide)) hgreg
  have hrel := isRelPrime_of_regular_mod_span_singleton hf0 hgreg
  exact ⟨homogeneousKoszulFraction_exact_middle p t ht f g h hg0 hf0 hrel,
    homogeneousKoszulFraction_exact_last p t ht f g h hf0 hrel hhreg⟩

end PfaffianDescent.ProjectiveNegativeTwist
