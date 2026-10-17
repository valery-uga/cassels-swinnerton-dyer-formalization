import PfaffianDescent.HomogeneousKoszulFractionMaps

/-! SOURCE ONLY / UNVERIFIED. Exactness in the actual homogeneous fraction
submodules. Clear homogeneous denominators, project the polynomial preimage
in its correct grading, then divide by the SAME homogeneous denominator.
No grading on full prime localization and no normalized-regularity input. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry MvPolynomial
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K
variable (p : Ideal (MvPolynomial (Fin 4) K)) [p.IsPrime]
local notation "L" => Localization p.primeCompl

theorem homogeneousKoszulFraction_exact_last
    (t : PS 1) (ht : t.val ∈ p.primeCompl) (f g h : PS 2)
    (hf0 : f.val ≠ 0) (hrel : IsRelPrime f.val g.val)
    (hreg : ∀ a : MvPolynomial (Fin 4) K,
      h.val * a ∈ Ideal.span ({f.val, g.val} : Set (MvPolynomial (Fin 4) K)) →
        a ∈ Ideal.span ({f.val, g.val} : Set (MvPolynomial (Fin 4) K))) :
    LinearMap.range (homogeneousKoszulFractionMiddle p f g h) =
      LinearMap.ker (homogeneousKoszulFractionLast p f g h) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact LinearMap.congr_fun (homogeneousKoszulFraction_last_middle_zero p f g h) x
  · intro x hx
    obtain ⟨d, hd, A, D, hD, hx0, hx1, hx2⟩ :=
      negativeTwistFraction_common_denominator_three p t ht 2 x
    have hz := congrArg Subtype.val hx
    change algebraMap (MvPolynomial (Fin 4) K) L f.val * x.1.val +
      algebraMap (MvPolynomial (Fin 4) K) L g.val * x.2.1.val +
      algebraMap (MvPolynomial (Fin 4) K) L h.val * x.2.2.val = 0 at hz
    rw [hx0, hx1, hx2,
      polynomialPrimeFraction_mul p f.val A.1.val D.val hD,
      polynomialPrimeFraction_mul p g.val A.2.1.val D.val hD,
      polynomialPrimeFraction_mul p h.val A.2.2.val D.val hD,
      polynomialPrimeFraction_add p _ _ D.val hD, polynomialPrimeFraction_add p _ _ D.val hD] at hz
    have hpoly : f.val * A.1.val + g.val * A.2.1.val + h.val * A.2.2.val = 0 :=
      (polynomialPrimeFraction_eq_zero_iff p _ D.val hD).mp hz
    let n := d - 4
    have hn : n + 4 = d := by dsimp [n]; omega
    let A' : PS (n + 4) × PS (n + 4) × PS (n + 4) :=
      (⟨A.1.val, by simpa only [hn] using A.1.property⟩,
        ⟨A.2.1.val, by simpa only [hn] using A.2.1.property⟩,
        ⟨A.2.2.val, by simpa only [hn] using A.2.2.property⟩)
    have hpcycle : A' ∈ LinearMap.ker
        (threeGeneratorGradedLast f.val g.val h.val f.property g.property h.property n) := by
      apply Subtype.ext
      exact hpoly
    rw [← threeGeneratorGraded_exact_last f.val g.val h.val f.property g.property h.property
      hf0 hrel hreg n] at hpcycle
    obtain ⟨B, hB⟩ := hpcycle
    let D' : PS ((n + 2) + 4) := ⟨D.val, by
      simpa only [← hn, Nat.add_assoc] using D.property⟩
    let z0 : stalkSubmodule PS p 4 := ⟨Localization.mk B.1.val ⟨D.val, hD⟩,
      Or.inr ⟨n + 2, B.1, D', hD, rfl⟩⟩
    let z1 : stalkSubmodule PS p 4 := ⟨Localization.mk B.2.1.val ⟨D.val, hD⟩,
      Or.inr ⟨n + 2, B.2.1, D', hD, rfl⟩⟩
    let z2 : stalkSubmodule PS p 4 := ⟨Localization.mk B.2.2.val ⟨D.val, hD⟩,
      Or.inr ⟨n + 2, B.2.2, D', hD, rfl⟩⟩
    have hB0 : -(g.val * B.1.val) - h.val * B.2.1.val = A.1.val := by
      have he := congrArg (fun v : _ × _ × _ => v.1.val) hB
      change -g.val * B.1.val - h.val * B.2.1.val = A.1.val at he
      simpa only [neg_mul] using he
    have hB1 : f.val * B.1.val - h.val * B.2.2.val = A.2.1.val :=
      congrArg (fun v : _ × _ × _ => v.2.1.val) hB
    have hB2 : f.val * B.2.1.val + g.val * B.2.2.val = A.2.2.val :=
      congrArg (fun v : _ × _ × _ => v.2.2.val) hB
    refine ⟨(z0, z1, z2), ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change -(algebraMap (MvPolynomial (Fin 4) K) L g.val *
          Localization.mk B.1.val ⟨D.val, hD⟩) -
        algebraMap (MvPolynomial (Fin 4) K) L h.val *
          Localization.mk B.2.1.val ⟨D.val, hD⟩ = x.1.val
      rw [polynomialPrimeFraction_mul p _ _ D.val hD, polynomialPrimeFraction_mul p _ _ D.val hD,
        Localization.neg_mk, polynomialPrimeFraction_sub p _ _ D.val hD, hB0, ← hx0]
    · apply Prod.ext
      · apply Subtype.ext
        change algebraMap (MvPolynomial (Fin 4) K) L f.val *
            Localization.mk B.1.val ⟨D.val, hD⟩ -
          algebraMap (MvPolynomial (Fin 4) K) L h.val *
            Localization.mk B.2.2.val ⟨D.val, hD⟩ = x.2.1.val
        rw [polynomialPrimeFraction_mul p _ _ D.val hD, polynomialPrimeFraction_mul p _ _ D.val hD,
          polynomialPrimeFraction_sub p _ _ D.val hD, hB1, ← hx1]
      · apply Subtype.ext
        change algebraMap (MvPolynomial (Fin 4) K) L f.val *
            Localization.mk B.2.1.val ⟨D.val, hD⟩ +
          algebraMap (MvPolynomial (Fin 4) K) L g.val *
            Localization.mk B.2.2.val ⟨D.val, hD⟩ = x.2.2.val
        rw [polynomialPrimeFraction_mul p _ _ D.val hD, polynomialPrimeFraction_mul p _ _ D.val hD,
          polynomialPrimeFraction_add p _ _ D.val hD, hB2, ← hx2]

end PfaffianDescent.ProjectiveNegativeTwist
