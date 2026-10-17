import PfaffianDescent.CubicLineFiniteSubscheme
import AllCharacteristics.SchemeQuadraticDescent
import Lean.Elab.Tactic.Omega

/-! A genuine auxiliary degree-three closed point for Coray's construction.
An actual line-section cycle supplies the point unless the cubic already has
an actual rational section. No Coray/Voisin degree reduction is assumed.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u

/-- An actual degree-three effective cycle gives a rational section, or a
single actual degree-three closed point in its support. -/
theorem hypersurface_section_or_cubic_of_effective_degree_three
    {K : Type u} [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) (hp : p.IsHomogeneous 3)
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 3) :
    (∃ q : Spec (.of K) ⟶ hypersurface p hp,
      q ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
    ∃ x ∈ z.support, (hypersurfaceToBase p hp).residueDegree x.1 = 3 := by
  classical
  have hsum : (∑ x ∈ z.support,
      z x * (hypersurfaceToBase p hp).residueDegree x.val) = 3 := hz
  obtain ⟨x, hx, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (hsum.trans_ne (by decide : (3 : ℕ) ≠ 0))
  have hweight : 0 < z x := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)
  have hterm : z x * (hypersurfaceToBase p hp).residueDegree x.val ≤ 3 := by
    calc
      _ ≤ ∑ y ∈ z.support, z y * (hypersurfaceToBase p hp).residueDegree y.val :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
      _ = 3 := hsum
  have hd : (hypersurfaceToBase p hp).residueDegree x.val ≤ 3 :=
    (Nat.le_mul_of_pos_left _ hweight).trans hterm
  by_cases hsmall : (hypersurfaceToBase p hp).residueDegree x.val ≤ 2
  · exact Or.inl (hypersurface_section_of_closedPoint_degree_le_two p hp x hsmall)
  · exact Or.inr ⟨x, hx, by omega⟩

/-- An actual finite line section constructs the auxiliary closed cubic
point over every infinite field, unless the original cubic has a rational
section already. Smoothness and Coray's main theorem are not prerequisites. -/
theorem hypersurface_section_or_cubic_of_nonzero_cubic
    {K : Type u} [Field K] [Infinite K] {n : ℕ} (hn : 2 ≤ n)
    (p : MvPolynomial (Fin n) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0) :
    (∃ q : Spec (.of K) ⟶ hypersurface p hp,
      q ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
    ∃ x : closedPoints (hypersurface p hp),
      (hypersurfaceToBase p hp).residueDegree x.1 = 3 := by
  let z := PfaffianDescent.cubicLineSectionCycle hn p hp hp0
  have hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 3 :=
    PfaffianDescent.cubicLineSectionCycle_degree hn p hp hp0
  rcases hypersurface_section_or_cubic_of_effective_degree_three p hp z hz with
    h | ⟨x, _, hx⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, hx⟩

end PfaffianDescent.Coray
