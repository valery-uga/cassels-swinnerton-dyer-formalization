import PfaffianDescent.CorayAuxiliaryCubicClosedPoint
import AllCharacteristics.ProperCyclePushforward

/-! The actual closed points used to start Coray's least-degree argument.
No geometric degree-reduction theorem is assumed here. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u

/-- A literal rational section supplies a literal closed degree-one point. -/
theorem closedPoint_degree_one_of_section
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ X)
    (hs : s ≫ f = 𝟙 _) :
    ∃ x : closedPoints X, f.residueDegree x.1 = 1 := by
  haveI : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id f s hs
  let b : closedPoints (Spec (.of K)) :=
    ⟨IsLocalRing.closedPoint K, isClosed_singleton⟩
  let x : closedPoints X := ⟨s b.1, by
    change IsClosed {s b.1}
    rw [← Set.image_singleton]
    exact s.isClosedMap _ b.2⟩
  refine ⟨x, ?_⟩
  have hd := residueDegree_comp s f b.1
  rw [hs, Scheme.Hom.residueDegree_id] at hd
  change 1 = f.residueDegree x.1 * s.residueDegree b.1 at hd
  exact Nat.eq_one_of_mul_eq_one_right hd.symm

/-- The actual line-section construction gives a closed point of degree
one or three, including the branch where it first produces a section. -/
theorem nonzero_cubic_has_closedPoint_degree_one_or_three
    {K : Type u} [Field K] [Infinite K] {n : ℕ} (hn : 2 ≤ n)
    (p : MvPolynomial (Fin n) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0) :
    ∃ x : closedPoints (hypersurface p hp),
      (hypersurfaceToBase p hp).residueDegree x.1 = 1 ∨
      (hypersurfaceToBase p hp).residueDegree x.1 = 3 := by
  rcases hypersurface_section_or_cubic_of_nonzero_cubic hn p hp hp0 with
    ⟨s, hs⟩ | ⟨x, hx⟩
  · obtain ⟨x, hx⟩ := closedPoint_degree_one_of_section (hypersurfaceToBase p hp) s hs
    exact ⟨x, Or.inl hx⟩
  · exact ⟨x, Or.inr hx⟩

/-- A literal signed degree-one cycle selects an actual closed point of
least degree among ALL actual closed points with degree coprime to three,
not just among the points occurring in the original cycle. -/
theorem zeroCycle_degree_one_has_minimal_coprime_closedPoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) (z : ZeroCycle X)
    (hz : ZeroCycle.degree f z = 1) :
    ∃ x : closedPoints X, Nat.Coprime (f.residueDegree x.1) 3 ∧
      ∀ y : closedPoints X, Nat.Coprime (f.residueDegree y.1) 3 →
        f.residueDegree x.1 ≤ f.residueDegree y.1 := by
  classical
  have hex : ∃ d : ℕ, ∃ x : closedPoints X,
      f.residueDegree x.1 = d ∧ Nat.Coprime d 3 := by
    obtain ⟨x, _, hx⟩ := ZeroCycle.exists_coprime_degree f z hz
    exact ⟨f.residueDegree x.1, x, rfl, hx⟩
  obtain ⟨x, hx, hcop⟩ := Nat.find_spec hex
  refine ⟨x, hx.symm ▸ hcop, ?_⟩
  intro y hy
  rw [hx]
  exact Nat.find_min' hex ⟨y, rfl, hy⟩

/-- In the no-rational-section branch, every coprime-degree point has degree
at least four: degrees at most two descend by the actual quadratic secant,
and degree three is excluded arithmetically. -/
theorem cubic_coprime_point_degree_ge_four_of_no_section
    {K : Type u} [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) (hp : p.IsHomogeneous 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (x : closedPoints (hypersurface p hp))
    (hc : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) :
    4 ≤ (hypersurfaceToBase p hp).residueDegree x.1 := by
  have hlarge : ¬ (hypersurfaceToBase p hp).residueDegree x.1 ≤ 2 := by
    intro hsmall
    exact hno (hypersurface_section_of_closedPoint_degree_le_two p hp x hsmall)
  have hnd : ¬ 3 ∣ (hypersurfaceToBase p hp).residueDegree x.1 :=
    Nat.prime_three.coprime_iff_not_dvd.mp hc.symm
  omega

end PfaffianDescent.Coray
