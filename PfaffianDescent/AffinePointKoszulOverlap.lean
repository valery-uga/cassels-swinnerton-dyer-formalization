import PfaffianDescent.AffinePointIdealSpreading
import PfaffianDescent.KoszulCechTransgression

/-!
# Koszul lifts on affine overlaps avoiding the point

The isolated common-zero condition implies a unit ideal of actual sections
on every affine subopen avoiding the point. Thus first lifts and unique
second coefficients on these overlaps require no extra Bezout hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace PfaffianDescent

universe u

/-- On an affine subopen avoiding the isolated common zero, the restrictions
of the two parameters generate the unit ideal of sections. -/
theorem affine_restricted_pair_span_eq_top_away_point
    {X : Scheme.{u}} (U : X.Opens) (x : X) (q f : Γ(X, U))
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ U) (hxW : x ∉ W) :
    Ideal.span ({X.presheaf.map (homOfLE hWU).op q,
      X.presheaf.map (homOfLE hWU).op f} : Set Γ(X, W)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  apply hW.mem_ideal_iff.mpr
  intro z hz
  rw [Ideal.map_span, Set.image_pair]
  change X.presheaf.germ W z hz 1 ∈
    Ideal.span ({X.presheaf.germ W z hz (X.presheaf.map (homOfLE hWU).op q),
      X.presheaf.germ W z hz (X.presheaf.map (homOfLE hWU).op f)} :
      Set (X.presheaf.stalk z))
  rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply,
    haway z (hWU hz) (fun heq => hxW (heq ▸ hz))]
  trivial

/-- Every section on such an overlap has a first Koszul lift. -/
theorem exists_affine_point_koszul_overlap_lift
    {X : Scheme.{u}} (U : X.Opens) (x : X) (q f : Γ(X, U))
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ U) (hxW : x ∉ W)
    (t : Γ(X, W)) :
    ∃ v : Γ(X, W) × Γ(X, W),
      twoGeneratorLast (X.presheaf.map (homOfLE hWU).op q)
        (X.presheaf.map (homOfLE hWU).op f) v = t := by
  have ht : t ∈ Ideal.span ({X.presheaf.map (homOfLE hWU).op q,
      X.presheaf.map (homOfLE hWU).op f} : Set Γ(X, W)) := by
    rw [affine_restricted_pair_span_eq_top_away_point U x q f haway W hW hWU hxW]
    trivial
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp ht
  refine ⟨(a, b), ?_⟩
  change _ * a + _ * b = t
  simpa only [mul_comm] using hab

end PfaffianDescent
