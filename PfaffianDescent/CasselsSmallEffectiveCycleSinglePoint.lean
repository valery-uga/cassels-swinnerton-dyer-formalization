import AllCharacteristics.SchemeQuadraticDescent
import PfaffianDescent.ResidualCycles
import Mathlib.Data.Finsupp.Single

/-! SOURCE ONLY. A degree4/5 effective cycle on a cubic with no ground section
is literally a single closed point. Only small-degree secant descent is used;
no degree-four/five point-descent theorem or external Coray/Voisin input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory AllCharacteristics
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u

/-- An effective weighted sum of degree4/5, all of whose support degrees are
at least3, has one point with multiplicity1. This is ordinary support arithmetic. -/
theorem finsupp_degree_four_or_five_min_three_single
    {ι : Type u} (z : ι →₀ ℕ) (D : ι → ℕ)
    (hdegree : (∑ x ∈ z.support, z x * D x) = 4 ∨
      (∑ x ∈ z.support, z x * D x) = 5)
    (hmin : ∀ x ∈ z.support, 3 ≤ D x) :
    ∃ x : ι, z = Finsupp.single x 1 ∧
      D x = ∑ y ∈ z.support, z y * D y := by
  classical
  have hpos : 0 < ∑ x ∈ z.support, z x * D x := by
    rcases hdegree with h4 | h5 <;> omega
  have hle : (∑ x ∈ z.support, z x * D x) ≤ 5 := by
    rcases hdegree with h4 | h5 <;> omega
  obtain ⟨x, hx, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.ne_of_gt hpos)
  have hxpos : 0 < z x := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)
  have hxdeg : 3 ≤ D x := hmin x hx
  have hxle : z x * D x ≤ 5 :=
    (Finset.single_le_sum (fun y _ => Nat.zero_le (z y * D y)) hx).trans hle
  have hxone : z x = 1 := by
    by_contra h
    have hx2 : 2 ≤ z x := by omega
    have h6 : 6 ≤ z x * D x := by
      exact Nat.mul_le_mul hx2 hxdeg
    omega
  have hsupport : z.support ⊆ {x} := by
    intro y hy
    apply Finset.mem_singleton.mpr
    by_contra hne
    have hxy : x ≠ y := Ne.symm hne
    have hypos : 0 < z y := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hy)
    have hydeg : 3 ≤ D y := hmin y hy
    have hxterm : 3 ≤ z x * D x :=
      hxdeg.trans (Nat.le_mul_of_pos_left _ hxpos)
    have hyterm : 3 ≤ z y * D y :=
      hydeg.trans (Nat.le_mul_of_pos_left _ hypos)
    have hpair : ({x, y} : Finset ι) ⊆ z.support := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hx
      · rcases Finset.mem_singleton.mp ha with rfl
        exact hy
    have htwo : z x * D x + z y * D y ≤
        ∑ a ∈ z.support, z a * D a := by
      calc
        _ = ∑ a ∈ ({x, y} : Finset ι), z a * D a := (Finset.sum_pair hxy).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hpair
          (fun a _ _ => Nat.zero_le (z a * D a))
    omega
  have heq : z = Finsupp.single x 1 := Finsupp.eq_single_iff.mpr ⟨hsupport, hxone⟩
  refine ⟨x, heq, ?_⟩
  rw [heq]
  simp

/-- Actual scheme effective cycles preserve their entire equality to a
single closed point; only a degree bound on their actual support is supplied. -/
theorem effectiveCycle_degree_four_or_five_min_three_single
    {X Y : Scheme.{u}} (f : X ⟶ Y) (z : EffectiveZeroCycle X)
    (hdegree : EffectiveZeroCycle.degree f z = 4 ∨ EffectiveZeroCycle.degree f z = 5)
    (hmin : ∀ x ∈ z.support, 3 ≤ f.residueDegree x.1) :
    ∃ x : closedPoints X, z = Finsupp.single x 1 ∧
      f.residueDegree x.1 = EffectiveZeroCycle.degree f z :=
  finsupp_degree_four_or_five_min_three_single z (fun x => f.residueDegree x.1)
    hdegree hmin

/-- The small-degree secant lemma derives the minimum support degree from
absence of an actual ground section; no degree4/5 descent is used. -/
theorem cubic_no_section_closedPoint_degree_ge_three
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnone : ¬ ∃ s : Spec (.of K) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _)
    (P : closedPoints (hypersurface F hF)) :
    3 ≤ (hypersurfaceToBase F hF).residueDegree P.1 := by
  by_contra h
  apply hnone
  exact hypersurface_section_of_closedPoint_degree_le_two F hF P (by omega)

/-- Literal TeX355--356, for the given actual degree4/5 effective cycle.
The conclusion is equality of the ENTIRE cycle with one coefficient1 point. -/
theorem cubic_no_section_effective_degree_four_or_five_eq_single
    {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnone : ¬ ∃ s : Spec (.of K) ⟶ hypersurface F hF,
      s ≫ hypersurfaceToBase F hF = 𝟙 _)
    (z : EffectiveZeroCycle (hypersurface F hF))
    (hdegree : EffectiveZeroCycle.degree (hypersurfaceToBase F hF) z = 4 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase F hF) z = 5) :
    ∃ P : closedPoints (hypersurface F hF), z = Finsupp.single P 1 ∧
      (hypersurfaceToBase F hF).residueDegree P.1 =
        EffectiveZeroCycle.degree (hypersurfaceToBase F hF) z :=
  effectiveCycle_degree_four_or_five_min_three_single (hypersurfaceToBase F hF) z
    hdegree (fun P _ => cubic_no_section_closedPoint_degree_ge_three F hF hnone P)

end PfaffianDescent
