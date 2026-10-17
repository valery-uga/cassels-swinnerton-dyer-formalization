import AllCharacteristics.CubicDegreeOneFieldDescent
import AllCharacteristics.FinitelyGeneratedDVRLifting
import AllCharacteristics.DVRSourceCycleLifting
import AllCharacteristics.HomogeneousSpecialization

/-!
# Constructed reduction of the degree-one problem to characteristic zero

For a nonzero smooth cubic over any field with a signed degree-one cycle,
construct a nonzero smooth cubic in characteristic zero with a signed
degree-one cycle. Any rational coordinate point on the constructed cubic
specializes and maps back to a point on the original cubic. The proof supplies
the finite coefficient model, complete DVR, smooth family, and generic cycle;
it does not assume the characteristic-zero rational-point theorem.
-/

open AlgebraicGeometry IsLocalRing
namespace AllCharacteristics
open HomogeneousProjective
universe u

/-- Every degree-one zero-cycle problem for a nonzero smooth cubic surface
over an arbitrary field reduces to a constructed such problem in
characteristic zero, with a proved implication on rational coordinates. -/
theorem exists_charZero_smooth_cubic_degree_one_reduction
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp)) (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ (K : Type u) (_ : Field K) (_ : CharZero K)
      (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous 3),
      q ≠ 0 ∧ Smooth (hypersurfaceToBase q hq) ∧
      (∃ w : ZeroCycle (hypersurface q hq), ZeroCycle.degree (hypersurfaceToBase q hq) w = 1) ∧
      ((∃ y : Fin 4 → K, y ≠ 0 ∧ q.eval y = 0) →
        ∃ x : Fin 4 → k, x ≠ 0 ∧ p.eval x = 0) := by
  rcases CharP.exists' k with hzero | ⟨ℓ, hprime, hchar⟩
  · exact ⟨k, inferInstance, inferInstance, p, hp, hne, inferInstance, ⟨z, hz⟩, fun h ↦ h⟩
  · obtain ⟨F, hF, q₀, hq₀, hmap, hq₀ne, hs₀, z₀, hz₀⟩ :=
      exists_fg_subfield_smooth_cubic_degree_one_model p hp hne z hz
    have : Field.FG F := hF
    have : Smooth (hypersurfaceToBase q₀ hq₀) := hs₀
    obtain ⟨R, _, _, _, _, _, b, hb⟩ := hasCompleteCharZeroDVRLift_of_fg_positive ℓ F
    let K := FractionRing R
    let g := algebraMap R K
    obtain ⟨qR, hqR, hred, _, hsK, w, hw⟩ :=
      exists_smooth_lift_with_zeroCycle b hb g q₀ hq₀ hq₀ne z₀
    have hqne : qR.map g ≠ 0 := by
      intro hzero
      have hRzero : qR = 0 := (MvPolynomial.map_injective g (IsFractionRing.injective R K))
        (hzero.trans (map_zero (MvPolynomial.map g)).symm)
      apply hq₀ne
      rw [← hred, hRzero, map_zero]
    refine ⟨K, inferInstance, inferInstance, qR.map g, hqR.map g, hqne, hsK,
      ⟨w, hw.trans hz₀⟩, ?_⟩
    rintro ⟨v, hv, heval⟩
    have hg : qR.eval₂ g v = 0 := by
      rw [MvPolynomial.eval₂_eq_eval_map]
      exact heval
    obtain ⟨y, hy, hey⟩ := specialize_homogeneous_polynomial qR hqR b v hv hg
    have hyq : q₀.eval y = 0 := by
      rw [MvPolynomial.eval₂_eq_eval_map, hred] at hey
      exact hey
    refine ⟨F.subtype ∘ y, ?_, ?_⟩
    · intro hzero
      apply hy
      funext i
      apply F.subtype.injective
      exact (congrFun hzero i).trans (map_zero F.subtype).symm
    · rw [← hmap, MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp, hyq, map_zero]

end AllCharacteristics
