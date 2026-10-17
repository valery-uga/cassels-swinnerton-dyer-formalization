import PfaffianDescent.PointIdealSpreading
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Isolating two equations at a closed point on an affine scheme

When two germs generate the maximal ideal, noetherianity allows a principal
neighborhood on which those two equations have no other common zero.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace PfaffianDescent

universe u

/-- Membership in an affine point ideal is membership of the germ in the
maximal ideal of its local ring. -/
theorem affinePoint_primeIdeal_mem_iff
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (a : Γ(X, U)) :
    a ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔
      X.presheaf.germ U x hx a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  rw [hU.primeIdealOf_eq_map_closedPoint]
  rfl

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Two equations whose germs generate a closed point's maximal ideal have
only that common zero on some principal neighborhood of the point. -/
theorem exists_basicOpen_only_common_zero_of_span_germs_eq_maximal
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(X, U)]
    (x : X) (hx : x ∈ U) (hxclosed : IsClosed ({x} : Set X))
    (q f : Γ(X, U))
    (hspan : Ideal.span ({X.presheaf.germ U x hx q,
        X.presheaf.germ U x hx f} : Set (X.presheaf.stalk x)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧
      ∀ (z : X) (hz : z ∈ X.basicOpen s), z ≠ x →
        Ideal.span ({X.presheaf.germ U z (X.basicOpen_le s hz) q,
          X.presheaf.germ U z (X.basicOpen_le s hz) f} :
          Set (X.presheaf.stalk z)) = ⊤ := by
  let m := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let I : Ideal Γ(X, U) := Ideal.span {q, f}
  letI : m.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨x, hx⟩ hxclosed
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) m := hU.isLocalization_stalk ⟨x, hx⟩
  have hmap : m.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) ≤
      I.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) := by
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal m (X.presheaf.stalk x)]
    change IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤
      (Ideal.span {q, f}).map (X.presheaf.germ U x hx).hom
    rw [Ideal.map_span, Set.image_pair, hspan]
  obtain ⟨s, hs, hisolate⟩ :=
    exists_principal_neighborhood_isolating_maximal_ideal
      (S := X.presheaf.stalk x) I m (IsNoetherian.noetherian m) hmap
  refine ⟨s, ?_, ?_⟩
  · apply (X.mem_basicOpen s x hx).mpr
    by_contra hu
    apply hs
    apply (affinePoint_primeIdeal_mem_iff U hU x hx s).mpr
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hu
  · intro z hz hzx
    let hzU := X.basicOpen_le s hz
    let p := (hU.primeIdealOf ⟨z, hzU⟩).asIdeal
    by_contra hnot
    have hsmall := IsLocalRing.le_maximalIdeal hnot
    have hIp : I ≤ p := by
      apply Ideal.span_le.mpr
      intro a ha
      rcases Set.mem_insert_iff.mp ha with heq | ha
      · subst a
        apply (affinePoint_primeIdeal_mem_iff U hU z hzU q).mpr
        exact hsmall (Ideal.subset_span (by simp))
      · have heq := Set.mem_singleton_iff.mp ha
        subst a
        apply (affinePoint_primeIdeal_mem_iff U hU z hzU f).mpr
        exact hsmall (Ideal.subset_span (by simp))
    have hsp : s ∉ p := by
      intro h
      have hg := (affinePoint_primeIdeal_mem_iff U hU z hzU s).mp h
      have hnu : ¬ IsUnit (X.presheaf.germ U z hzU s) := by
        simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hg
      exact hnu ((X.mem_basicOpen s z hzU).mp hz)
    have hpm : p = m := hisolate p hIp hsp
    have heq : hU.primeIdealOf ⟨z, hzU⟩ = hU.primeIdealOf ⟨x, hx⟩ :=
      PrimeSpectrum.ext hpm
    apply hzx
    have h := congrArg hU.fromSpec heq
    simpa only [hU.fromSpec_primeIdealOf] using h

/-- Restricting the two equations to the isolating principal neighborhood
preserves their germs and makes their common-zero locus a single point. -/
theorem exists_affine_restricted_pair_with_only_common_zero
    {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(X, U)]
    (x : X) (hx : x ∈ U) (hxclosed : IsClosed ({x} : Set X))
    (q f : Γ(X, U))
    (hspan : Ideal.span ({X.presheaf.germ U x hx q,
        X.presheaf.germ U x hx f} : Set (X.presheaf.stalk x)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    ∃ (W : X.Opens) (_hW : IsAffineOpen W) (hxW : x ∈ W)
      (qW fW : Γ(X, W)), W ≤ U ∧
      X.presheaf.germ W x hxW qW = X.presheaf.germ U x hx q ∧
      X.presheaf.germ W x hxW fW = X.presheaf.germ U x hx f ∧
      ∀ (z : X) (hz : z ∈ W), z ≠ x →
        Ideal.span ({X.presheaf.germ W z hz qW,
          X.presheaf.germ W z hz fW} : Set (X.presheaf.stalk z)) = ⊤ := by
  obtain ⟨s, hxs, hzero⟩ :=
    exists_basicOpen_only_common_zero_of_span_germs_eq_maximal U hU x hx hxclosed q f hspan
  let W := X.basicOpen s
  let hWU : W ≤ U := X.basicOpen_le s
  let qW := X.presheaf.map (homOfLE hWU).op q
  let fW := X.presheaf.map (homOfLE hWU).op f
  refine ⟨W, hU.basicOpen s, hxs, qW, fW, hWU, ?_, ?_, ?_⟩
  · exact X.presheaf.germ_res_apply (homOfLE hWU) x hxs q
  · exact X.presheaf.germ_res_apply (homOfLE hWU) x hxs f
  · intro z hz hzx
    dsimp only [qW, fW]
    rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]
    exact hzero z hz hzx

end PfaffianDescent
