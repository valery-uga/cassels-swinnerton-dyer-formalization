import PfaffianDescent.SmoothPointParameterPair
import PfaffianDescent.AffinePointIdealSpreading
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Affine Koszul parameters near a regular surface point

Local regular parameters can be represented by sections and restricted to
an affine neighborhood where their only common zero is the chosen point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

namespace PfaffianDescent

universe u

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- A closed regular surface point has an affine two-equation presentation,
inside any prescribed open neighborhood, regular at the point and with no
other common zero. -/
theorem exists_affine_point_koszul_parameters
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (x : X) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (hxclosed : IsClosed ({x} : Set X)) (O : X.Opens) (hxO : x ∈ O) :
    ∃ (W : X.Opens) (_hW : IsAffineOpen W) (hxW : x ∈ W)
      (q f : Γ(X, W)), W ≤ O ∧
      X.presheaf.germ W x hxW q ∈ (X.presheaf.stalk x)⁰ ∧
      Ideal.Quotient.mk (Ideal.span {X.presheaf.germ W x hxW q})
          (X.presheaf.germ W x hxW f) ∈
        ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ W x hxW q})⁰ ∧
      Ideal.span ({X.presheaf.germ W x hxW q,
          X.presheaf.germ W x hxW f} : Set (X.presheaf.stalk x)) =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
      ∀ (z : X) (hz : z ∈ W), z ≠ x →
        Ideal.span ({X.presheaf.germ W z hz q,
          X.presheaf.germ W z hz f} : Set (X.presheaf.stalk z)) = ⊤ := by
  obtain ⟨p, r, hpreg, hrreg, hspan⟩ :=
    exists_regular_pair_span_maximalIdeal_of_dim_two hdim
  obtain ⟨U, hxU, qU, hqU⟩ := X.presheaf.exists_germ_eq p
  obtain ⟨V, hxV, fV, hfV⟩ := X.presheaf.exists_germ_eq r
  let N := U ⊓ V ⊓ O
  have hxN : x ∈ N := ⟨⟨hxU, hxV⟩, hxO⟩
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAN⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxN N.isOpen
  have hAU : A ≤ U := hAN.trans (inf_le_left.trans inf_le_left)
  have hAV : A ≤ V := hAN.trans (inf_le_left.trans inf_le_right)
  have hAO : A ≤ O := hAN.trans inf_le_right
  let qA := X.presheaf.map (homOfLE hAU).op qU
  let fA := X.presheaf.map (homOfLE hAV).op fV
  have hqA : X.presheaf.germ A x hxA qA = p := by
    rw [X.presheaf.germ_res_apply]
    exact hqU
  have hfA : X.presheaf.germ A x hxA fA = r := by
    rw [X.presheaf.germ_res_apply]
    exact hfV
  letI : IsNoetherianRing Γ(X, A) :=
    IsLocallyNoetherian.component_noetherian ⟨A, hA⟩
  obtain ⟨W, hW, hxW, q, f, hWA, hq, hf, hzero⟩ :=
    exists_affine_restricted_pair_with_only_common_zero
      A hA x hxA hxclosed qA fA (by rw [hqA, hfA]; exact hspan)
  have hq' : X.presheaf.germ W x hxW q = p := hq.trans hqA
  have hf' : X.presheaf.germ W x hxW f = r := hf.trans hfA
  refine ⟨W, hW, hxW, q, f, hWA.trans hAO, ?_, ?_, ?_, hzero⟩
  · rw [hq']
    exact hpreg
  · rw [hq', hf']
    exact hrreg
  · rw [hq', hf']
    exact hspan

end PfaffianDescent
