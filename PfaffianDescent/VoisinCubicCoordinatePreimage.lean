import PfaffianDescent.VoisinCubicQuotientRawCechExt

/-!
# Coordinate opens of a cubic hypersurface as ambient preimages

The hypersurface immersion pulls each standard coordinate open of projective
three-space back to the corresponding intrinsic coordinate open.  The same
holds for every finite ordered intersection used in the Cech complexes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent

universe u

/-- Scheme-theoretic preimage preserves a finite infimum of opens. -/
lemma schemePreimage_finset_inf {X Y : Scheme.{u}} (g : X ⟶ Y)
    {α : Type} (s : Finset α) (U : α → Y.Opens) :
    g ⁻¹ᵁ (s.inf U) = s.inf (fun i => g ⁻¹ᵁ U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.inf_empty, Scheme.Hom.preimage_top]
  | insert a s ha ih =>
      rw [Finset.inf_insert, Finset.inf_insert, Scheme.Hom.preimage_inf, ih]

/-- Scheme-theoretic preimage preserves an infimum indexed by a finite type. -/
lemma schemePreimage_iInf_finite {X Y : Scheme.{u}} (g : X ⟶ Y)
    {α : Type} [Fintype α] (U : α → Y.Opens) :
    g ⁻¹ᵁ (⨅ i, U i) = ⨅ i, g ⁻¹ᵁ U i := by
  classical
  rw [← show Finset.univ.inf U = ⨅ i, U i by
        simp [Finset.inf_eq_iInf],
    schemePreimage_finset_inf]
  simp [Finset.inf_eq_iInf]

namespace ProjectiveNegativeTwist

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- A cubic hypersurface immersion pulls a standard ambient coordinate open
back to the corresponding intrinsic quotient-coordinate open. -/
theorem hypersurfaceToAmbient_preimage_p3StandardOpen
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4) :
    (hypersurfaceToAmbient p hp) ⁻¹ᵁ p3StandardOpen K j =
      quotientCoordinateOpen (equationIdeal p hp) j := by
  let I := equationIdeal p hp
  have h := Proj.map_preimage_basicOpen
    (quotientGradedRingHom I)
    (irrelevant_le_map_quotientGradedRingHom I) (X j)
  rw [quotientGradedRingHom_coordinate] at h
  exact h

/-- The pullback of every ordered finite intersection in the ambient
coordinate cover is the matching intrinsic intersection on the cubic. -/
theorem hypersurfaceToAmbient_preimage_p3CechProduct
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (f : Fin (n + 1) → Fin 4) :
    (hypersurfaceToAmbient p hp) ⁻¹ᵁ
        (∏ᶜ fun a : Fin (n + 1) => p3StandardOpen K (f a)) =
      ∏ᶜ fun a : Fin (n + 1) =>
        quotientCoordinateOpen (equationIdeal p hp) (f a) := by
  rw [p3CechProduct_eq_inf, quotientCechProduct_eq_inf,
    schemePreimage_iInf_finite]
  apply iInf_congr
  intro a
  exact hypersurfaceToAmbient_preimage_p3StandardOpen K p hp (f a)

/-- On an ambient open, sections of a pushed-forward module are literally
sections of the original module on its preimage, as additive groups. -/
noncomputable def pushforwardOpenSectionsAddEquiv
    {X Y : Scheme.{u}} (g : X ⟶ Y) (M : X.Modules) (U : Y.Opens) :
    ((Scheme.Modules.pushforward g).obj M).presheaf.obj (op U) ≃+
      M.presheaf.obj (op (g ⁻¹ᵁ U)) :=
  AddEquiv.refl _

/-- The preceding identification commutes with restriction to a smaller
ambient open. -/
theorem pushforwardOpenSectionsAddEquiv_restrict
    {X Y : Scheme.{u}} (g : X ⟶ Y) (M : X.Modules)
    {U V : Y.Opens} (h : U ≤ V)
    (x : ((Scheme.Modules.pushforward g).obj M).presheaf.obj (op V)) :
    pushforwardOpenSectionsAddEquiv g M U
        (((Scheme.Modules.pushforward g).obj M).presheaf.map
          (homOfLE h).op x) =
      M.presheaf.map
        (homOfLE (show g ⁻¹ᵁ U ≤ g ⁻¹ᵁ V from g.preimage_mono h)).op
        (pushforwardOpenSectionsAddEquiv g M V x) := by
  rfl

end ProjectiveNegativeTwist
end PfaffianDescent
