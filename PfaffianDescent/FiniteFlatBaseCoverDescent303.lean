import PfaffianDescent.FiniteFlatHilbertTestPoints195
import Mathlib.AlgebraicGeometry.Morphisms.Basic

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency.types false in
/-- Finiteness descends from actual Cartesian local families on a base open cover. -/
theorem finite_of_openCover_cartesian303
    {Z B : Scheme.{u}} (f : Z ⟶ B) (U : B.OpenCover.{u})
    (Z' : U.I₀ → Scheme.{u}) (a : ∀ i, Z' i ⟶ Z) (p : ∀ i, Z' i ⟶ U.X i)
    (h : ∀ i, IsPullback (a i) (p i) f (U.f i))
    (hf : ∀ i, IsFinite (p i)) : IsFinite f := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) (f := f) U
  intro i
  letI : IsFinite (p i) := hf i
  change IsFinite (pullback.snd f (U.f i))
  rw [← (h i).isoPullback_inv_snd]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- Flatness descends along the same actual Cartesian base charts. -/
theorem flat_of_openCover_cartesian303
    {Z B : Scheme.{u}} (f : Z ⟶ B) (U : B.OpenCover.{u})
    (Z' : U.I₀ → Scheme.{u}) (a : ∀ i, Z' i ⟶ Z) (p : ∀ i, Z' i ⟶ U.X i)
    (h : ∀ i, IsPullback (a i) (p i) f (U.f i))
    (hf : ∀ i, Flat (p i)) : Flat f := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @Flat) (f := f) U
  intro i
  letI : Flat (p i) := hf i
  change Flat (pullback.snd f (U.f i))
  rw [← (h i).isoPullback_inv_snd]
  infer_instance

/-- The constant rank is tested at a preimage on the actual covering chart. -/
theorem finiteFlat_rank_of_openCover_cartesian303
    {Z B : Scheme.{u}} (f : Z ⟶ B) (U : B.OpenCover.{u})
    (Z' : U.I₀ → Scheme.{u}) (a : ∀ i, Z' i ⟶ Z) (p : ∀ i, Z' i ⟶ U.X i)
    (h : ∀ i, IsPullback (a i) (p i) f (U.f i)) (n : ℕ)
    (hf : ∀ i, IsFinite (p i)) (hflat : ∀ i, Flat (p i))
    (hn : ∀ i y, (p i).finrank y = n) :
    IsFinite f ∧ Flat f ∧ ∀ y, f.finrank y = n := by
  letI : IsFinite f := finite_of_openCover_cartesian303 f U Z' a p h hf
  letI : Flat f := flat_of_openCover_cartesian303 f U Z' a p h hflat
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro y
  obtain ⟨z, hz⟩ := Scheme.Cover.covers U y
  have he := Scheme.Hom.finrank_of_isPullback (a (Scheme.Cover.idx U y))
    (p (Scheme.Cover.idx U y)) f (U.f (Scheme.Cover.idx U y))
    (h (Scheme.Cover.idx U y)) z
  rw [hz] at he
  exact he.symm.trans (hn _ z)

/-- Construct the actual Hilbert test point of a global closed family using
only its Cartesian local families and their finite-flat ranks. -/
def closedImmersionHilbertPoint_of_openCover_cartesian303
    {Z X B : Scheme.{u}} (F : X ⟶ B) (j : Z ⟶ X) [IsClosedImmersion j]
    (U : B.OpenCover.{u}) (Z' : U.I₀ → Scheme.{u})
    (a : ∀ i, Z' i ⟶ Z) (p : ∀ i, Z' i ⟶ U.X i)
    (h : ∀ i, IsPullback (a i) (p i) (j ≫ F) (U.f i)) (n : ℕ)
    (hf : ∀ i, IsFinite (p i)) (hflat : ∀ i, Flat (p i))
    (hn : ∀ i y, (p i).finrank y = n) : FiniteFlatHilbertPoint195 F n := by
  have H := finiteFlat_rank_of_openCover_cartesian303 (j ≫ F) U Z' a p h n hf hflat hn
  letI := H.1
  letI := H.2.1
  exact closedImmersionHilbertPoint195 F j n H.2.2

end PfaffianDescent
end
