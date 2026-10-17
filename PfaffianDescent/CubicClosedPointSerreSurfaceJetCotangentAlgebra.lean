import PfaffianDescent.CubicClosedPointSerreSurfaceJets
import Mathlib.RingTheory.Ideal.Cotangent

/-! # Derivatives of an actual square-zero algebra quotient

This algebra layer constructs the residue ideal, the derivative on it, and
its cotangent quotient. Identifying this quotient with Γ of the actual point
pullback of the twisted ideal sheaf remains a separate geometric adapter.
-/
noncomputable section
open TrivSqZeroExt
namespace PfaffianDescent
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
set_option backward.isDefEq.respectTransparency false

abbrev cubicClosedPointSerreSurfaceJetCotangent_residueMap
    (φ : A →ₐ[K] CubicSurfaceFirstJet K) : A →ₐ[K] K :=
  (TrivSqZeroExt.fstHom K K (Fin 2 → K)).comp φ

abbrev cubicClosedPointSerreSurfaceJetCotangent_ideal
    (φ : A →ₐ[K] CubicSurfaceFirstJet K) : Ideal A :=
  RingHom.ker (cubicClosedPointSerreSurfaceJetCotangent_residueMap φ).toRingHom

/-- The residue ideal is maximal without any supplied maximality premise. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_ideal_isMaximal
    (φ : A →ₐ[K] CubicSurfaceFirstJet K) :
    (cubicClosedPointSerreSurfaceJetCotangent_ideal φ).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨algebraMap K A c, by simp⟩

/-- The actual derivative on the actual residue ideal. -/
def cubicClosedPointSerreSurfaceJetCotangent_derivative
    (φ : A →ₐ[K] CubicSurfaceFirstJet K) :
    cubicClosedPointSerreSurfaceJetCotangent_ideal φ →ₗ[K] (Fin 2 → K) :=
  (TrivSqZeroExt.sndHom K (Fin 2 → K)).comp
    (φ.toLinearMap.domRestrict
      ((cubicClosedPointSerreSurfaceJetCotangent_ideal φ).restrictScalars K))

/-- Products of two elements of the residue ideal have zero derivative. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_derivative_mul
    (φ : A →ₐ[K] CubicSurfaceFirstJet K)
    (a b : cubicClosedPointSerreSurfaceJetCotangent_ideal φ) :
    cubicClosedPointSerreSurfaceJetCotangent_derivative φ (a * b) = 0 := by
  have ha : (φ a.1).fst = 0 := a.2
  have hb : (φ b.1).fst = 0 := b.2
  change (φ (a.1 * b.1)).snd = 0
  rw [map_mul, TrivSqZeroExt.snd_mul, ha, hb]
  simp

/-- The derivative kills the actual ideal square, as a submodule of the ideal. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_derivative_square_zero
    (φ : A →ₐ[K] CubicSurfaceFirstJet K)
    (a : cubicClosedPointSerreSurfaceJetCotangent_ideal φ)
    (ha : a ∈ cubicClosedPointSerreSurfaceJetCotangent_ideal φ •
      (⊤ : Submodule A (cubicClosedPointSerreSurfaceJetCotangent_ideal φ))) :
    cubicClosedPointSerreSurfaceJetCotangent_derivative φ a = 0 := by
  refine Submodule.smul_induction_on ha (fun r hr y _ => ?_) (fun y z hy hz => ?_)
  · exact cubicClosedPointSerreSurfaceJetCotangent_derivative_mul φ ⟨r, hr⟩ y
  · rw [map_add, hy, hz, add_zero]

/-- A surjective actual square-zero quotient has a surjective ideal derivative. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_derivative_surjective
    (φ : A →ₐ[K] CubicSurfaceFirstJet K) (hφ : Function.Surjective φ) :
    Function.Surjective (cubicClosedPointSerreSurfaceJetCotangent_derivative φ) := by
  intro v
  obtain ⟨a, ha⟩ := hφ (inr v)
  have hm : a ∈ cubicClosedPointSerreSurfaceJetCotangent_ideal φ := by
    change (φ a).fst = 0
    rw [ha]
    rfl
  refine ⟨⟨a, hm⟩, ?_⟩
  change (φ a).snd = v
  rw [ha]
  rfl

/-- The literal derivative descends to the actual cotangent quotient. -/
def cubicClosedPointSerreSurfaceJetCotangent_map
    (φ : A →ₐ[K] CubicSurfaceFirstJet K) :
    (cubicClosedPointSerreSurfaceJetCotangent_ideal φ).Cotangent →ₗ[K] (Fin 2 → K) := by
  let m := cubicClosedPointSerreSurfaceJetCotangent_ideal φ
  let N : Submodule A m := m • ⊤
  exact (N.restrictScalars K).liftQ
    (cubicClosedPointSerreSurfaceJetCotangent_derivative φ)
    (by intro a ha; exact cubicClosedPointSerreSurfaceJetCotangent_derivative_square_zero φ a ha)

end PfaffianDescent
