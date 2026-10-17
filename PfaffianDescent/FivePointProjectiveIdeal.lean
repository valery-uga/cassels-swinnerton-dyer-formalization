import PfaffianDescent.FivePointResolution

namespace PfaffianDescent
open MvPolynomial
section
variable {K : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma fivePointGeneralPosition_ne_zero (p : Fin 5 → (Fin 4 → K))
    (hp : FivePointGeneralPosition p) (i : Fin 5) : p i ≠ 0 := by
  let e : Fin 4 → Fin 5 := fun j => Equiv.swap 0 i j.castSucc
  have he : Function.Injective e :=
    (Equiv.swap 0 i).injective.comp (Fin.castSucc_injective 4)
  have h := (hp e he).ne_zero (0 : Fin 4)
  change p (Equiv.swap 0 i 0) ≠ 0 at h
  rwa [Equiv.swap_apply_left] at h

/-- The actual projective points of an arbitrary general-position frame. -/
noncomputable def fivePointProjectiveMap (p : Fin 5 → (Fin 4 → K))
    (hp : FivePointGeneralPosition p) (i : Fin 5) :
    ProjectiveSpectrum (homogeneousSubmodule (Fin 4) K) :=
  projectiveVectorPoint (p i) (fivePointGeneralPosition_ne_zero p hp i)

/-- The ideal resolved above is the actual projective vanishing ideal of the five points. -/
theorem five_point_projective_vanishing_ideal (p : Fin 5 → (Fin 4 → K))
    (hp : FivePointGeneralPosition p) :
    (ProjectiveSpectrum.vanishingIdeal (Set.range (fivePointProjectiveMap p hp))).toIdeal =
      fiveVectorIdeal p := by
  ext f
  change f ∈ ProjectiveSpectrum.vanishingIdeal (Set.range (fivePointProjectiveMap p hp)) ↔ _
  rw [ProjectiveSpectrum.mem_vanishingIdeal]
  change (∀ x, x ∈ Set.range (fivePointProjectiveMap p hp) → f ∈ x.asHomogeneousIdeal) ↔
    f ∈ ⨅ i : Fin 5, (vectorLineIdeal (p i)).toIdeal
  rw [Submodule.mem_iInf]
  constructor
  · intro h i
    exact h (fivePointProjectiveMap p hp i) (Set.mem_range_self i)
  · intro h x hx
    obtain ⟨i, rfl⟩ := hx
    exact h i

end
end PfaffianDescent
