import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
universe u
section
variable {K A : Type u} [CommRing K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜] (z : A) (hz : z ∈ 𝒜 1)

/-- Membership of a homogeneous numerator in a projective point is membership
of its normalized fraction in the corresponding affine-chart prime. -/
theorem homogeneousChart_prime_membership
    (q : Spec (.of (Away 𝒜 z))) (n : ℕ) (a : A) (ha : a ∈ 𝒜 n) :
    a ∈ (Proj.awayι 𝒜 z hz (by decide : 0 < 1) q).asHomogeneousIdeal ↔
      Away.mk 𝒜 hz n a (by simpa using ha) ∈ q.asIdeal := by
  let E := Proj.basicOpenIsoSpec 𝒜 z hz (by decide : 0 < 1)
  let x := E.inv q
  have hx : (ProjectiveSpectrum.Proj.toSpec 𝒜 z).base x = q := by
    change E.hom (E.inv q) = q
    exact congrArg (fun f => f q) E.inv_hom_id
  have h := ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 x
    (⟨n, ⟨a, ha⟩, ⟨z^n, by simpa using SetLike.pow_mem_graded n hz⟩, ⟨n, rfl⟩⟩)
  rw [hx] at h
  have hm : HomogeneousLocalization.mk
      (⟨n, ⟨a, ha⟩, ⟨z^n, by simpa using SetLike.pow_mem_graded n hz⟩, ⟨n, rfl⟩⟩ :
        NumDenSameDeg 𝒜 (.powers z)) = Away.mk 𝒜 hz n a (by simpa using ha) := by
    apply val_injective
    rfl
  rw [hm] at h
  exact h.symm

end
end PfaffianDescent
