import PfaffianDescent.ProjectiveDescent

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u

section
variable {K : Type u} [Field K] [NeZero (2 : K)]

/-- A Pfaffian presentation over the ground field gives a rational section of
the actual projective cubic surface. -/
theorem projective_pfaffian_to_point
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (A : Fin 4 → Mat K 6) (hA : ∀ i, IsAlternating (A i))
    (hpres : (pfaffianCubic A).toMvPolynomial = f) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  obtain ⟨x, hx, hF⟩ := pfaffian_to_point A hA
  apply cubic_projective_section_of_coordinates f hf x hx
  rw [← hpres]
  change MvPolynomial.eval₂ (RingHom.id K) x (pfaffianCubic A).toMvPolynomial = 0
  rw [Cubic.eval_toMvPolynomial]
  exact (eval_pfaffianCubic A x).trans hF

end

section
variable {K : Type u} [Field K] [CharZero K]

/-- Quadratic secant descent for field-valued points of the projective cubic scheme. -/
theorem projective_cubic_degree_le_two_descent {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] (hdim : Module.finrank K L ≤ 2)
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface f hf)
    (hq : q ≫ hypersurfaceToBase f hf = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  obtain ⟨p, hp, hF⟩ := hypersurface_coordinates_of_point (algebraMap K L) f hf q hq
  obtain ⟨c, hc⟩ := homogeneous_cubic_has_tensor f hf
  rw [← hc, Cubic.eval_toMvPolynomial] at hF
  obtain ⟨x, hx, hFx⟩ := cubic_degree_le_two_secant hdim c p hp hF
  apply cubic_projective_section_of_coordinates f hf x hx
  rw [← hc]
  exact (Cubic.eval_toMvPolynomial (RingHom.id K) c x).trans hFx

end
end PfaffianDescent
