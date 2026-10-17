import PfaffianDescent.MultivariateCubic
import PfaffianDescent.QuarticMultivariate
import AllCharacteristics.ProjectivePoints

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u v

section
variable {K : Type u} [Field K]

/-- A rational homogeneous zero gives a section of the actual projective cubic scheme. -/
theorem cubic_projective_section_of_coordinates (f : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (x : Vec K 4) (hx : x ≠ 0) (hF : MvPolynomial.eval x f = 0) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  obtain ⟨s, hs⟩ := hypersurface_point_of_coordinates (RingHom.id K) f hf x hx hF
  refine ⟨s, ?_⟩
  simpa using hs

end

section
variable {K : Type u} [Field K] [CharZero K]

/-- Degree-five descent for actual field-valued points of the projective cubic scheme. -/
theorem projective_cubic_degree_five_descent {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] (hdim : Module.finrank K L = 5)
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface f hf)
    (hq : q ≫ hypersurfaceToBase f hf = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  obtain ⟨p, hp, hF⟩ := hypersurface_coordinates_of_point (algebraMap K L) f hf q hq
  obtain ⟨x, hx, hFx⟩ := homogeneous_cubic_degree_five_descent f hf hdim p hp hF
  exact cubic_projective_section_of_coordinates f hf x hx hFx

/-- Degree-four descent for actual field-valued points of the projective cubic scheme. -/
theorem projective_cubic_degree_four_descent {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] (hdim : Module.finrank K L = 4)
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface f hf)
    (hq : q ≫ hypersurfaceToBase f hf = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  obtain ⟨p, hp, hF⟩ := hypersurface_coordinates_of_point (algebraMap K L) f hf q hq
  obtain ⟨x, hx, hFx⟩ := homogeneous_cubic_degree_four_descent f hf hdim p hp hF
  exact cubic_projective_section_of_coordinates f hf x hx hFx

/-- An effective family of actual projective scheme points with total degree five
produces a section over the base field. -/
theorem projective_cubic_effective_degree_five_to_point {ι : Type v} [Fintype ι]
    (L : ι → Type u) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    [∀ i, FiniteDimensional K (L i)]
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3) (w : ι → ℕ)
    (q : ∀ i, Spec (.of (L i)) ⟶ hypersurface f hf)
    (hq : ∀ i, q i ≫ hypersurfaceToBase f hf =
      Spec.map (CommRingCat.ofHom (algebraMap K (L i))))
    (hdegree : ∑ i, w i * Module.finrank K (L i) = 5) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  choose p hp hF using fun i => hypersurface_coordinates_of_point
    (algebraMap K (L i)) f hf (q i) (hq i)
  obtain ⟨x, hx, hFx⟩ := homogeneous_cubic_effective_degree_five_to_point L f hf w p
    (fun i _ => hp i) (fun i _ => hF i) hdegree
  exact cubic_projective_section_of_coordinates f hf x hx hFx

/-- The analogous effective-degree-four statement for actual projective scheme points. -/
theorem projective_cubic_effective_degree_four_to_point {ι : Type v} [Fintype ι]
    (L : ι → Type u) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    [∀ i, FiniteDimensional K (L i)]
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3) (w : ι → ℕ)
    (q : ∀ i, Spec (.of (L i)) ⟶ hypersurface f hf)
    (hq : ∀ i, q i ≫ hypersurfaceToBase f hf =
      Spec.map (CommRingCat.ofHom (algebraMap K (L i))))
    (hdegree : ∑ i, w i * Module.finrank K (L i) = 4) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  choose p hp hF using fun i => hypersurface_coordinates_of_point
    (algebraMap K (L i)) f hf (q i) (hq i)
  obtain ⟨x, hx, hFx⟩ := homogeneous_cubic_effective_degree_four_to_point L f hf w p
    (fun i _ => hp i) (fun i _ => hF i) hdegree
  exact cubic_projective_section_of_coordinates f hf x hx hFx

end
end PfaffianDescent
