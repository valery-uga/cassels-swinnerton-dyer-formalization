import PfaffianDescent.ProjectiveDescent
import PfaffianDescent.ClosedPointFields
import PfaffianDescent.SectionCycles

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u

section
variable {K : Type u} [Field K] [CharZero K]

/-- An effective cycle of closed points of degree four or five on the actual
projective cubic scheme gives a rational section. -/
theorem projective_cubic_closed_point_cycle_descent
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (z : AllCharacteristics.EffectiveZeroCycle (hypersurface f hf))
    (hz : AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = 4 ∨
      AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = 5) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  classical
  let X := hypersurface f hf
  let g := hypersurfaceToBase f hf
  let ι := ↥z.support
  let L (i : ι) : Type u := X.residueField i.val.val
  letI (i : ι) : Field (L i) := inferInstanceAs (Field (X.residueField i.val.val))
  letI (i : ι) : Algebra K (L i) := (closedPointBaseHom g i.val).toAlgebra
  haveI (i : ι) : FiniteDimensional K (L i) := (closedPoint_field_degree g i.val).1
  let q (i : ι) : Spec (.of (L i)) ⟶ X := X.fromSpecResidueField i.val.val
  have hq (i : ι) : q i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K (L i))) :=
    (closedPointBaseHom_spec g i.val).symm
  have hd : (∑ i : ι, z i.val * Module.finrank K (L i)) =
      AllCharacteristics.EffectiveZeroCycle.degree g z := by
    have hdim (i : ι) : Module.finrank K (L i) = g.residueDegree i.val.val :=
      (closedPoint_field_degree g i.val).2
    simp_rw [hdim]
    exact Finset.sum_coe_sort z.support (fun i => z i * g.residueDegree i.val)
  rcases hz with hz | hz
  · exact projective_cubic_effective_degree_four_to_point L f hf (fun i : ι => z i.val) q hq
      (hd.trans hz)
  · exact projective_cubic_effective_degree_five_to_point L f hf (fun i : ι => z i.val) q hq
      (hd.trans hz)

/-- Theorem 1.1, for the closed-point zero-cycles of a projective cubic scheme.
The theorem does not require smoothness. -/
theorem projective_cubic_effective_cycle_degree_five_to_point
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (z : AllCharacteristics.EffectiveZeroCycle (hypersurface f hf))
    (hz : AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = 5) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ :=
  projective_cubic_closed_point_cycle_descent f hf z (Or.inr hz)

/-- The effective degree-four consequence, for actual closed-point cycles. -/
theorem projective_cubic_effective_cycle_degree_four_to_point
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (z : AllCharacteristics.EffectiveZeroCycle (hypersurface f hf))
    (hz : AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = 4) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ :=
  projective_cubic_closed_point_cycle_descent f hf z (Or.inl hz)

/-- Effective degrees four and five are equivalent on the actual projective
cubic scheme. Both are also equivalent to the existence of a rational section. -/
theorem projective_cubic_effective_four_iff_five
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3) :
    (∃ z : AllCharacteristics.EffectiveZeroCycle (hypersurface f hf),
      AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = 4) ↔
    (∃ z : AllCharacteristics.EffectiveZeroCycle (hypersurface f hf),
      AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = 5) := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨s, hs⟩ := projective_cubic_effective_cycle_degree_four_to_point f hf z hz
    exact effective_cycle_of_section (hypersurfaceToBase f hf) s hs 5
  · rintro ⟨z, hz⟩
    obtain ⟨s, hs⟩ := projective_cubic_effective_cycle_degree_five_to_point f hf z hz
    exact effective_cycle_of_section (hypersurfaceToBase f hf) s hs 4

/- The descent result can be packaged directly as an equivalence with a
rational section, which is the form consumed by the later scheme arguments. -/
theorem projective_cubic_effective_degree_four_iff_rational_section
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3) :
    (∃ z : AllCharacteristics.EffectiveZeroCycle (hypersurface f hf),
      AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = 4) ↔
    (∃ s : Spec (.of K) ⟶ hypersurface f hf,
      s ≫ hypersurfaceToBase f hf = 𝟙 _) := by
  constructor
  · rintro ⟨z, hz⟩
    exact projective_cubic_effective_cycle_degree_four_to_point f hf z hz
  · rintro ⟨s, hs⟩
    exact effective_cycle_of_section (hypersurfaceToBase f hf) s hs 4

theorem projective_cubic_effective_degree_five_iff_rational_section
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3) :
    (∃ z : AllCharacteristics.EffectiveZeroCycle (hypersurface f hf),
      AllCharacteristics.EffectiveZeroCycle.degree (hypersurfaceToBase f hf) z = 5) ↔
    (∃ s : Spec (.of K) ⟶ hypersurface f hf,
      s ≫ hypersurfaceToBase f hf = 𝟙 _) := by
  constructor
  · rintro ⟨z, hz⟩
    exact projective_cubic_effective_cycle_degree_five_to_point f hf z hz
  · rintro ⟨s, hs⟩
    exact effective_cycle_of_section (hypersurfaceToBase f hf) s hs 5

end
end PfaffianDescent
