import AllCharacteristics.ProjectiveCoefficientMap

/-!
# Composition of projective coefficient changes

Coefficient maps on homogeneous coordinate rings and on actual projective
schemes respect identity and composition. These identities give the functorial
compatibility needed when comparing restrictions on triple coefficient-chart
overlaps.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Equal admissible graded maps induce the same actual projective morphism. -/
theorem projMap_congr
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ S))
    (φ ψ : grading I →+*ᵍ grading J)
    (hφ : HomogeneousIdeal.irrelevant (grading J) ≤
      (HomogeneousIdeal.irrelevant (grading I)).map φ)
    (hψ : HomogeneousIdeal.irrelevant (grading J) ≤
      (HomogeneousIdeal.irrelevant (grading I)).map ψ)
    (h : φ = ψ) : Proj.map φ hφ = Proj.map ψ hψ := by
  subst ψ
  rfl

/-- Identity coefficient change preserves each homogeneous defining ideal. -/
theorem coefficientIdeal_id (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R)) :
    I.toIdeal.map (MvPolynomial.map (RingHom.id R)) = I.toIdeal := by
  have h : (MvPolynomial.map (RingHom.id R) : MvPolynomial σ R →+* MvPolynomial σ R) =
      RingHom.id _ := RingHom.ext MvPolynomial.map_id
  rw [h, Ideal.map_id]

/-- Identity coefficient change is the identity on the homogeneous coordinate ring. -/
theorem coordinateCoefficientMap_id
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R)) :
    coordinateCoefficientMap (RingHom.id R) I I (coefficientIdeal_id I) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [coordinateCoefficientMap_mk, MvPolynomial.map_id]
  rfl

/-- Identity coefficient change is the identity graded homomorphism. -/
theorem gradedCoefficientMap_id
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R)) :
    gradedCoefficientMap (RingHom.id R) I I (coefficientIdeal_id I) = GradedRingHom.id (grading I) := by
  apply GradedRingHom.ext
  intro x
  exact DFunLike.congr_fun (coordinateCoefficientMap_id I) x

/-- Identity coefficient change induces the identity on the actual projective scheme. -/
theorem projectiveCoefficientMap_id
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R)) :
    projectiveCoefficientMap (RingHom.id R) I I (coefficientIdeal_id I) = 𝟙 (scheme I) := by
  exact (projMap_congr I I (gradedCoefficientMap (RingHom.id R) I I (coefficientIdeal_id I))
    (GradedRingHom.id (grading I))
    (irrelevant_le_map_gradedCoefficientMap (RingHom.id R) I I (coefficientIdeal_id I))
    (by simp) (gradedCoefficientMap_id I)).trans Proj.map_id

variable (f : R →+* S) (g : S →+* T)
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
variable (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ S))
variable (K : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ T))
variable (hf : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal)
variable (hg : J.toIdeal.map (MvPolynomial.map g) = K.toIdeal)

include hf hg in
/-- Compatible successive coefficient changes give the expected composite ideal. -/
theorem coefficientIdeal_comp : I.toIdeal.map (MvPolynomial.map (g.comp f)) = K.toIdeal := by
  have h : (MvPolynomial.map (g.comp f) : MvPolynomial σ R →+* MvPolynomial σ T) =
      (MvPolynomial.map g).comp (MvPolynomial.map f) :=
    RingHom.ext (fun p ↦ (MvPolynomial.map_map f g p).symm)
  rw [h, ← Ideal.map_map, hf, hg]

/-- Coefficient maps on homogeneous coordinate rings compose as their base maps do. -/
theorem coordinateCoefficientMap_comp :
    (coordinateCoefficientMap g J K hg).comp (coordinateCoefficientMap f I J hf) =
      coordinateCoefficientMap (g.comp f) I K (coefficientIdeal_comp f g I J K hf hg) := by
  apply RingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change coordinateCoefficientMap g J K hg
    (coordinateCoefficientMap f I J hf (Ideal.Quotient.mk I.toIdeal p)) = _
  rw [coordinateCoefficientMap_mk, coordinateCoefficientMap_mk,
    coordinateCoefficientMap_mk, MvPolynomial.map_map]

/-- The corresponding graded coefficient homomorphisms obey composition. -/
theorem gradedCoefficientMap_comp :
    (gradedCoefficientMap g J K hg).comp (gradedCoefficientMap f I J hf) =
      gradedCoefficientMap (g.comp f) I K (coefficientIdeal_comp f g I J K hf hg) := by
  apply GradedRingHom.ext
  intro x
  exact DFunLike.congr_fun (coordinateCoefficientMap_comp f g I J K hf hg) x

/-- Actual projective coefficient morphisms compose contravariantly. -/
theorem projectiveCoefficientMap_comp :
    projectiveCoefficientMap g J K hg ≫ projectiveCoefficientMap f I J hf =
      projectiveCoefficientMap (g.comp f) I K (coefficientIdeal_comp f g I J K hf hg) := by
  exact (Proj.map_comp (gradedCoefficientMap f I J hf) (gradedCoefficientMap g J K hg)
    (irrelevant_le_map_gradedCoefficientMap f I J hf)
    (irrelevant_le_map_gradedCoefficientMap g J K hg)).symm.trans
      (projMap_congr I K
        ((gradedCoefficientMap g J K hg).comp (gradedCoefficientMap f I J hf))
        (gradedCoefficientMap (g.comp f) I K (coefficientIdeal_comp f g I J K hf hg))
        (HomogeneousIdeal.irrelevant_le_map_comp
          (irrelevant_le_map_gradedCoefficientMap f I J hf)
          (irrelevant_le_map_gradedCoefficientMap g J K hg))
        (irrelevant_le_map_gradedCoefficientMap (g.comp f) I K
          (coefficientIdeal_comp f g I J K hf hg))
        (gradedCoefficientMap_comp f g I J K hf hg))

end HomogeneousProjective
end AllCharacteristics
