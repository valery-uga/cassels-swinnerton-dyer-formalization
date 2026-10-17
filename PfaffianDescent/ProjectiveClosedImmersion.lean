import PfaffianDescent.GradedSurjection
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
universe u
section
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)

/-- Surjective graded ring maps induce closed immersions of actual projective
schemes. The proof uses the surjective map on each homogeneous affine chart. -/
theorem projectiveMap_closedImmersion_of_surjective :
    IsClosedImmersion (Proj.map f (gradedSurjective_irrelevant_le f hf)) := by
  let h := Proj.map f (gradedSurjective_irrelevant_le f hf)
  let U : (Σ d : PNat, 𝒜 d) → (Proj 𝒜).Opens := fun s => Proj.basicOpen 𝒜 s.2
  have hU : ⨆ s, U s = ⊤ := by
    calc
      ⨆ s, U s = ⨆ s, ((Proj.affineOpenCover 𝒜).openCover.f s).opensRange := by
        apply iSup_congr
        intro s
        exact (Proj.opensRange_awayι 𝒜 (s.2 : A) s.2.2 s.1.2).symm
      _ = ⊤ := (Proj.affineOpenCover 𝒜).openCover.iSup_opensRange
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) U hU
  intro s
  change (Σ d : PNat, 𝒜 d) at s
  let eA : (U s : Scheme) ≅ Spec (.of (Away 𝒜 (s.2 : A))) :=
    Proj.basicOpenIsoSpec 𝒜 (s.2 : A) s.2.2 s.1.2
  let eB : (h ⁻¹ᵁ U s : Scheme) ≅ Spec (.of (Away ℬ (f s.2))) :=
    Proj.basicOpenIsoSpec ℬ (f s.2) (f.2 s.2.2) s.1.2
  let r : (h ⁻¹ᵁ U s : Scheme) ⟶ (U s : Scheme) := h ∣_ U s
  have he₀ : (eB.inv ≫ r) ≫ (U s).ι =
      (Spec.map (CommRingCat.ofHom (Away.map f (s.2 : A))) ≫ eA.inv) ≫ (U s).ι := by
    change (eB.inv ≫ (h ∣_ U s)) ≫ (U s).ι = _
    rw [Category.assoc, morphismRestrict_ι]
    exact Proj.awayι_comp_map f (gradedSurjective_irrelevant_le f hf) s.1.2 _ s.2.2
  have he₁ := (cancel_mono (U s).ι).mp he₀
  have he : (eB.inv ≫ r) ≫ eA.hom =
      Spec.map (CommRingCat.ofHom (Away.map f (s.2 : A))) := by
    rw [he₁, Category.assoc, eA.inv_hom_id, Category.comp_id]
  change IsClosedImmersion r
  apply (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion eB.inv r).mp
  apply (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion (eB.inv ≫ r) eA.hom).mp
  rw [he]
  exact IsClosedImmersion.spec_of_surjective _ (gradedSurjective_awayMap f hf _ s.2.2)

end
end PfaffianDescent
