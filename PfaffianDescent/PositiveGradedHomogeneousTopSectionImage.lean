import PfaffianDescent.VoisinHypersurfacePositiveTwist

noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {A B ρ τ : Type u} [CommRing A] [CommRing B]
  [SetLike ρ A] [AddSubgroupClass ρ A] [SetLike τ B] [AddSubgroupClass τ B]
  (G : ℕ → ρ) (H : ℕ → τ) [GradedRing G] [GradedRing H]

private lemma nativeLocalRingHom_mk_one
    {R T : Type u} [CommRing R] [CommRing T]
    (I : Ideal R) [I.IsPrime] (J : Ideal T) [J.IsPrime]
    (f : R →+* T) (h : I = J.comap f) (r : R) :
    Localization.localRingHom I J f h (Localization.mk r (1 : I.primeCompl)) =
      Localization.mk (f r) (1 : J.primeCompl) := by
  rw [Localization.localRingHom_mk]
  congr 1
  exact Subtype.ext (map_one f)

/-- The actual native graded restriction sends a homogeneous fraction p/1
literally to f(p)/1; no section-surjectivity or comparison premise is used. -/
theorem positiveGradedHomogeneousTopSectionImage
    (f : G →+*ᵍ H)
    (hf : HomogeneousIdeal.irrelevant H ≤ (HomogeneousIdeal.irrelevant G).map f)
    (m : ℕ) (p : G m) :
    (gradedRingHomPositiveTwistToPushforward G H f hf m).app ⊤
        (PresheafOfModules.sections.eval (positiveGlobalSectionOfHomogeneous G m p) (op ⊤)) =
      PresheafOfModules.sections.eval
        (positiveGlobalSectionOfHomogeneous H m ⟨f p, f.2 p.2⟩) (op ⊤) := by
  apply Subtype.ext
  funext y
  letI : (positivePointIdeal G (Proj.map f hf y.1)).IsPrime :=
    ProjectiveSpectrum.isPrime (Proj.map f hf y.1)
  letI : (positivePointIdeal H y.1).IsPrime := ProjectiveSpectrum.isPrime y.1
  change Localization.localRingHom
      (positivePointIdeal G (Proj.map f hf y.1))
      (positivePointIdeal H y.1) f.toRingHom rfl
        (Localization.mk (p : A) (1 : (positivePointIdeal G (Proj.map f hf y.1)).primeCompl)) =
    Localization.mk (f p : B) (1 : (positivePointIdeal H y.1).primeCompl)
  exact nativeLocalRingHom_mk_one
    (positivePointIdeal G (Proj.map f hf y.1))
    (positivePointIdeal H y.1) f.toRingHom rfl (p : A)

end PfaffianDescent.ProjectiveNegativeTwist
end
