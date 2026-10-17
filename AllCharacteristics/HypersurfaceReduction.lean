import AllCharacteristics.ProjectiveBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Exact special-fiber identification for a lifted homogeneous equation

An equality between the reduced polynomial and a specified source equation
identifies their actual projective schemes. The resulting map is Cartesian
over the coefficient spectra and is a closed immersion for a surjective
coefficient map.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R k : Type u} {σ : Type} [CommRing R] [CommRing k]
variable (b : R →+* k) (q : MvPolynomial σ R) {d : ℕ} (hq : q.IsHomogeneous d)
variable (p : MvPolynomial σ k) (hp : p.IsHomogeneous d) (he : q.map b = p)

/-- A specified reduced equation defines exactly the scheme-theoretic fiber
of the lifted hypersurface. -/
noncomputable def hypersurfaceReductionIso :
    hypersurface p hp ≅ pullback (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom b)) := by
  subst p
  exact hypersurfaceBaseChangeIso b q hq

/-- The exact reduction isomorphism is over the residue coefficient ring. -/
theorem hypersurfaceReductionIso_hom_snd :
    (hypersurfaceReductionIso b q hq p hp he).hom ≫
      pullback.snd (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom b)) =
        hypersurfaceToBase p hp := by
  subst p
  exact hypersurfaceBaseChangeIso_hom_snd b q hq

/-- The inclusion of the specified reduced hypersurface into the lifted
family, defined by the actual special-fiber isomorphism. -/
noncomputable def hypersurfaceReductionMap : hypersurface p hp ⟶ hypersurface q hq :=
  (hypersurfaceReductionIso b q hq p hp he).hom ≫
    pullback.fst (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom b))

/-- The reduction inclusion respects the coefficient structure maps. -/
theorem hypersurfaceReductionMap_toBase :
    hypersurfaceReductionMap b q hq p hp he ≫ hypersurfaceToBase q hq =
      hypersurfaceToBase p hp ≫ Spec.map (CommRingCat.ofHom b) := by
  rw [hypersurfaceReductionMap, Category.assoc, pullback.condition,
    ← Category.assoc, hypersurfaceReductionIso_hom_snd]

/-- The source hypersurface is the entire fiber of the lifted family. -/
theorem isPullback_hypersurfaceReductionMap :
    IsPullback (hypersurfaceReductionMap b q hq p hp he) (hypersurfaceToBase p hp)
      (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom b)) :=
  IsPullback.of_iso_pullback ⟨hypersurfaceReductionMap_toBase b q hq p hp he⟩
    (hypersurfaceReductionIso b q hq p hp he) rfl
    (hypersurfaceReductionIso_hom_snd b q hq p hp he)

/-- For a surjective coefficient map the exact special-fiber inclusion is
a closed immersion. -/
theorem isClosedImmersion_hypersurfaceReductionMap (hb : Function.Surjective b) :
    IsClosedImmersion (hypersurfaceReductionMap b q hq p hp he) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom b)) :=
    IsClosedImmersion.spec_of_surjective _ hb
  unfold hypersurfaceReductionMap
  infer_instance

end HomogeneousProjective
end AllCharacteristics
