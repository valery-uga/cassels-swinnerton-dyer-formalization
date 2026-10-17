import PfaffianDescent.ActualHomogeneousQuadraticOverlapFraction
import PfaffianDescent.ProjectivePositiveTwist

/- SOURCE ONLY / UNVERIFIED. TRUE positive-twist basis section transition
on the actual homogeneous product open, proved by localization values.
No supplied generator/unit-transition comparison is an input. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory Opposite HomogeneousLocalization
open AllCharacteristics.GradedChart
universe u
variable {K A : Type u} [CommRing K] [CommRing A] [Algebra K A]
  (G : ℕ → Submodule K A) [GradedRing G]
  {f g : A} (hf : f ∈ G 1) (hg : g ∈ G 1)

lemma actualPositiveTwo_overlap_basis_section
    : let W := Proj.basicOpen G (f * g)
      let ratio := (Proj.awayToSection G (f * g)).hom
        (awayMap G hg rfl (normalized G hf g hg))
      let f2 : G 2 := ⟨f ^ 2, by simpa using pow_mem_graded 2 hf⟩
      let g2 : G 2 := ⟨g ^ 2, by simpa using pow_mem_graded 2 hg⟩
      ratio ^ 2 • (positiveGlobalSectionOfHomogeneous G 2 f2).val (op W) =
        (positiveGlobalSectionOfHomogeneous G 2 g2).val (op W) := by
  dsimp only
  apply Subtype.ext
  funext x
  change (((Proj.awayToSection G (f * g)).hom
      (awayMap G hg rfl (normalized G hf g hg))).val x).val ^ 2 *
      Localization.mk (f ^ 2) (1 : (positivePointIdeal G x.1).primeCompl) =
        Localization.mk (g ^ 2) (1 : (positivePointIdeal G x.1).primeCompl)
  have hval := ProjectiveSpectrum.Proj.awayToSection_apply G (f * g)
    (awayMap G hg rfl (normalized G hf g hg)) x
  erw [hval, val_awayMap_normalized]
  rw [Localization.mk_eq_mk', IsLocalization.map_mk']
  simp only [RingHom.id_apply]
  rw [← Localization.mk_eq_mk']
  simp only [pow_two, Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  rw [Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

end PfaffianDescent.ProjectiveNegativeTwist
