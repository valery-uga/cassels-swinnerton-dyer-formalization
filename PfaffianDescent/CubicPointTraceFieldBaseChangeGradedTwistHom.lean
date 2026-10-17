import PfaffianDescent.VoisinHypersurfaceTwist
import PfaffianDescent.VoisinProjectiveCubicCohomology
import PfaffianDescent.BundleSectionZeroLocus
import PfaffianDescent.GradedTwistMultiplicationRestriction

/-! # Actual graded negative-twist pullback maps

These are adjoints of the actual homogeneous-fraction restriction maps.
Their zero-twist normalization and homogeneous-multiplication square are
proved directly from the underlying local-ring maps.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false

variable {A B ρ τ : Type u} [CommRing A] [CommRing B]
  [SetLike ρ A] [AddSubgroupClass ρ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒢 : ℕ → ρ) (ℋ : ℕ → τ) [GradedRing 𝒢] [GradedRing ℋ]
  (f : 𝒢 →+*ᵍ ℋ)
  (hf : HomogeneousIdeal.irrelevant ℋ ≤ (HomogeneousIdeal.irrelevant 𝒢).map f)

/-- Restriction of the zero twist is the actual structure-module restriction,
under the canonical zero-twist isomorphisms. -/
theorem cubicPointTraceFieldBaseChangeGradedTwistToPushforward_zero :
    unitToZeroTwist 𝒢 ≫ gradedRingHomTwistToPushforward 𝒢 ℋ f hf 0 =
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (Proj.map f hf) ≫
        (Scheme.Modules.pushforward (Proj.map f hf)).map (unitToZeroTwist ℋ) := by
  ext U
  apply Subtype.ext
  funext y
  change Localization.localRingHom
      (pointIdeal 𝒢 (Proj.map f hf y.1)) (pointIdeal ℋ y.1) f.toRingHom rfl
        (1 : HomogeneousLocalization.AtPrime 𝒢
          (pointIdeal 𝒢 (Proj.map f hf y.1))).val =
    (HomogeneousLocalization.localRingHom f
      (pointIdeal 𝒢 (Proj.map f hf y.1)) (pointIdeal ℋ y.1) rfl 1).val
  exact (HomogeneousLocalization.val_localRingHom _).symm

/-- Actual graded negative-twist restriction commutes with multiplication
by a homogeneous section. -/
theorem cubicPointTraceFieldBaseChangeGradedTwistToPushforward_mul
    {d : ℕ} (s : 𝒢 d) (m : ℕ) :
    mulHomogeneous 𝒢 s m ≫ gradedRingHomTwistToPushforward 𝒢 ℋ f hf m =
      gradedRingHomTwistToPushforward 𝒢 ℋ f hf (m + d) ≫
        (Scheme.Modules.pushforward (Proj.map f hf)).map
          (mulHomogeneous ℋ ⟨f s, f.2 s.2⟩ m) :=
  gradedRingHomTwistToPushforward_mulHomogeneous 𝒢 ℋ f hf s m

/-- The actual pullback morphism on negative twists, obtained from the
actual geometric pullback-pushforward adjunction. -/
def cubicPointTraceFieldBaseChangeGradedTwistPullbackHom (m : ℕ) :
    (Scheme.Modules.pullback (Proj.map f hf)).obj (sheafOfModules 𝒢 m) ⟶
      sheafOfModules ℋ m :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)).homEquiv _ _).symm
    (gradedRingHomTwistToPushforward 𝒢 ℋ f hf m)

end PfaffianDescent.ProjectiveNegativeTwist
