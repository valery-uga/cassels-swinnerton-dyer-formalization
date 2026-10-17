import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.AffineScheme
import PfaffianDescent.SchemeDimensionFromCharts

/-!
# Krull dimension under integral extensions

An integral ring map cannot increase Krull dimension.  The proof sends a
chain of prime ideals in the target to its contractions; incomparability
preserves strict inclusions.
-/

namespace PfaffianDescent

open Order
open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits MorphismProperty

universe u

/-- The Krull dimension of the target of an integral ring homomorphism is at
most the dimension of its source. -/
theorem ringKrullDim_le_of_isIntegral {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  rw [ringKrullDim, ringKrullDim]
  letI : Algebra R S := f.toAlgebra
  have hIntegral : Algebra.IsIntegral R S := ⟨hf⟩
  letI : Algebra.IsIntegral R S := hIntegral
  apply krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro I J hIJ
  exact Ideal.IsIntegral.comap_lt_comap (R := R) (A := S) hIJ

/-- An integral morphism between affine schemes cannot increase their
topological Krull dimension. -/
theorem affineSpec_dimension_le_of_integral
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) :
    topologicalKrullDim (Spec (.of S)) ≤ topologicalKrullDim (Spec (.of R)) := by
  change topologicalKrullDim (PrimeSpectrum S) ≤ topologicalKrullDim (PrimeSpectrum R)
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_le_of_isIntegral f hf

/-- A finite affine morphism induces an integral ring map, hence its source
has dimension at most the dimension of its affine target. -/
theorem affineSpec_dimension_le_of_finite
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : IsFinite (Spec.map (CommRingCat.ofHom f))) :
    topologicalKrullDim (Spec (.of S)) ≤ topologicalKrullDim (Spec (.of R)) := by
  apply affineSpec_dimension_le_of_integral f
  letI : IsFinite (Spec.map (CommRingCat.ofHom f)) := hf
  exact (IsIntegralHom.SpecMap_iff (φ := CommRingCat.ofHom f)).mp
    (inferInstance : IsIntegralHom (Spec.map (CommRingCat.ofHom f)))

/-- A finite morphism between affine schemes cannot increase dimension.  The
proof transports it to the finite map on global sections and applies the
integral affine-spectrum result. -/
theorem finite_affine_morphism_dimension_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y] [IsFinite f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  have hfinite : (f.appTop).hom.Finite :=
    IsFinite.finite_app f ⊤ (isAffineOpen_top Y)
  have hintegral : (f.appTop).hom.IsIntegral :=
    (RingHom.finite_iff_isIntegral_and_finiteType).mp hfinite |>.1
  have hdim := affineSpec_dimension_le_of_integral f.appTop.hom hintegral
  calc
    topologicalKrullDim X =
        topologicalKrullDim (Spec Γ(X, ⊤)) :=
      IsHomeomorph.topologicalKrullDim_eq _ X.isoSpec.hom.homeomorph.isHomeomorph
    _ ≤ topologicalKrullDim (Spec Γ(Y, ⊤)) := hdim
    _ = topologicalKrullDim Y :=
      (IsHomeomorph.topologicalKrullDim_eq _
        Y.isoSpec.hom.homeomorph.isHomeomorph).symm

/-- A finite affine scheme over a field has Krull dimension at most zero. -/
theorem finite_affine_scheme_over_field_dimension_le_zero
    {K : Type u} [Field K] {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of K)) [IsFinite f] :
    topologicalKrullDim X ≤ 0 := by
  have hK : topologicalKrullDim (Spec (.of K)) = 0 := by
    change topologicalKrullDim (PrimeSpectrum K) = 0
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      ringKrullDim_eq_zero_of_field]
  exact (finite_affine_morphism_dimension_le f).trans_eq hK

/-- A finite morphism of schemes cannot increase topological Krull dimension.
Cover the source by inverse images of affine target charts and apply the affine
dimension bound on each chart. -/
theorem finite_morphism_dimension_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  let 𝒰 := Y.affineCover.pullback₁ f
  have hchart (i : Y.affineCover.I₀) :
      topologicalKrullDim (𝒰.X i) ≤ topologicalKrullDim Y := by
    let g := Y.affineCover.f i
    letI : IsAffine (Y.affineCover.X i) := inferInstance
    letI : IsAffineHom f := (inferInstance : IsFinite f).toIsAffineHom
    letI : MorphismProperty.IsStableUnderBaseChangeAlong @IsAffineHom g :=
      ⟨fun pb h => (inferInstance : MorphismProperty.IsStableUnderBaseChange
        @IsAffineHom).of_isPullback pb h⟩
    letI : IsAffineHom (pullback.snd f g) :=
      MorphismProperty.pullback_snd f g inferInstance
    letI : IsAffine (𝒰.X i) := by
      change IsAffine (pullback f g)
      exact isAffine_of_isAffineHom (pullback.snd f g)
    letI : MorphismProperty.IsStableUnderBaseChangeAlong @IsFinite g :=
      ⟨fun pb h => (inferInstance : MorphismProperty.IsStableUnderBaseChange
        @IsFinite).of_isPullback pb h⟩
    letI : IsFinite (pullback.snd f g) :=
      MorphismProperty.pullback_snd f g inferInstance
    have hfinite := finite_affine_morphism_dimension_le (pullback.snd f g)
    have htarget :
        topologicalKrullDim (Y.affineCover.X i) ≤ topologicalKrullDim Y := by
      exact (Y.affineCover.f i).isOpenEmbedding.isInducing.topologicalKrullDim_le
    exact hfinite.trans htarget
  exact scheme_dimension_le_of_openCover (Y.affineCover.pullback₁ f)
    (topologicalKrullDim Y) hchart

end PfaffianDescent
