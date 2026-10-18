import AllCharacteristics.SmoothSchemeRegularity
import AllCharacteristics.ProjectiveHypersurfaceClosedDimension
import PfaffianDescent.ClosedImmersionStalkFlatQuotient173
import PfaffianDescent.FiniteSchemeModuleNativeWeightedRankAnyField
import PfaffianDescent.SmoothCubicOriginalFamilyStalkBridge172

/-!
Natural stalk input for an
arbitrary finite embedded family.  The family is never replaced by a reduced
point and its ideal is never assumed a regular pair.  Regularity, finite
colength, whole ideal germs, and (for actual cubic surfaces) exact dimension
two are derived from the original geometry.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- A surjective map to a local Artinian ring forces a positive power of
the ORIGINAL maximal ideal into its actual kernel.  No colength or
primary-ideal certificate is supplied. -/
theorem localArtinianSurjection_exists_maximalIdeal_pow_le_ker001
    {A C : Type u} [CommRing A] [IsLocalRing A] [CommRing C]
    [IsLocalRing C] [IsArtinianRing C]
    (c : A →+* C) (hc : Function.Surjective c) :
    ∃ N : ℕ, 0 < N ∧ maximalIdeal A ^ N ≤ RingHom.ker c := by
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal C).mp inferInstance
  have hmap : (maximalIdeal A ^ (N + 1)).map c = ⊥ := by
    rw [Ideal.map_pow, IsLocalRing.map_maximalIdeal_of_surjective c hc,
      pow_succ, hN, zero_mul]
    rfl
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  exact (Ideal.map_le_iff_le_comap).mp hmap.le

/-- Generic upper bound for the native stalk of a smooth relative surface
over a field.  Its affine scalar map and locally standard-smooth
presentation are derived from the actual scheme morphism. -/
theorem smoothRelativeSurface_field_stalk_dim_le_two001
    {K : Type u} [Field K] {X : Scheme.{u}}
    (F : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 2 F] (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ 2 := by
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  let Y := X.affineCover.X i
  let A := Γ(Y, ⊤)
  let j : Spec (.of A) ⟶ X := Y.isoSpec.inv ≫ X.affineCover.f i
  let f : K →+* A := (Spec.preimage (j ≫ F)).hom
  letI : Algebra K A := f.toAlgebra
  have hj : j ≫ F = Spec.map (CommRingCat.ofHom (algebraMap K A)) :=
    (Spec.map_preimage (j ≫ F)).symm
  letI : IsOpenImmersion j := inferInstance
  have hstd : SmoothOfRelativeDimension 2
      (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
    rw [← hj]
    exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) (j ≫ F))
  have hlocal : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 2)
      (algebraMap K A) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 2)).mp hstd
  let y' : PrimeSpectrum A := Y.isoSpec.hom y
  letI : y'.asIdeal.IsPrime := y'.isPrime
  have hdim :=
    AllCharacteristics.ringKrullDim_localizationAtPrime_le_of_locally_standardSmoothOfRelativeDimension_of_field
      (K := K) (A := A) 2 hlocal y'.asIdeal
  let e1 := (asIso ((X.affineCover.f i).stalkMap y)).commRingCatIsoToRingEquiv
  let e2 := (asIso (Y.isoSpec.hom.stalkMap y)).commRingCatIsoToRingEquiv
  let e3 := (Spec.stalkIso (.of A) y').commRingCatIsoToRingEquiv
  calc
    ringKrullDim (X.presheaf.stalk (X.affineCover.f i y)) =
        ringKrullDim (Y.presheaf.stalk y) := ringKrullDim_eq_of_ringEquiv e1
    _ = ringKrullDim (Localization.AtPrime y'.asIdeal) :=
      (ringKrullDim_eq_of_ringEquiv e2).symm.trans (ringKrullDim_eq_of_ringEquiv e3)
    _ ≤ 2 := hdim

/-- Arbitrary closed finite family over a field supplies the ACTUAL
ambient stalk's regularity and the WHOLE stalk ideal's finite colength.
Reducedness, separability, a field-point presentation and regular-pair
generation are all unnecessary. -/
theorem finiteEmbeddedFieldFamily_stalk_regular_finiteColength001
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (F : X ⟶ Spec (.of K)) [Smooth F]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsFinite (i ≫ F)] (z : Z) :
    IsRegularLocalRing (X.presheaf.stalk (i z)) ∧
      IsArtinianRing (X.presheaf.stalk (i z) ⧸ RingHom.ker (i.stalkMap z).hom) ∧
      ∃ N : ℕ, 0 < N ∧
        maximalIdeal (X.presheaf.stalk (i z)) ^ N ≤ RingHom.ker (i.stalkMap z).hom := by
  letI : IsRegularRing Γ(Spec (.of K), ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  have hreg := AllCharacteristics.isRegularLocalRing_stalk_of_smooth_over_affine F (i z)
  letI : IsArtinianRing (Z.presheaf.stalk z) :=
    Coray.finiteScheme_nativeStalk_isArtinian_anyField (i ≫ F) z
  let e := (i.stalkMap z).hom.quotientKerEquivOfSurjective (i.stalkMap_surjective z)
  have hArt : IsArtinianRing
      (X.presheaf.stalk (i z) ⧸ RingHom.ker (i.stalkMap z).hom) :=
    e.symm.isArtinianRing
  exact ⟨hreg, hArt,
    localArtinianSurjection_exists_maximalIdeal_pow_le_ker001
      (i.stalkMap z).hom (i.stalkMap_surjective z)⟩

/-- The full affine ideal germ, rather than just its radical or support,
has Artinian quotient and contains a positive power of the maximal ideal. -/
theorem finiteEmbeddedFieldFamily_affineIdeal_germ_finiteColength001
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (F : X ⟶ Spec (.of K)) [Smooth F]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsFinite (i ≫ F)]
    (U : X.affineOpens) (z : Z) (hz : i z ∈ U.1) :
    IsArtinianRing (X.presheaf.stalk (i z) ⧸
      (i.ker.ideal U).map (X.presheaf.germ U.1 (i z) hz).hom) ∧
      ∃ N : ℕ, 0 < N ∧ maximalIdeal (X.presheaf.stalk (i z)) ^ N ≤
        (i.ker.ideal U).map (X.presheaf.germ U.1 (i z) hz).hom := by
  rw [cubicClosedPointSerreFiniteZeroResidual_affineIdeal_germ_eq_stalkMap_kernel i U z hz]
  exact (finiteEmbeddedFieldFamily_stalk_regular_finiteColength001 F i z).2

/-- On an actual nonzero smooth cubic, ANY finite-family support point is
closed and has ambient local dimension exactly two.  The arbitrary
nonreduced family's WHOLE stalk ideal has finite colength there. -/
theorem finiteEmbeddedCubicFieldFamily_stalk_intake001
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)] (z : Z) :
    IsClosed ({i z} : Set (hypersurface p hp)) ∧
      IsRegularLocalRing ((hypersurface p hp).presheaf.stalk (i z)) ∧
      ringKrullDim ((hypersurface p hp).presheaf.stalk (i z)) = 2 ∧
      IsArtinianRing ((hypersurface p hp).presheaf.stalk (i z) ⧸
        RingHom.ker (i.stalkMap z).hom) ∧
      ∃ N : ℕ, 0 < N ∧
        maximalIdeal ((hypersurface p hp).presheaf.stalk (i z)) ^ N ≤
          RingHom.ker (i.stalkMap z).hom := by
  letI : IsLocallyArtinian Z := IsLocallyArtinian.of_locallyQuasiFinite
    (i ≫ hypersurfaceToBase p hp)
  have hz : IsClosed ({z} : Set Z) := isClosed_singleton
  have hx : IsClosed ({i z} : Set (hypersurface p hp)) := by
    simpa only [Set.image_singleton] using i.isClosedEmbedding.isClosedMap _ hz
  obtain ⟨hreg, hArt, hpow⟩ :=
    finiteEmbeddedFieldFamily_stalk_regular_finiteColength001 (hypersurfaceToBase p hp) i z
  exact ⟨hx, hreg, ringKrullDim_stalk_projective_hypersurface_eq_two p hp hp0 (i z) hx,
    hArt, hpow⟩

/-- Literal residue-base-change intake for an ARBITRARY original finite
family on a smooth lifted cubic.  The special family is constructed as the
categorical pullback.  Its support point, regularity, exact local dimension
two, and finite-colength whole ideal are all derived internally. -/
theorem arbitraryCubicFamily_residueSupport_stalk_intake001
    {B K : Type u} [CommRing B] [Field K]
    (b : B →+* K) (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (he : q.map b = p) [Smooth (hypersurfaceToBase q hq)]
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface q hq) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase q hq)]
    (z0 : ↥(pullback i (hypersurfaceReductionMap b q hq p hp he) : Scheme.{u})) :
    let i0 := pullback.snd i (hypersurfaceReductionMap b q hq p hp he)
    IsClosed ({i0 z0} : Set (hypersurface p hp)) ∧
      IsRegularLocalRing ((hypersurface p hp).presheaf.stalk (i0 z0)) ∧
      ringKrullDim ((hypersurface p hp).presheaf.stalk (i0 z0)) = 2 ∧
      IsArtinianRing ((hypersurface p hp).presheaf.stalk (i0 z0) ⧸
        RingHom.ker (i0.stalkMap z0).hom) ∧
      ∃ N : ℕ, 0 < N ∧
        maximalIdeal ((hypersurface p hp).presheaf.stalk (i0 z0)) ^ N ≤
          RingHom.ker (i0.stalkMap z0).hom := by
  let d := hypersurfaceReductionMap b q hq p hp he
  let i0 := pullback.snd i d
  have Hbase := isPullback_hypersurfaceReductionMap b q hq p hp he
  letI : Smooth (hypersurfaceToBase p hp) :=
    MorphismProperty.of_isPullback Hbase
      (inferInstance : Smooth (hypersurfaceToBase q hq))
  letI : IsFinite (i0 ≫ hypersurfaceToBase p hp) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback i d).paste_vert Hbase)
      (inferInstance : IsFinite (i ≫ hypersurfaceToBase q hq))
  exact finiteEmbeddedCubicFieldFamily_stalk_intake001 p hp hp0 i0 z0

/-- The actual original-base ambient stalk modulo the ACTUAL residue
kernel is the regular special ambient stalk found from arbitrary-family
support.  This applies172 to the internally derived closed support point;
it does not assert that the arbitrary family is itself a reduced point. -/
theorem arbitraryCubicFamily_residueSupport_ambientStalkQuotientIso001
    {B K : Type u} [CommRing B] [Field K]
    (b : B →+* K) (hb : Function.Surjective b)
    (q : MvPolynomial (Fin 4) B) (hq : q.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (he : q.map b = p) [Smooth (hypersurfaceToBase q hq)]
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface q hq) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase q hq)]
    (z0 : ↥(pullback i (hypersurfaceReductionMap b q hq p hp he) : Scheme.{u})) :
    let x0 := pullback.snd i (hypersurfaceReductionMap b q hq p hp he) z0
    Nonempty (((hypersurface q hq).presheaf.stalk
      (hypersurfaceReductionMap b q hq p hp he x0) ⧸
      (RingHom.ker b).map (familyBaseToStalk169 (hypersurfaceToBase q hq)
        (hypersurfaceReductionMap b q hq p hp he x0))) ≃+*
      (hypersurface p hp).presheaf.stalk x0) := by
  have hx := (arbitraryCubicFamily_residueSupport_stalk_intake001 b q hq p hp hp0 he i z0).1
  exact ⟨smoothCubic_originalFamilyStalkQuotientEquiv172 b hb q hq p hp he ⟨_, hx⟩⟩

/-- The actual upstairs ambient and actual arbitrary embedded-family
stalk quotient have the original Artin-base action and are flat.  This
uses generic169/173 and introduces no regularity or generation input. -/
theorem arbitraryEmbeddedArtinFamily_upstairsStalk_properties001
    {B : Type u} [CommRing B] [IsArtinianRing B] {X Z : Scheme.{u}}
    (F : X ⟶ Spec (.of B)) [Smooth F]
    (i : Z ⟶ X) [IsClosedImmersion i] [Flat (i ≫ F)] (z : Z) :
    letI := familyStalkAlgebra169 F (i z)
    Module.Flat B (X.presheaf.stalk (i z)) ∧
      IsLocalRing (X.presheaf.stalk (i z)) ∧
      IsNoetherianRing (X.presheaf.stalk (i z)) ∧
      Module.Flat B (X.presheaf.stalk (i z) ⧸ RingHom.ker (i.stalkMap z).hom) := by
  letI := familyStalkAlgebra169 F (i z)
  obtain ⟨hflat, hlocal, hnoeth⟩ := smooth_family_stalk_properties_artin169 F (i z)
  refine ⟨hflat, hlocal, hnoeth, ?_⟩
  exact quotientKernel_flat_of_coefficient_map173
    (familyBaseToStalk169 F (i z)) (familyBaseToStalk169 (i ≫ F) z)
    (i.stalkMap z).hom (i.stalkMap_surjective z)
    (familyBaseToStalk169_comp171 F i z).symm
    (flat_familyBaseToStalk169 (i ≫ F) z)

end PfaffianDescent
end
