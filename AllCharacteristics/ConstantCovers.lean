import AllCharacteristics.FiniteSigmaSpec
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Extensive
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Finite constant covers and their rank

The actual coproduct of finitely many copies of any scheme is a finite étale
cover of constant rank equal to the number of copies. Its Cartesian
base-change square and its comparison with a product algebra over an affine
base are proved explicitly.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u

/-- The actual coproduct of copies of the base, with its structure map. -/
noncomputable def constantCoverToBase (ι : Type u) [Finite ι] (S : Scheme.{u}) :
    (∐ fun _ : ι => S) ⟶ S := Sigma.desc (fun _ => 𝟙 S)

/-- The constant cover commutes with arbitrary base change in an actual Cartesian square. -/
lemma isPullback_constantCoverToBase (ι : Type u) [Finite ι]
    {T S : Scheme.{u}} (g : T ⟶ S) :
    IsPullback (CategoryTheory.Limits.Sigma.map (f := fun _ : ι => T) (g := fun _ : ι => S) fun _ => g) (constantCoverToBase ι T)
      (constantCoverToBase ι S) g := by
  have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts
    (coproductIsCoproduct (fun _ : ι => S))
  have h := hu.isPullback_of_isColimit_left (fun _ : ι => 𝟙 S)
    (constantCoverToBase ι S) g (fun _ : ι => 𝟙 T) (fun _ : ι => g)
    (fun _ => IsPullback.of_horiz_isIso (by simp))
    (coproductIsCoproduct (fun _ : ι => T))
    (fun _ => Sigma.ι_desc _ _)
  convert h.flip using 1 <;> rfl

/-- Over a spectrum, the constant cover is the spectrum of the product algebra. -/
lemma constantCoverToBase_spec_factor (ι : Type u) [Finite ι]
    (R : Type u) [CommRing R] :
    constantCoverToBase ι (Spec (.of R)) =
      sigmaSpec (fun _ : ι => CommRingCat.of R) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (ι → R))) := by
  apply Sigma.hom_ext
  intro i
  rw [constantCoverToBase, Sigma.ι_desc, ← Category.assoc, ι_sigmaSpec, ← Spec.map_comp]
  change 𝟙 (Spec (.of R)) = Spec.map (CommRingCat.ofHom (RingHom.id R))
  simp

/-- A constant cover of an affine spectrum is finite. -/
lemma isFinite_constantCoverToBase_spec (ι : Type u) [Finite ι]
    (R : Type u) [CommRing R] : IsFinite (constantCoverToBase ι (Spec (.of R))) := by
  let := Fintype.ofFinite ι
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (ι → R)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  rw [constantCoverToBase_spec_factor]
  infer_instance

/-- A constant cover is flat over its original base. -/
lemma flat_constantCoverToBase (ι : Type u) [Finite ι] (S : Scheme.{u}) :
    Flat (constantCoverToBase ι S) := by
  change Flat (Sigma.desc (fun _ : ι => 𝟙 S))
  infer_instance

/-- A constant cover is étale over its original base. -/
lemma etale_constantCoverToBase (ι : Type u) [Finite ι] (S : Scheme.{u}) :
    Etale (constantCoverToBase ι S) := by
  let : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ Etale.instHasRingHomPropertyEtale
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{u}) (fun _ => inferInstance)

/-- The rank of a constant spectrum cover is exactly the number of copies. -/
lemma finrank_constantCoverToBase_spec (ι : Type u) [Fintype ι]
    (R : Type u) [CommRing R] (x : PrimeSpectrum R) :
    (constantCoverToBase ι (Spec (.of R))).finrank x = Fintype.card ι := by
  have : Nontrivial R := x.nontrivial
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (ι → R)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R (ι → R)))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  rw [constantCoverToBase_spec_factor, Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  exact Module.finrank_pi R

/-- A constant cover of any affine scheme is finite. -/
lemma isFinite_constantCoverToBase_affine (ι : Type u) [Finite ι]
    (S : Scheme.{u}) [IsAffine S] : IsFinite (constantCoverToBase ι S) :=
  MorphismProperty.of_isPullback (P := @IsFinite.{u})
    (isPullback_constantCoverToBase ι S.isoSpec.hom)
    (isFinite_constantCoverToBase_spec ι Γ(S, ⊤))

/-- A constant cover with finitely many copies is finite over any scheme. -/
lemma isFinite_constantCoverToBase (ι : Type u) [Finite ι] (S : Scheme.{u}) :
    IsFinite (constantCoverToBase ι S) := by
  let : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite.{u}) S.affineCover]
  intro i
  change S.affineCover.I₀ at i
  change IsFinite (pullback.snd (constantCoverToBase ι S) (S.affineCover.f i))
  let h := isPullback_constantCoverToBase ι (S.affineCover.f i)
  have : IsFinite (constantCoverToBase ι (S.affineCover.X i)) :=
    isFinite_constantCoverToBase_affine ι _
  rw [← h.isoPullback_inv_snd]
  infer_instance

/-- The constant cover has the specified rank at every point of any affine base. -/
lemma finrank_constantCoverToBase_affine (ι : Type u) [Fintype ι]
    (S : Scheme.{u}) [IsAffine S] (x : S) :
    (constantCoverToBase ι S).finrank x = Fintype.card ι := by
  have : IsFinite (constantCoverToBase ι (Spec (.of Γ(S, ⊤)))) :=
    isFinite_constantCoverToBase_spec ι _
  have : Flat (constantCoverToBase ι (Spec (.of Γ(S, ⊤)))) :=
    flat_constantCoverToBase ι _
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _
    (isPullback_constantCoverToBase ι S.isoSpec.hom)]
  exact finrank_constantCoverToBase_spec ι _ _

/-- The constant cover has exactly the number of copies as its rank at every base point. -/
lemma finrank_constantCoverToBase (ι : Type u) [Fintype ι]
    (S : Scheme.{u}) (x : S) :
    (constantCoverToBase ι S).finrank x = Fintype.card ι := by
  obtain ⟨i, y, rfl⟩ := S.affineCover.exists_eq x
  have : IsFinite (constantCoverToBase ι S) := isFinite_constantCoverToBase ι S
  have : Flat (constantCoverToBase ι S) := flat_constantCoverToBase ι S
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _
    (isPullback_constantCoverToBase ι (S.affineCover.f i)) y]
  exact finrank_constantCoverToBase_affine ι _ _

end AllCharacteristics
