import AllCharacteristics.FiniteSubschemeFromImmersion
import AllCharacteristics.FiniteFlatCycle
import PfaffianDescent.IntrinsicFiniteCycle
import PfaffianDescent.FiniteSchemeFundamentalIso

/-!
# Rank and cycles of finite-subscheme data

An ideal-defined finite-flat subscheme datum over a field retains its stated
rank as an intrinsic scheme rank and supplies an effective zero-cycle of that
degree on its ambient scheme.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics

universe u

/-- The constant-rank field fiber of a finite-subscheme datum has its stated
intrinsic scheme rank. -/
theorem finiteSubschemeDatum_finiteSchemeRank
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {n : ℕ} (D : FiniteSubschemeDatum f n) :
    letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
    finiteSchemeRank (D.val.subschemeι ≫ f) = n := by
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  rw [finiteSchemeRank_eq_finrank]
  exact D.property.2.2.2 (IsLocalRing.closedPoint k)

/-- The canonical affine presentation of a finite-subscheme datum, obtained
from the spectrum of the global coordinate algebra of its closed subscheme. -/
noncomputable def finiteSubschemeDatumSpecMap
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {n : ℕ} (D : FiniteSubschemeDatum f n) :
    Spec (.of Γ(D.val.subscheme, ⊤)) ⟶ X := by
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  haveI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ f)
  exact D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι

/-- The affine presentation of a finite-subscheme datum is over the base
field through its canonical coordinate-algebra structure. -/
theorem finiteSubschemeDatumSpecMap_toBase
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {n : ℕ} (D : FiniteSubschemeDatum f n) :
    letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
    letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ f)
    finiteSubschemeDatumSpecMap f D ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(D.val.subscheme, ⊤))) := by
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  haveI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ f)
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ f)
  change D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫ f = _
  rw [← PfaffianDescent.finiteSchemeCoefficient_spec]

instance finiteSubschemeDatumSpecMap_isClosedImmersion
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {n : ℕ} (D : FiniteSubschemeDatum f n) :
    IsClosedImmersion (finiteSubschemeDatumSpecMap f D) := by
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  haveI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ f)
  unfold finiteSubschemeDatumSpecMap
  infer_instance

/-- The affine presentation has the finite-flat rank specified by the datum. -/
theorem finiteSubschemeDatumSpecMap_finrank
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {n : ℕ} (D : FiniteSubschemeDatum f n) :
    letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
    (finiteSubschemeDatumSpecMap f D ≫ f).finrank
      (IsLocalRing.closedPoint k) = n := by
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  haveI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ f)
  letI : IsFinite (D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫ f) := by
    infer_instance
  change (D.val.subscheme.isoSpec.inv ≫ (D.val.subschemeι ≫ f)).finrank
      (IsLocalRing.closedPoint k) = n
  rw [Scheme.Hom.finrank_comp_left_of_isIso]
  exact D.property.2.2.2 (IsLocalRing.closedPoint k)

/-- The canonical effective zero-cycle carried by a finite-subscheme datum:
the proper pushforward of the intrinsic fundamental cycle of its closed
subscheme. -/
noncomputable def finiteSubschemeDatumCycle
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {n : ℕ} (D : FiniteSubschemeDatum f n) : EffectiveZeroCycle X := by
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  exact pushforwardCycle D.val.subschemeι
    (PfaffianDescent.finiteSchemeFundamentalCycle (D.val.subschemeι ≫ f))

/-- The canonical cycle of a finite-subscheme datum has its specified
finite-flat rank as degree. -/
theorem finiteSubschemeDatumCycle_degree
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {n : ℕ} (D : FiniteSubschemeDatum f n) :
    EffectiveZeroCycle.degree f (finiteSubschemeDatumCycle f D) = n := by
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  rw [finiteSubschemeDatumCycle, degree_pushforwardCycle,
    PfaffianDescent.finiteSchemeFundamentalCycle_degree]
  exact finiteSubschemeDatum_finiteSchemeRank f D

/-- When a datum is formed from a finite flat closed immersion, its canonical
cycle is the pushforward of the intrinsic fundamental cycle of that original
embedded scheme. -/
theorem finiteSubschemeDatumCycle_of_closedImmersion
    {k : Type u} [Field k] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of k))
    [IsFinite (i ≫ f)] [Flat (i ≫ f)] [LocallyOfFinitePresentation (i ≫ f)]
    (n : ℕ) (hn : ∀ s : Spec (.of k), (i ≫ f).finrank s = n) :
    finiteSubschemeDatumCycle f (finiteSubschemeDatumOfClosedImmersion i f n hn) =
      pushforwardCycle i (PfaffianDescent.finiteSchemeFundamentalCycle (i ≫ f)) := by
  let D := finiteSubschemeDatumOfClosedImmersion i f n hn
  let e := finiteSubschemeDatumOfClosedImmersionIso i f n hn
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  letI : IsArtinianScheme Z := PfaffianDescent.finiteScheme_isArtinian (i ≫ f)
  letI : IsArtinianScheme D.val.subscheme :=
    PfaffianDescent.finiteScheme_isArtinian (D.val.subschemeι ≫ f)
  have hfund : pushforwardCycle e.hom
      (PfaffianDescent.finiteSchemeFundamentalCycle (i ≫ f)) =
      PfaffianDescent.finiteSchemeFundamentalCycle (D.val.subschemeι ≫ f) := by
    change pushforwardCycle e.hom (fundamentalZeroCycle Z) =
      fundamentalZeroCycle D.val.subscheme
    rw [PfaffianDescent.pushforwardCycle_iso e]
    exact PfaffianDescent.fundamentalZeroCycle_iso e
  have hι : e.hom ≫ D.val.subschemeι = i :=
    finiteSubschemeDatumOfClosedImmersionIso_hom_ι i f n hn
  change pushforwardCycle D.val.subschemeι
      (PfaffianDescent.finiteSchemeFundamentalCycle (D.val.subschemeι ≫ f)) = _
  rw [← hfund, ← pushforwardCycle_comp]
  simpa only [hι]

/-- Isomorphic finite subschemes with the same map to the ambient scheme
carry the same canonical effective zero-cycle.

This removes presentation choices from the finite-flat pencils used in
Voisin's construction: an endpoint can be identified with a prescribed
finite datum at the scheme level, and its cycle equality then follows from
the identification rather than being supplied separately. -/
theorem finiteSubschemeDatumCycle_eq_of_iso
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {n : ℕ} (D E : FiniteSubschemeDatum f n)
    (e : D.val.subscheme ≅ E.val.subscheme)
    (he : e.hom ≫ E.val.subschemeι = D.val.subschemeι) :
    finiteSubschemeDatumCycle f D = finiteSubschemeDatumCycle f E := by
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  letI : IsFinite (E.val.subschemeι ≫ f) := E.property.1
  have hfund : pushforwardCycle e.hom
      (PfaffianDescent.finiteSchemeFundamentalCycle (D.val.subschemeι ≫ f)) =
      PfaffianDescent.finiteSchemeFundamentalCycle (E.val.subschemeι ≫ f) := by
    exact PfaffianDescent.finiteSchemeFundamentalCycle_iso e
      (D.val.subschemeι ≫ f) (E.val.subschemeι ≫ f)
  change pushforwardCycle D.val.subschemeι
      (PfaffianDescent.finiteSchemeFundamentalCycle (D.val.subschemeι ≫ f)) =
    pushforwardCycle E.val.subschemeι
      (PfaffianDescent.finiteSchemeFundamentalCycle (E.val.subschemeι ≫ f))
  rw [← hfund, ← pushforwardCycle_comp]
  simpa only [he]

/-- The affine presentations used to read a finite-subscheme datum as a map
to the ambient scheme have exactly the range of the datum's closed
immersion.  This lets scheme-level identifications of finite subschemes be
used in support-disjointness arguments without choosing an affine
presentation. -/
theorem range_finiteSubschemeDatumSpecMap_eq_range_subschemeι
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {n : ℕ} (D : FiniteSubschemeDatum f n) :
    Set.range (finiteSubschemeDatumSpecMap f D) =
      Set.range D.val.subschemeι := by
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  haveI : IsAffine D.val.subscheme :=
    isAffine_of_isAffineHom (D.val.subschemeι ≫ f)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨D.val.subscheme.isoSpec.inv y, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨D.val.subscheme.isoSpec.hom y, ?_⟩
    change D.val.subschemeι (D.val.subscheme.isoSpec.inv
      (D.val.subscheme.isoSpec.hom y)) = D.val.subschemeι y
    simp

/-- Isomorphic finite subschemes over the ambient scheme have the same
underlying support.  Together with
`finiteSubschemeDatumCycle_eq_of_iso`, this removes both cycle and support
dependence on the particular closed-immersion presentation selected by a
complete-intersection construction. -/
theorem range_finiteSubschemeDatumSpecMap_eq_of_iso
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {n : ℕ} (D E : FiniteSubschemeDatum f n)
    (e : D.val.subscheme ≅ E.val.subscheme)
    (he : e.hom ≫ E.val.subschemeι = D.val.subschemeι) :
    Set.range (finiteSubschemeDatumSpecMap f D) =
      Set.range (finiteSubschemeDatumSpecMap f E) := by
  rw [range_finiteSubschemeDatumSpecMap_eq_range_subschemeι,
    range_finiteSubschemeDatumSpecMap_eq_range_subschemeι]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨e.hom y, ?_⟩
    change (e.hom ≫ E.val.subschemeι) y = D.val.subschemeι y
    rw [he]
  · rintro ⟨y, rfl⟩
    refine ⟨e.inv y, ?_⟩
    change D.val.subschemeι (e.inv y) = E.val.subschemeι y
    rw [← he]
    simp

/-- Forming a finite-subscheme datum from a finite flat closed immersion does
not change its support.  This identifies the canonical affine presentation
of the resulting datum with the image of the original immersion. -/
theorem range_finiteSubschemeDatumSpecMap_finiteSubschemeDatumOfClosedImmersion
    {k : Type u} [Field k] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of k))
    [IsFinite (i ≫ f)] [Flat (i ≫ f)] [LocallyOfFinitePresentation (i ≫ f)]
    (n : ℕ) (hn : ∀ s : Spec (.of k), (i ≫ f).finrank s = n) :
    Set.range (finiteSubschemeDatumSpecMap f
      (finiteSubschemeDatumOfClosedImmersion i f n hn)) = Set.range i := by
  rw [range_finiteSubschemeDatumSpecMap_eq_range_subschemeι]
  let e := finiteSubschemeDatumOfClosedImmersionIso i f n hn
  have he : e.hom ≫
      (finiteSubschemeDatumOfClosedImmersion i f n hn).val.subschemeι = i :=
    finiteSubschemeDatumOfClosedImmersionIso_hom_ι i f n hn
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨e.inv y, ?_⟩
    have hcancel : e.hom (e.inv y) = y := by
      simpa using congrArg (fun g => g y) e.inv_hom_id
    simpa only [Scheme.Hom.comp_apply, hcancel] using
      (congrArg (fun g : Z ⟶ X => g (e.inv y)) he).symm
  · rintro ⟨y, rfl⟩
    refine ⟨e.hom y, ?_⟩
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun g : Z ⟶ X => g y) he

/-- A finite-subscheme datum over a field gives an effective ambient
zero-cycle with precisely its specified degree. -/
theorem finiteSubschemeDatum_exists_effectiveZeroCycle
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {n : ℕ} (D : FiniteSubschemeDatum f n) :
    ∃ z : EffectiveZeroCycle X, EffectiveZeroCycle.degree f z = n := by
  letI : IsFinite (D.val.subschemeι ≫ f) := D.property.1
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_of_finite_closed_subscheme
    D.val.subschemeι f
  have hrank : finiteSchemeRank (D.val.subschemeι ≫ f) = n := by
    rw [finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint k)
  exact ⟨z, hz.trans hrank⟩

end AllCharacteristics
