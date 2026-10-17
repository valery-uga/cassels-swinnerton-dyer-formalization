import AllCharacteristics.FiniteSubschemeFromImmersion
import AllCharacteristics.FiniteSubschemeRank
import AllCharacteristics.FiniteSubschemeClosedImmersionPushforward
import PfaffianDescent.FiniteSchemeResidual
import PfaffianDescent.FiniteEtaleSchemeFrobenius
import PfaffianDescent.FiniteEtaleResidualDisjoint

/-!
# Residual finite-subscheme data

The annihilator construction in a finite Frobenius scheme gives an actual
closed residual subscheme.  Over a field its finite structure morphism is
automatically finite flat and finitely presented, so a complementary-rank
residual can be fed back into the finite-subscheme moduli interface.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open AllCharacteristics

universe u

/-- The annihilator residual to a rank-`d` closed subscheme in a rank-`N`
finite Frobenius scheme is an ideal-defined finite-flat subscheme of rank
`N - d`. -/
noncomputable def finiteSubschemeDatumOfFiniteResidual
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of K)) [IsFinite f]
    (N d : ℕ)
    (hX : finiteSchemeRank f = N)
    (hZ : finiteSchemeRank (i ≫ f) = d)
    (hfrob : letI := finiteSchemeCoefficientAlgebra f
      ∃ ell : Module.Dual K Γ(X, ⊤), IsFrobeniusFunctional ell) :
    FiniteSubschemeDatum f (N - d) := by
  let r : Spec (.of (Γ(X, ⊤) ⧸ residualAlgebraIdeal
      (RingHom.ker i.appTop.hom))) ⟶ X := finiteClosedResidualι i f
  haveI : IsClosedImmersion r := by
    dsimp [r]
    infer_instance
  haveI : IsFinite (r ≫ f) := by
    dsimp [r]
    infer_instance
  haveI : Flat (r ≫ f) := by
    infer_instance
  haveI : LocallyOfFinitePresentation (r ≫ f) := by
    infer_instance
  have hr : finiteSchemeRank (r ≫ f) = N - d := by
    dsimp [r]
    exact finite_scheme_residual_rank_complement i f N d hX hZ hfrob
  exact finiteSubschemeDatumOfClosedImmersion r f (N - d) (fun s ↦ by
    have hs : s = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst s
    exact (finiteSchemeRank_eq_finrank (r ≫ f)).symm.trans hr)

/-- If the ambient finite Frobenius scheme is itself a closed subscheme of a
larger scheme, its residual is a finite-subscheme datum on that larger
scheme.  This is the form used to pass a rank-two residual from an auxiliary
finite intersection back to the cubic surface. -/
noncomputable def finiteSubschemeDatumOfFiniteResidualOnAmbient
    {K : Type u} [Field K] {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (c : X ⟶ Y) [IsClosedImmersion c]
    (f : Y ⟶ Spec (.of K)) [IsFinite (c ≫ f)]
    (N d : ℕ)
    (hX : finiteSchemeRank (c ≫ f) = N)
    (hZ : finiteSchemeRank (i ≫ c ≫ f) = d)
    (hfrob : letI := finiteSchemeCoefficientAlgebra (c ≫ f)
      ∃ ell : Module.Dual K Γ(X, ⊤), IsFrobeniusFunctional ell) :
    FiniteSubschemeDatum f (N - d) := by
  let r : Spec (.of (Γ(X, ⊤) ⧸ residualAlgebraIdeal
      (RingHom.ker i.appTop.hom))) ⟶ X := finiteClosedResidualι i (c ≫ f)
  haveI : IsClosedImmersion r := by
    dsimp [r]
    infer_instance
  haveI : IsClosedImmersion (r ≫ c) := by
    infer_instance
  haveI : IsFinite ((r ≫ c) ≫ f) := by
    rw [Category.assoc]
    dsimp [r]
    infer_instance
  haveI : IsFinite (r ≫ (c ≫ f)) := by
    dsimp [r]
    infer_instance
  haveI : Flat ((r ≫ c) ≫ f) := by
    infer_instance
  haveI : LocallyOfFinitePresentation ((r ≫ c) ≫ f) := by
    infer_instance
  have hZ' : finiteSchemeRank (i ≫ (c ≫ f)) = d := by
    simpa only [Category.assoc] using hZ
  have hr' : finiteSchemeRank (r ≫ (c ≫ f)) = N - d := by
    dsimp [r]
    exact finite_scheme_residual_rank_complement i (c ≫ f) N d hX hZ' hfrob
  have hr : finiteSchemeRank ((r ≫ c) ≫ f) = N - d := by
    simpa only [Category.assoc] using hr'
  exact finiteSubschemeDatumOfClosedImmersion (r ≫ c) f (N - d) (fun s ↦ by
    have hs : s = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst s
    exact (finiteSchemeRank_eq_finrank ((r ≫ c) ≫ f)).symm.trans hr)

/-- If the finite ambient scheme is étale, the residual datum retains that
property over the base field. The datum is defined through the image ideal of
the residual closed immersion, so the proof transports étaleness through the
canonical isomorphism with that residual scheme. -/
theorem finiteSubschemeDatumOfFiniteResidualOnAmbient_toBase_etale_of_finiteEtale
    {K : Type u} [Field K] [CharZero K] {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (c : X ⟶ Y) [IsClosedImmersion c]
    (f : Y ⟶ Spec (.of K)) [IsFinite (c ≫ f)] [Etale (c ≫ f)]
    (N d : ℕ)
    (hX : finiteSchemeRank (c ≫ f) = N)
    (hZ : finiteSchemeRank (i ≫ c ≫ f) = d) :
    let D := finiteSubschemeDatumOfFiniteResidualOnAmbient i c f N d hX hZ
      (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f))
    Etale (D.val.subschemeι ≫ f) := by
  let r : Spec (.of (Γ(X, ⊤) ⧸ residualAlgebraIdeal
      (RingHom.ker i.appTop.hom))) ⟶ X := finiteClosedResidualι i (c ≫ f)
  letI : IsFinite ((r ≫ c) ≫ f) := by
    rw [Category.assoc]
    dsimp [r]
    infer_instance
  have hr : Etale ((r ≫ c) ≫ f) := by
    exact (finiteClosedResidualOnAmbient_rank_complement_and_etale_of_finiteEtale
      i c f N d hX hZ).1
  have hrrank : finiteSchemeRank ((r ≫ c) ≫ f) = N - d := by
    simpa only [r] using
      (finiteClosedResidualOnAmbient_rank_complement_and_etale_of_finiteEtale
        i c f N d hX hZ).2
  let e := finiteSubschemeDatumOfClosedImmersionIso (r ≫ c) f (N - d) (fun s ↦ by
    have hs : s = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst s
    exact (finiteSchemeRank_eq_finrank ((r ≫ c) ≫ f)).symm.trans hrrank)
  have he : e.hom ≫
      (finiteSubschemeDatumOfFiniteResidualOnAmbient i c f N d hX hZ
        (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f))).val.subschemeι ≫ f =
      (r ≫ c) ≫ f := by
    exact finiteSubschemeDatumOfClosedImmersionIso_hom_toBase (r ≫ c) f (N - d) _
  have hrewrite :
      (finiteSubschemeDatumOfFiniteResidualOnAmbient i c f N d hX hZ
        (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f))).val.subschemeι ≫ f =
      e.inv ≫ ((r ≫ c) ≫ f) := by
    calc
      _ = (𝟙 _) ≫ _ := rfl
      _ = (e.inv ≫ e.hom) ≫ _ := by rw [e.inv_hom_id]
      _ = e.inv ≫ (e.hom ≫ _) := Category.assoc _ _ _
      _ = e.inv ≫ ((r ≫ c) ≫ f) := congrArg (fun g ↦ e.inv ≫ g) he
  dsimp only
  rw [hrewrite]
  letI : IsIso e.inv := by
    dsimp [e]
    infer_instance
  letI : IsOpenImmersion e.inv := by infer_instance
  letI : Etale e.inv := by infer_instance
  letI : Etale ((r ≫ c) ≫ f) := hr
  exact Etale.etale_comp (f := e.inv) ((r ≫ c) ≫ f)

/-- In a finite étale ambient scheme, the datum formed from the annihilator
residual is disjoint from the finite datum embedded in that ambient scheme.
The source datum may be presented by any closed immersion into the auxiliary
finite scheme: its map back to the ambient surface is enough to identify the
two supports.  This supplies the disjointness required by the first and
middle pencils in Voisin's construction from the residual construction
itself. -/
theorem disjoint_finiteSubschemeDatumOfFiniteResidualOnAmbient_of_finiteEtale
    {K : Type u} [Field K] [CharZero K] {X Y : Scheme.{u}}
    (c : X ⟶ Y) [IsClosedImmersion c]
    (f : Y ⟶ Spec (.of K)) [IsFinite (c ≫ f)] [Etale (c ≫ f)]
    (N d : ℕ) (hX : finiteSchemeRank (c ≫ f) = N)
    (D : FiniteSubschemeDatum f d)
    (i : D.val.subscheme ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ c = D.val.subschemeι)
    (hZ : finiteSchemeRank (i ≫ c ≫ f) = d) :
    Disjoint
      (Set.range (finiteSubschemeDatumSpecMap f
        (finiteSubschemeDatumOfFiniteResidualOnAmbient i c f N d hX hZ
          (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f)))) )
      (Set.range (finiteSubschemeDatumSpecMap f D)) := by
  let r := finiteClosedResidualι i (c ≫ f)
  have hri : Disjoint (Set.range i) (Set.range r) :=
    disjoint_range_closedImmersion_finiteClosedResidualι_of_finiteEtale i (c ≫ f)
  have hcomp : Disjoint (Set.range (r ≫ c)) (Set.range (i ≫ c)) := by
    rw [Set.disjoint_left] at hri ⊢
    rintro x ⟨a, ha⟩ ⟨b, hb⟩
    apply hri (show i b ∈ Set.range i from ⟨b, rfl⟩)
    exact ⟨a, c.isClosedEmbedding.injective (ha.trans hb.symm)⟩
  letI : IsFinite ((r ≫ c) ≫ f) := by
    rw [Category.assoc]
    dsimp [r]
    infer_instance
  letI : Flat ((r ≫ c) ≫ f) := by infer_instance
  letI : LocallyOfFinitePresentation ((r ≫ c) ≫ f) := by infer_instance
  have hres : Set.range (finiteSubschemeDatumSpecMap f
      (finiteSubschemeDatumOfFiniteResidualOnAmbient i c f N d hX hZ
        (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f)))) ⊆
      Set.range (r ≫ c) := by
    unfold finiteSubschemeDatumOfFiniteResidualOnAmbient
    apply finiteSubschemeDatumSpecMap_ofClosedImmersion_range_subset
  have hD : Set.range (finiteSubschemeDatumSpecMap f D) =
      Set.range (i ≫ c) := by
    rw [range_finiteSubschemeDatumSpecMap_eq_range_subschemeι]
    rw [← hi]
  rw [Set.disjoint_left] at hcomp ⊢
  intro x hxres hxD
  exact hcomp (hres hxres) (by rw [hD] at hxD; exact hxD)

/-- The rank-two step in Voisin's degree-ten argument has the numerical form
`11 - 3 = 8`.  Whenever its degree-three component is realized as a closed
subscheme of the finite rank-eleven ambient scheme, the annihilator residual
is therefore an actual rank-eight datum on the cubic surface. -/
noncomputable def finiteSubschemeDatumRankEightOfRankElevenResidual
    {K : Type u} [Field K] {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (c : X ⟶ Y) [IsClosedImmersion c]
    (f : Y ⟶ Spec (.of K)) [IsFinite (c ≫ f)]
    (hX : finiteSchemeRank (c ≫ f) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ f) = 3)
    (hfrob : letI := finiteSchemeCoefficientAlgebra (c ≫ f)
      ∃ ell : Module.Dual K Γ(X, ⊤), IsFrobeniusFunctional ell) :
    FiniteSubschemeDatum f 8 := by
  simpa using finiteSubschemeDatumOfFiniteResidualOnAmbient
    i c f 11 3 hX hZ hfrob

/-- In characteristic zero, a finite étale rank-eleven ambient scheme
supplies the Frobenius functional automatically.  Thus a rank-three closed
component has a rank-eight residual datum without a further algebraic
assumption. -/
noncomputable def finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
    {K : Type u} [Field K] [CharZero K] {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (c : X ⟶ Y) [IsClosedImmersion c]
    (f : Y ⟶ Spec (.of K)) [IsFinite (c ≫ f)] [Etale (c ≫ f)]
    (hX : finiteSchemeRank (c ≫ f) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ f) = 3) :
    FiniteSubschemeDatum f 8 := by
  apply finiteSubschemeDatumRankEightOfRankElevenResidual i c f hX hZ
  exact finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f)

/-- The rank-eight datum obtained from a degree-three component of a finite
étale rank-eleven scheme is itself finite étale. This is the finite-scheme
output consumed by Voisin's final cubic--quadric--quadric residual. -/
theorem finiteSubschemeDatumRankEightOfEtaleRankElevenResidual_toBase_etale
    {K : Type u} [Field K] [CharZero K] {X Y Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (c : X ⟶ Y) [IsClosedImmersion c]
    (f : Y ⟶ Spec (.of K)) [IsFinite (c ≫ f)] [Etale (c ≫ f)]
    (hX : finiteSchemeRank (c ≫ f) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ f) = 3) :
    Etale ((finiteSubschemeDatumRankEightOfEtaleRankElevenResidual i c f hX hZ).val.subschemeι ≫
      f) := by
  exact finiteSubschemeDatumOfFiniteResidualOnAmbient_toBase_etale_of_finiteEtale
    i c f 11 3 hX hZ

end PfaffianDescent
