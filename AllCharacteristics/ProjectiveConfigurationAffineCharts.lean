import AllCharacteristics.ProjectiveConfigurationQuotientAction
import AllCharacteristics.ProjectiveConfigurationFiniteEtale
import AllCharacteristics.FreeQuotientChartFactorization
import AllCharacteristics.OpenPullbackChartRestriction

/-! # Actual free affine quotient charts of projective configurations -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

/-- Starting from a prescribed affine open containing all coordinates, an
ordered configuration lies in a free affine quotient chart inside that
common-open locus. -/
theorem exists_projectiveConfigurationQuotient_affineChart_inside_commonOpen
    (U₀ : (Proj 𝒜).affineOpens)
    (x : (orderedFamilyConfigurationOver f n).left)
    (hxU : x.val ∈ orderedFamilyCommonOpen f U₀.val n) :
    ∃ (U : Scheme.{u}) (_ : IsAffine U)
      (τ : Equiv.Perm (Fin n) → (U ⟶ U)) (hτ₁ : τ 1 = 𝟙 U)
      (hτcomp : ∀ g h : Equiv.Perm (Fin n), τ (g * h) = τ g ≫ τ h)
      (i : U ⟶ (orderedFamilyConfigurationOver f n).left) (_ : IsOpenImmersion i)
      (_hi : ∀ g : Equiv.Perm (Fin n), τ g ≫ i = i ≫ configurationRightAction f n g)
      (p : U ⟶ S) (hp : ∀ g : Equiv.Perm (Fin n), τ g ≫ p = p)
      (j : affineSchemeActionQuotient (Equiv.Perm (Fin n)) τ hτ₁ hτcomp p hp ⟶
        (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme),
      IsOpenImmersion j ∧ x ∈ Set.range i ∧
        i ≫ projectiveConfigurationQuotientMap 𝒜 f n =
          affineSchemeActionQuotientMap (Equiv.Perm (Fin n)) τ hτ₁ hτcomp p hp ≫ j ∧
        i ≫ (orderedFamilyConfigurationOver f n).hom = p ∧
        (∀ z : U, (orderedFamilyConfigurationOpen f n).ι (i z) ∈
          orderedFamilyCommonOpen f U₀.val n) := by
  let G := Equiv.Perm (Fin n)
  change (orderedFamilyConfigurationOpen f n).toScheme at x
  let U := U₀
  let H := orderedFamilyCommonOpen f U.val n
  have hHa : IsAffine H.toScheme := isAffineOpen_orderedFamilyCommonOpen f U.val n U.property
  let ρH := commonOpenRightAction f U.val n
  have hH₁ : ρH 1 = 𝟙 H.toScheme := commonOpenRightAction_one f U.val n
  have hHcomp : ∀ g h : G, ρH (g * h) = ρH g ≫ ρH h := commonOpenRightAction_mul f U.val n
  let pH : H.toScheme ⟶ S := H.ι ≫ (orderedFamilyPowerOver f n).hom
  have hpH : ∀ g : G, ρH g ≫ pH = pH := commonOpenRightAction_toBase f U.val n
  let W := commonOpenConfiguration f U.val n
  have hW : ∀ g : G, (ρH g) ⁻¹ᵁ W = W := commonOpenConfiguration_preimage f U.val n
  have hxW : (⟨x.val, hxU⟩ : H.toScheme) ∈ W := x.property
  obtain ⟨D, hDa, hxD, hDW, hD⟩ := exists_stable_affineOpen_inside G ρH hH₁ hHcomp
    pH hpH W hW ⟨x.val, hxU⟩ hxW
  have : IsAffine D.toScheme := hDa
  let τ := schemeRestrictedRightAction G ρH D hD
  have hτ₁ : τ 1 = 𝟙 D.toScheme := schemeRestrictedRightAction_one G ρH hH₁ D hD
  have hτcomp : ∀ g h : G, τ (g * h) = τ g ≫ τ h :=
    schemeRestrictedRightAction_mul G ρH hHcomp D hD
  let p : D.toScheme ⟶ S := D.ι ≫ pH
  have hp : ∀ g : G, τ g ≫ p = p := schemeRestrictedRightAction_toBase G ρH D hD pH hpH
  have hDI : ∀ g : G, τ g ≫ D.ι = D.ι ≫ ρH g := schemeRestrictedRightAction_ι G ρH D hD
  let QD := affineSchemeActionQuotient G τ hτ₁ hτcomp p hp
  let r : D.toScheme ⟶ QD := affineSchemeActionQuotientMap G τ hτ₁ hτcomp p hp
  let qH : H.toScheme ⟶ commonOpenTupleQuotient f U.val n :=
    commonOpenTupleQuotientMap f U.val n U.property
  let jD : QD ⟶ commonOpenTupleQuotient f U.val n :=
    affineSchemeActionQuotientMorphism G τ hτ₁ hτcomp ρH hH₁ hHcomp p hp pH hpH D.ι hDI
  have hjD : IsOpenImmersion jD := isOpenImmersion_affineSchemeActionQuotientMorphism
    G τ hτ₁ hτcomp ρH hH₁ hHcomp p hp pH hpH D.ι hDI
  have hrj : r ≫ jD = D.ι ≫ qH := affineSchemeActionQuotientMorphism_square
    G τ hτ₁ hτcomp ρH hH₁ hHcomp p hp pH hpH D.ι hDI
  let jH : commonOpenTupleQuotient f U.val n ⟶ projectiveOrderedTupleQuotient 𝒜 f n :=
    commonOpenTupleQuotientGluedChart f n U
  have hjH : IsOpenImmersion jH := inferInstanceAs
    (IsOpenImmersion (commonOpenTupleQuotientGluedChart f n U))
  let iFull : D.toScheme ⟶ (orderedFamilyPowerOver f n).left := D.ι ≫ H.ι
  let jFull : QD ⟶ projectiveOrderedTupleQuotient 𝒜 f n := jD ≫ jH
  let qFull := projectiveOrderedTupleQuotientMap 𝒜 f n
  have hiFull : IsOpenImmersion iFull := inferInstance
  have hjFull : IsOpenImmersion jFull := inferInstance
  have hchart : H.ι ≫ qFull = qH ≫ jH := projectiveOrderedTupleQuotientMap_chart 𝒜 f n U
  have hs : iFull ≫ qFull = r ≫ jFull := by
    change (D.ι ≫ H.ι) ≫ qFull = r ≫ (jD ≫ jH)
    rw [Category.assoc, hchart, ← Category.assoc D.ι qH jH, ← hrj, Category.assoc]
  have heq : ∀ g : G, τ g ≫ iFull = iFull ≫ orderedFamilyRightAction f n g := by
    intro g
    have hg : ρH g ≫ H.ι = H.ι ≫ orderedFamilyRightAction f n g :=
      commonOpenRightAction_toPower 𝒜 f n U.val g
    change τ g ≫ (D.ι ≫ H.ι) = (D.ι ≫ H.ι) ≫ orderedFamilyRightAction f n g
    rw [← Category.assoc, hDI, Category.assoc, hg, Category.assoc]
  have hstable := equivariant_opensRange_preimage G (orderedFamilyRightAction f n)
    (orderedFamilyRightAction_one f n) (orderedFamilyRightAction_mul f n) τ iFull heq
  have hpb : IsPullback iFull r qFull jFull := isPullback_orbitQuotient_openChart
    G (orderedFamilyRightAction f n) qFull
    (projectiveOrderedTupleQuotientMap_eq_iff_orbit 𝒜 f n) iFull jFull r hs hstable
  let C := (orderedFamilyConfigurationOver f n).left
  let l : C ⟶ (orderedFamilyPowerOver f n).left := (orderedFamilyConfigurationOpen f n).ι
  have : IsOpenImmersion l := inferInstanceAs
    (IsOpenImmersion (orderedFamilyConfigurationOpen f n).ι)
  let k := (projectiveConfigurationQuotientOpen 𝒜 f n).ι
  let q : C ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme :=
    projectiveConfigurationQuotientMap 𝒜 f n
  have hsub : Set.range iFull ⊆ Set.range l := by
    rintro z ⟨d, rfl⟩
    exact ⟨⟨d.val.val, hDW d.property⟩, rfl⟩
  obtain ⟨i, j, hil, hjk, hio, hjo, hsmall⟩ := exists_openPullbackChart_restriction
    qFull r iFull jFull l k q hpb (isPullback_projectiveConfigurationQuotientMap 𝒜 f n) hsub
  have hi : ∀ g : G, τ g ≫ i = i ≫ configurationRightAction f n g := by
    intro g
    have hg : configurationRightAction f n g ≫ l = l ≫ orderedFamilyRightAction f n g :=
      configurationRightAction_ι f n g
    apply (cancel_mono l).mp
    rw [Category.assoc (τ g) i l, hil, heq,
      Category.assoc i (configurationRightAction f n g) l, hg,
      ← Category.assoc i l (orderedFamilyRightAction f n g), hil]
  refine ⟨D.toScheme, hDa, τ, hτ₁, hτcomp, i, hio, hi, p, hp, j, hjo, ?_, hsmall.w, ?_, ?_⟩
  · let d : D.toScheme := ⟨⟨x.val, hxU⟩, hxD⟩
    refine ⟨d, ?_⟩
    apply Subtype.ext
    exact congrArg (fun m : D.toScheme ⟶ (orderedFamilyPowerOver f n).left ↦ m d) hil
  · change i ≫ (l ≫ (orderedFamilyPowerOver f n).hom) = D.ι ≫ (H.ι ≫ (orderedFamilyPowerOver f n).hom)
    rw [← Category.assoc i l, hil]
    exact Category.assoc D.ι H.ι (orderedFamilyPowerOver f n).hom
  · intro z
    have hz := congrArg
      (fun m : D.toScheme ⟶ (orderedFamilyPowerOver f n).left => m z) hil
    change l (i z) = iFull z at hz
    change l (i z) ∈ H
    rw [hz]
    exact (D.ι z).property

/-- Every ordered projective configuration lies in an actual free affine
invariant-spectrum quotient chart, preserving its original base map. -/
theorem exists_projectiveConfigurationQuotient_affineChart
    (x : (orderedFamilyConfigurationOver f n).left) :
    ∃ (U : Scheme.{u}) (_ : IsAffine U)
      (τ : Equiv.Perm (Fin n) → (U ⟶ U)) (hτ₁ : τ 1 = 𝟙 U)
      (hτcomp : ∀ g h : Equiv.Perm (Fin n), τ (g * h) = τ g ≫ τ h)
      (i : U ⟶ (orderedFamilyConfigurationOver f n).left) (_ : IsOpenImmersion i)
      (_hi : ∀ g : Equiv.Perm (Fin n), τ g ≫ i = i ≫ configurationRightAction f n g)
      (p : U ⟶ S) (hp : ∀ g : Equiv.Perm (Fin n), τ g ≫ p = p)
      (j : affineSchemeActionQuotient (Equiv.Perm (Fin n)) τ hτ₁ hτcomp p hp ⟶
        (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme),
      IsOpenImmersion j ∧ x ∈ Set.range i ∧
        i ≫ projectiveConfigurationQuotientMap 𝒜 f n =
          affineSchemeActionQuotientMap (Equiv.Perm (Fin n)) τ hτ₁ hτcomp p hp ≫ j ∧
        i ≫ (orderedFamilyConfigurationOver f n).hom = p := by
  obtain ⟨U, hxU⟩ := exists_commonAffineOpen_orderedProjectivePoint 𝒜 f n x.val
  obtain ⟨V, hV, τ, hτ₁, hτcomp, i, hi, heq, p, hp, j, hj,
    hx, hs, hbase, _⟩ :=
    exists_projectiveConfigurationQuotient_affineChart_inside_commonOpen
      𝒜 f n U x hxU
  exact ⟨V, hV, τ, hτ₁, hτcomp, i, hi, heq, p, hp, j, hj,
    hx, hs, hbase⟩

end AllCharacteristics
