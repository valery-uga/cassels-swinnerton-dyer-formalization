import AllCharacteristics.ProjectiveConfigurationQuotient
import AllCharacteristics.RelativeAffineConfigurationQuotient

/-!
# Étaleness of the actual global projective configuration quotient

The original configuration scheme is covered by its common-affine chart
restrictions. On each chart the original quotient is étale by the proved
free-action argument. The actual quotient-chart identities identify these
maps with the global configuration quotient.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

/-- The actual unordered distinct-configuration quotient of a projective
scheme is étale in every characteristic. -/
instance etale_projectiveConfigurationQuotientMap :
    Etale (projectiveConfigurationQuotientMap 𝒜 f n) := by
  apply etale_of_source_open_neighborhoods
  intro x
  change (orderedFamilyConfigurationOpen f n).toScheme at x
  obtain ⟨U, hxU⟩ := exists_commonAffineOpen_orderedProjectivePoint 𝒜 f n x.val
  let W := commonOpenConfiguration f U.val n
  let C := (orderedFamilyConfigurationOpen f n).toScheme
  let d : W.toScheme ⟶ C := commonOpenConfigurationToConfiguration f U.val n
  have hd : d ≫ (orderedFamilyConfigurationOpen f n).ι =
      W.ι ≫ (orderedFamilyCommonOpen f U.val n).ι :=
    morphismRestrict_ι (orderedFamilyCommonOpen f U.val n).ι
      (orderedFamilyConfigurationOpen f n)
  refine ⟨W.toScheme, d, isOpenImmersion_commonOpenConfigurationToConfiguration f U.val n, ?_, ?_⟩
  · have hw : (⟨x.val, hxU⟩ : (orderedFamilyCommonOpen f U.val n).toScheme) ∈ W := x.property
    let w : W.toScheme := ⟨⟨x.val, hxU⟩, hw⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    exact congrArg (fun m : W.toScheme ⟶ (orderedFamilyPowerOver f n).left ↦ m w) hd
  · let j := (projectiveConfigurationQuotientOpen 𝒜 f n).ι
    let q : C ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme :=
      projectiveConfigurationQuotientMap 𝒜 f n
    let i : C ⟶ (orderedFamilyPowerOver f n).left := (orderedFamilyConfigurationOpen f n).ι
    let c := (orderedFamilyCommonOpen f U.val n).ι
    let qFull : (orderedFamilyPowerOver f n).left ⟶ projectiveOrderedTupleQuotient 𝒜 f n :=
      projectiveOrderedTupleQuotientMap 𝒜 f n
    have hUa : IsAffineOpen U.val := U.property
    let qU : (orderedFamilyCommonOpen f U.val n).toScheme ⟶ commonOpenTupleQuotient f U.val n :=
      commonOpenTupleQuotientMap f U.val n hUa
    let l : commonOpenTupleQuotient f U.val n ⟶ projectiveOrderedTupleQuotient 𝒜 f n :=
      commonOpenTupleQuotientGluedChart f n U
    have hj : IsOpenImmersion j := inferInstanceAs
      (IsOpenImmersion (projectiveConfigurationQuotientOpen 𝒜 f n).ι)
    have hl : IsOpenImmersion l := inferInstanceAs
      (IsOpenImmersion (commonOpenTupleQuotientGluedChart f n U))
    have hq : Etale (W.ι ≫ qU) :=
      etale_commonOpenTupleQuotientMap_on_configuration f U.val n hUa
    have hp : i ≫ qFull = q ≫ j := (isPullback_projectiveConfigurationQuotientMap 𝒜 f n).w
    have hchart : c ≫ qFull = qU ≫ l := projectiveOrderedTupleQuotientMap_chart 𝒜 f n U
    have hd' : d ≫ i = W.ι ≫ c := hd
    have he : (d ≫ q) ≫ j = (W.ι ≫ qU) ≫ l := by
      calc
        (d ≫ q) ≫ j = (d ≫ i) ≫ qFull :=
          (Category.assoc d q j).trans
            ((congrArg (fun m : C ⟶ projectiveOrderedTupleQuotient 𝒜 f n ↦ d ≫ m) hp.symm).trans
              (Category.assoc d i qFull).symm)
        _ = (W.ι ≫ c) ≫ qFull :=
          congrArg (fun m : W.toScheme ⟶ (orderedFamilyPowerOver f n).left ↦ m ≫ qFull) hd'
        _ = W.ι ≫ (qU ≫ l) :=
          (Category.assoc W.ι c qFull).trans
            (congrArg (fun m : (orderedFamilyCommonOpen f U.val n).toScheme ⟶
              projectiveOrderedTupleQuotient 𝒜 f n ↦ W.ι ≫ m) hchart)
        _ = (W.ι ≫ qU) ≫ l := (Category.assoc W.ι qU l).symm
    have : Etale ((d ≫ q) ≫ j) := he.symm ▸ Etale.etale_comp (W.ι ≫ qU) l
    exact Etale.of_comp (d ≫ q) j

end AllCharacteristics
