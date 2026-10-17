import PfaffianDescent.VoisinGenericCubicResidual
import PfaffianDescent.VoisinEffectiveCycleGenericSpecialization
import PfaffianDescent.VoisinDegreeTenComplementCycle
import PfaffianDescent.VoisinSmoothGenericEightIntrinsicPresentation
import PfaffianDescent.FiniteSubschemeResidualDatum
import AllCharacteristics.ArbitraryFieldCubicCycleDescent

/-!
# Specializing the first generic degree-ten residual

The degree-sixteen completion need not be étale.  The original degree-ten
configuration is finite étale, and the generic degree-eleven residual cycle
specializes through its configuration space.  This is the specialization
direction used in Voisin's first residual argument.
-/

open AlgebraicGeometry CategoryTheory
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent

universe u

variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A degree-eleven effective cycle obtained from the first generic residual
is enough to enter a later finite-etale configuration step, unless the cubic
already has a rational point. The degree-eight alternative can skip the
rank-two construction; the degree-eleven alternative supplies its étale input.
No reducedness of the original effective cycle is assumed. -/
theorem section_or_degreeEight_or_degreeEleven_etaleDatum_of_effectiveDegreeEleven
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 11) :
    (∃ a : Spec (.of K) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
    (∃ D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8,
      Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)) ∨
    (∃ D₁₁ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      Etale (D₁₁.val.subschemeι ≫ hypersurfaceToBase p hp)) := by
  rcases cubic_section_or_closedPoint_degree_eight_or_eleven_of_effective_degree_eleven
      p hp hne z hz with hsection | ⟨x, h8 | h11⟩
  · exact Or.inl hsection
  · exact Or.inr (Or.inl ⟨_,
      finiteSubschemeDatumOfClosedPointOfResidueDegree_toBase_etale
        (hypersurfaceToBase p hp) x 8 h8⟩)
  · exact Or.inr (Or.inr ⟨_,
      finiteSubschemeDatumOfClosedPointOfResidueDegree_toBase_etale
        (hypersurfaceToBase p hp) x 11 h11⟩)

/-- The same reduction after the rank-two step: degree-eight effectivity
supplies an étale degree-eight starting datum for the final quadratic
residual, unless it has already given a rational point. -/
theorem section_or_degreeEight_etaleDatum_of_effectiveDegreeEight
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 8) :
    (∃ a : Spec (.of K) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
    (∃ D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8,
      Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)) := by
  rcases cubic_section_or_closedPoint_degree_eight_of_effective_degree_eight
      p hp hne z hz with hsection | ⟨x, h8⟩
  · exact Or.inl hsection
  · exact Or.inr ⟨_,
      finiteSubschemeDatumOfClosedPointOfResidueDegree_toBase_etale
        (hypersurfaceToBase p hp) x 8 h8⟩

/-- The final degree-eight branch is now closed internally: an effective
degree-eight cycle gives either a rational section immediately or, through
its degree-eight closed support point and canonical generic finiteness, an
effective degree-four cycle. -/
theorem section_or_effectiveDegreeFour_of_effectiveDegreeEight
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 8) :
    (∃ a : Spec (.of K) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
    (∃ z₄ : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₄ = 4) := by
  rcases section_or_degreeEight_etaleDatum_of_effectiveDegreeEight
      p hp hne z hz with hsection | ⟨D₈, hD₈⟩
  · exact Or.inl hsection
  · letI : Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := hD₈
    exact Or.inr
      (exists_effectiveDegreeFourCycle_of_smoothCubic_and_etaleDegreeEight
        p hp hne D₈)

/-- The exact endpoint needed from the middle Serre construction.  Once its
moving rank-eleven zero scheme is finite etale and contains the intended
rank-three closed component, the annihilator residual is an etale
degree-eight datum.  Canonical generic finiteness then produces the required
effective degree-four cycle, with no further Bertini or complete-intersection
input. -/
theorem exists_effectiveDegreeFourCycle_of_etaleRankEleven_with_rankThreeClosedSubscheme
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {W Z : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i]
    (c : W ⟶ hypersurface p hp) [IsClosedImmersion c]
    [IsFinite (c ≫ hypersurfaceToBase p hp)]
    [Etale (c ≫ hypersurfaceToBase p hp)]
    (hW : finiteSchemeRank (c ≫ hypersurfaceToBase p hp) = 11)
    (hZ : finiteSchemeRank (i ≫ c ≫ hypersurfaceToBase p hp) = 3) :
    ∃ z₄ : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₄ = 4 := by
  let D₈ := finiteSubschemeDatumRankEightOfEtaleRankElevenResidual
    i c (hypersurfaceToBase p hp) hW hZ
  letI : Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) :=
    finiteSubschemeDatumRankEightOfEtaleRankElevenResidual_toBase_etale
      i c (hypersurfaceToBase p hp) hW hZ
  exact exists_effectiveDegreeFourCycle_of_smoothCubic_and_etaleDegreeEight
    p hp hne D₈

/-- After specializing the first residual, the degree-eight alternative is
fully eliminated.  The sole remaining nontrivial branch is an étale
degree-eleven datum, which is the input to Voisin's middle rank-two descent. -/
theorem section_or_effectiveDegreeFour_or_degreeEleven_etaleDatum_of_effectiveDegreeEleven
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 11) :
    (∃ a : Spec (.of K) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
    (∃ z₄ : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₄ = 4) ∨
    (∃ D₁₁ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      Etale (D₁₁.val.subschemeι ≫ hypersurfaceToBase p hp)) := by
  rcases section_or_degreeEight_or_degreeEleven_etaleDatum_of_effectiveDegreeEleven
      p hp hne z hz with hsection | h₈ | h₁₁
  · exact Or.inl hsection
  · rcases h₈ with ⟨D₈, hD₈⟩
    letI : Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp) := hD₈
    exact Or.inr (Or.inl
      (exists_effectiveDegreeFourCycle_of_smoothCubic_and_etaleDegreeEight
        p hp hne D₈))
  · exact Or.inr (Or.inr h₁₁)

/-- The strong first-residual geometry at the generic degree-ten
configuration produces an effective degree-eleven cycle on the original
cubic. No reducedness or étaleness condition on the degree-sixteen completion
is required. -/
theorem effectiveDegreeElevenCycle_of_genericFirstResidualGeometry
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    [Etale (D₁₀.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 10 D₁₀
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫
          cubicConfigurationToBase p hp 10),
      DegreeTenGenericFirstResidualGeometry p hp a ha →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 11 := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 10 D₁₀
  intro a ha hgeometry
  obtain ⟨_, R, hdegree, _, _⟩ := hgeometry
  obtain ⟨z, hz⟩ := effectiveCycle_of_genericEffectiveCycle
    10 p hp hne D₁₀ a ha
    (finiteSubschemeDatumCycle
      (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) R)
  exact ⟨z, hz.trans hdegree⟩

/-- The source-faithful cycle-level version: one regular first cubic and the
selected rank drop suffice to produce and specialize an effective
degree-eleven complement. In particular, this route does not assume a
finite étale degree-eleven residual scheme or transverse intersection. -/
theorem effectiveDegreeElevenCycle_of_genericSelectedFinrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    [Etale (D₁₀.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 10 D₁₀
    ∀ (a : CommRingCat.of K ⟶
        CommRingCat.of (cubicConfigurationBase p hp 10).functionField)
      (ha : Spec.map a =
        cubicConfigurationGenericBaseMap p hp 10 ≫
          cubicConfigurationToBase p hp 10)
      (S : DegreeTenRegularCubicSectionEmbeddingData
        (p.map a.hom) (hp.map a.hom)
        (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha)),
      DegreeTenRegularCubicSectionSelectedFinrankDrop
          (p.map a.hom) (hp.map a.hom)
          (cubicConfigurationGenericFiniteSubscheme p hp 10 a ha) S →
        ∃ z : EffectiveZeroCycle (hypersurface p hp),
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 11 := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 10 D₁₀
  intro a ha S hdrop
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  let Dη := cubicConfigurationGenericFiniteSubscheme p hp 10 a ha
  have hneη : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 10 a hne
  obtain ⟨zη, hzη⟩ :=
    exists_degreeTenComplementCycle_of_regularCubicSectionEmbeddingData_of_selectedFinrankDrop
      (p.map a.hom) (hp.map a.hom) hneη Dη S hdrop
  obtain ⟨z, hz⟩ := effectiveCycle_of_genericEffectiveCycle
    10 p hp hne D₁₀ a ha zη
  exact ⟨z, hz.trans hzη⟩

/-- Voisin's generic associated-component avoidance alone suffices for the
first degree-eleven effectivity conclusion. Smoothness already constructs
the first regular cubic; proper intersection supplies the effective
complement, with no transversality hypothesis. -/
theorem effectiveDegreeElevenCycle_of_genericThirdCubicAvoidance
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    [Etale (D₁₀.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 10 D₁₀
    GenericDegreeTenThirdCubicAvoidance p hp →
      ∃ z : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 11 := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 10 D₁₀
  intro havoid
  obtain ⟨a, ha⟩ := exists_cubicConfigurationGenericBaseMap p hp 10
  letI : CharZero (cubicConfigurationBase p hp 10).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 10
  letI : Infinite (cubicConfigurationBase p hp 10).functionField :=
    CharZero.infinite _
  letI : Smooth (hypersurfaceToBase (p.map a.hom) (hp.map a.hom)) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 10 a
  let Dη := cubicConfigurationGenericFiniteSubscheme p hp 10 a ha
  have hneη : p.map a.hom ≠ 0 :=
    cubicConfigurationCoefficientChange_ne_zero p hp 10 a hne
  obtain ⟨S⟩ := nonempty_degreeTenRegularCubicSectionEmbeddingData_of_smooth_cubic
    (p.map a.hom) (hp.map a.hom) hneη Dη
  have hdropC :=
    (GenericDegreeTenThirdCubicAvoidance.finrankDrop p hp havoid)
      a ha S.completion
  have hdropS :=
    DegreeTenRegularCubicSectionSelectedFinrankDrop.ofCompletionFinrankDrop
      (p.map a.hom) (hp.map a.hom) Dη S hdropC
  exact effectiveDegreeElevenCycle_of_genericSelectedFinrankDrop
    p hp hne D₁₀ a ha S hdropS

/-- The first generic residual, under associated-component avoidance, enters
the later construction through an étale degree-eight or degree-eleven closed
point, unless it has already produced a rational point. This removes any
need to assume the first residual itself is étale for the rational-point
route. -/
theorem section_or_degreeEight_or_degreeEleven_etaleDatum_of_genericThirdCubicAvoidance
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    [Etale (D₁₀.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp 10) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
        p hp hne 10 D₁₀
    GenericDegreeTenThirdCubicAvoidance p hp →
      (∃ a : Spec (.of K) ⟶ hypersurface p hp,
        a ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
      (∃ D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8,
        Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)) ∨
      (∃ D₁₁ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
        Etale (D₁₁.val.subschemeι ≫ hypersurfaceToBase p hp)) := by
  letI : IsIntegral (cubicConfigurationBase p hp 10) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp hne 10 D₁₀
  intro havoid
  obtain ⟨z, hz⟩ :=
    effectiveDegreeElevenCycle_of_genericThirdCubicAvoidance
      p hp hne D₁₀ havoid
  exact section_or_degreeEight_or_degreeEleven_etaleDatum_of_effectiveDegreeEleven
    p hp hne z hz

end PfaffianDescent
