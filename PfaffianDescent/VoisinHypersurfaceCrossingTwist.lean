import PfaffianDescent.VoisinCrossingStalkCompatibility
import PfaffianDescent.VoisinGlobalExtVanishing
import PfaffianDescent.SchemePushforwardUnitSections
import PfaffianDescent.CubicFiniteSubschemeHyperplane

/-! # Crossing multiplication in the hypersurface restriction sequence -/

noncomputable section

namespace PfaffianDescent

open scoped DirectSum Pointwise
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

namespace ProjectiveNegativeTwist

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} {σ : Type} [Field K]
local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ K

set_option linter.style.haveILetI false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Crossing multiplication by a hypersurface equation vanishes after
restriction to that hypersurface. -/
theorem negativeToPositiveMulHomogeneous_comp_hypersurfacePositiveTwistToPushforward_eq_zero
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ) (hmd : m ≤ d) :
    negativeToPositiveMulHomogeneous 𝒜 ⟨p, hp⟩ m hmd ≫
      hypersurfacePositiveTwistToPushforward p hp (d - m) = 0 := by
  apply schemeModule_hom_ext_of_stalkMap_eq
  intro x
  let F := schemeModuleStalkFunctor (Proj 𝒜) x
  letI : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive F
  change F.map (negativeToPositiveMulHomogeneous 𝒜 ⟨p, hp⟩ m hmd ≫
      hypersurfacePositiveTwistToPushforward p hp (d - m)) = F.map 0
  rw [F.map_comp, F.map_zero]
  apply ConcreteCategory.hom_ext
  intro z
  let i := hypersurfaceToAmbient p hp
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y, hy⟩ := hx
    subst x
    let I := equationIdeal p hp
    let ℬ := grading I
    let q := quotientGradedRingHom I
    let hq := irrelevant_le_map_quotientGradedRingHom I
    let x := ProjectiveSpectrum.comap q hq y
    let fA := schemeModuleStalkLinearMap
      (negativeToPositiveMulHomogeneous 𝒜 ⟨p, hp⟩ m hmd) x
    let gA := schemeModuleStalkLinearMap
      (hypersurfacePositiveTwistToPushforward p hp (d - m)) x
    let tSource := stalkToFractionModule 𝒜 m x
    let tMiddle := positiveStalkToFractionModule 𝒜 (d - m) x
    let push := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
      (positiveSheafOfModules ℬ (d - m)).val.presheaf y
    let tTarget := fun w => positiveStalkToFractionModule ℬ (d - m) y (push w)
    let FM := negativeToPositiveMulHomogeneousStalk 𝒜
      x.asHomogeneousIdeal.toIdeal ⟨p, hp⟩ m hmd
    let GM := hypersurfacePositiveTwistStalkMap p hp (d - m) y
    haveI : IsIso push :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrpCat i.isClosedEmbedding.isInducing
        (positiveSheafOfModules ℬ (d - m)).val.presheaf y
    have htTargetInj : Function.Injective tTarget := by
      intro a b hab
      apply (ConcreteCategory.bijective_of_isIso push).injective
      apply positiveStalkToFractionModule_injective ℬ (d - m) y
      exact hab
    have htTargetZero : tTarget 0 = 0 := by
      change positiveStalkToFractionModule ℬ (d - m) y (push 0) = 0
      rw [map_zero, map_zero]
    have hfcomp (w) : tMiddle (fA w) = FM (tSource w) := by
      exact stalkToPositiveStalk_negativeToPositiveMulHomogeneous
        𝒜 ⟨p, hp⟩ m hmd x w
    have hgcomp (w) : tTarget (gA w) = GM (tMiddle w) := by
      exact gradedRingHomPositiveTwistToPushforward_stalkMap_compat
        𝒜 ℬ q hq (d - m) y w
    have hzero : GM (FM (tSource z)) = 0 := by
      exact gradedRingHom_negativeToPositiveMul_stalk_eq_zero
        𝒜 ℬ q hq ⟨p, hp⟩ m hmd
        (Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_singleton p))) y (tSource z)
    apply htTargetInj
    calc
      tTarget (gA (fA z)) = GM (tMiddle (fA z)) := hgcomp (fA z)
      _ = GM (FM (tSource z)) := congrArg GM (hfcomp z)
      _ = 0 := hzero
      _ = tTarget 0 := htTargetZero.symm
  · have hsub : Subsingleton (↑(F.obj
        ((Scheme.Modules.pushforward i).obj
          (positiveSheafOfModules (grading (equationIdeal p hp)) (d - m))))) := by
      change Subsingleton
        (((Scheme.Modules.pushforward i).obj
          (positiveSheafOfModules (grading (equationIdeal p hp)) (d - m))).presheaf.stalk x)
      exact schemeModulePushforward_stalk_subsingleton_off_range i
        (positiveSheafOfModules (grading (equationIdeal p hp)) (d - m)) x hx
    exact @Subsingleton.elim _ hsub _ _

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency.types false in
/-- At a hypersurface point, the kernel of restriction on `O(d-m)` is the
image of crossing multiplication `O(-m) → O(d-m)`. -/
theorem hypersurface_crossingTwistStalk_exact
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) (hmd : m ≤ d)
    (y : ProjectiveSpectrum (grading (equationIdeal p hp))) :
    let I := equationIdeal p hp
    let q := quotientGradedRingHom I
    let x := ProjectiveSpectrum.comap q
      (irrelevant_le_map_quotientGradedRingHom I) y
    Function.Exact
      (negativeToPositiveMulHomogeneousStalk 𝒜
        x.asHomogeneousIdeal.toIdeal ⟨p, hp⟩ m hmd)
      (hypersurfacePositiveTwistStalkMap p hp (d - m) y) := by
  dsimp only
  let I := equationIdeal p hp
  let ℬ := grading I
  let q := quotientGradedRingHom I
  let x := ProjectiveSpectrum.comap q
    (irrelevant_le_map_quotientGradedRingHom I) y
  letI : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  letI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have hxy : x.asHomogeneousIdeal.toIdeal =
      Ideal.comap q.toRingHom y.asHomogeneousIdeal.toIdeal := rfl
  let F := negativeToPositiveMulHomogeneousStalk 𝒜
    x.asHomogeneousIdeal.toIdeal ⟨p, hp⟩ m hmd
  let G := hypersurfacePositiveTwistStalkMap p hp (d - m) y
  change Function.Exact F G
  intro z
  constructor
  · intro hz
    rcases z.2 with hz0 | ⟨i, a, b, hb, hzrep⟩
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      rw [map_zero, hz0]
      rfl
    · have hzmap : Localization.localRingHom
          x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal
          q.toRingHom hxy (Localization.mk (a : MvPolynomial σ K)
            ⟨(b : MvPolynomial σ K), hb⟩) = 0 := by
        have hzval := congrArg Subtype.val hz
        change (G z).1 = 0 at hzval
        rw [hypersurfacePositiveTwistStalkMap_coe p hp (d - m) y] at hzval
        rw [hzrep] at hzval
        exact hzval
      have hqnum : q (a : MvPolynomial σ K) = 0 :=
        map_num_eq_zero_of_localRingHom_localization_mk_eq_zero
          x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal
          q.toRingHom hxy a ⟨b, hb⟩ hzmap
      have hmem : (a : MvPolynomial σ K) ∈
          Ideal.span ({p} : Set (MvPolynomial σ K)) :=
        Ideal.Quotient.eq_zero_iff_mem.mp hqnum
      have hfactor := homogeneous_mem_span_singleton_factor
        ⟨p, hp⟩ a hmem
      by_cases hmi : m ≤ i
      · obtain ⟨c, hc⟩ := hfactor.1 (by omega)
        have hcdeg : (d - m + i) - d = i - m := by omega
        let c' : 𝒜 (i - m) := ⟨c, by
          rw [← hcdeg]
          exact c.2⟩
        let b' : 𝒜 ((i - m) + m) := ⟨b, by
          rw [show (i - m) + m = i by omega]
          exact b.2⟩
        have hc' : p * (c' : MvPolynomial σ K) = a := by
          simpa only [c'] using hc
        let w : stalkSubmodule 𝒜 x.asHomogeneousIdeal.toIdeal m :=
          ⟨Localization.mk (c' : MvPolynomial σ K)
              ⟨(b' : MvPolynomial σ K), by
                rw [show (b' : MvPolynomial σ K) = b by rfl]
                exact hb⟩,
            Or.inr ⟨i - m, c', b', by
              rw [show (b' : MvPolynomial σ K) = b by rfl]
              exact hb, rfl⟩⟩
        refine ⟨w, ?_⟩
        apply Subtype.ext
        change algebraMap (MvPolynomial σ K)
            (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) p *
            Localization.mk (c' : MvPolynomial σ K) _ = z.1
        rw [hzrep, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
        rw [hc']
        congr 1
        apply Subtype.ext
        simp [b']
      · have ha0 : (a : MvPolynomial σ K) = 0 :=
          hfactor.2 (by omega)
        refine ⟨0, ?_⟩
        apply Subtype.ext
        rw [map_zero, hzrep, ha0, Localization.mk_zero]
        rfl
  · rintro ⟨w, rfl⟩
    apply Subtype.ext
    change (G (F w)).1 = 0
    change Localization.localRingHom
        x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal
        q.toRingHom hxy
        (algebraMap (MvPolynomial σ K)
          (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) p * w.1) = 0
    rw [map_mul]
    have hpzero : q (p : MvPolynomial σ K) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_singleton p))
    have hploc : Localization.localRingHom
        x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal
        q.toRingHom hxy
        (algebraMap (MvPolynomial σ K)
          (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) p) = 0 := by
      have hpzero' : q.toRingHom p = 0 := hpzero
      rw [← Localization.mk_one_eq_algebraMap,
        Localization.localRingHom_mk, hpzero', Localization.mk_zero]
    rw [hploc, zero_mul]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The mixed-sign restriction complex is exact on every ambient stalk. -/
theorem hypersurface_crossingTwist_stalk_exact_all
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) (hmd : m ≤ d) (x : Proj 𝒜) :
    Function.Exact
      (schemeModuleStalkLinearMap
        (negativeToPositiveMulHomogeneous 𝒜 ⟨p, hp⟩ m hmd) x)
      (schemeModuleStalkLinearMap
        (hypersurfacePositiveTwistToPushforward p hp (d - m)) x) := by
  let I := equationIdeal p hp
  let ℬ := grading I
  let i := hypersurfaceToAmbient p hp
  let fA := schemeModuleStalkLinearMap
    (negativeToPositiveMulHomogeneous 𝒜 ⟨p, hp⟩ m hmd) x
  let gA := schemeModuleStalkLinearMap
    (hypersurfacePositiveTwistToPushforward p hp (d - m)) x
  change Function.Exact fA gA
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hx
    let q := quotientGradedRingHom I
    let hq := irrelevant_le_map_quotientGradedRingHom I
    let x := ProjectiveSpectrum.comap q hq y
    let tSource := stalkToFractionModule 𝒜 m x
    let tMiddle := positiveStalkToFractionModule 𝒜 (d - m) x
    let push := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
      (positiveSheafOfModules ℬ (d - m)).val.presheaf y
    let tTarget := fun z => positiveStalkToFractionModule ℬ (d - m) y (push z)
    let FM := negativeToPositiveMulHomogeneousStalk 𝒜
      x.asHomogeneousIdeal.toIdeal ⟨p, hp⟩ m hmd
    let GM := hypersurfacePositiveTwistStalkMap p hp (d - m) y
    haveI : IsIso push :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrpCat i.isClosedEmbedding.isInducing
        (positiveSheafOfModules ℬ (d - m)).val.presheaf y
    have htSourceSurj : Function.Surjective tSource :=
      stalkToFractionModule_surjective 𝒜 m x
    have htMiddleInj : Function.Injective tMiddle :=
      positiveStalkToFractionModule_injective 𝒜 (d - m) x
    have htTargetInj : Function.Injective tTarget := by
      intro a b hab
      apply (ConcreteCategory.bijective_of_isIso push).injective
      apply positiveStalkToFractionModule_injective ℬ (d - m) y
      exact hab
    have htTargetZero : tTarget 0 = 0 := by
      change positiveStalkToFractionModule ℬ (d - m) y (push 0) = 0
      rw [map_zero, map_zero]
    have hlocal : Function.Exact FM GM :=
      hypersurface_crossingTwistStalk_exact p hp m hmd y
    have hfcomp (z) : tMiddle (fA z) = FM (tSource z) := by
      exact stalkToPositiveStalk_negativeToPositiveMulHomogeneous
        𝒜 ⟨p, hp⟩ m hmd x z
    have hgcomp (z) : tTarget (gA z) = GM (tMiddle z) := by
      exact gradedRingHomPositiveTwistToPushforward_stalkMap_compat
        𝒜 ℬ q hq (d - m) y z
    intro v
    constructor
    · intro hgv
      have hG : GM (tMiddle v) = 0 := by
        calc
          GM (tMiddle v) = tTarget (gA v) := (hgcomp v).symm
          _ = tTarget 0 := congrArg tTarget hgv
          _ = 0 := htTargetZero
      obtain ⟨w, hw⟩ := (hlocal (tMiddle v)).mp hG
      obtain ⟨z, hz⟩ := htSourceSurj w
      refine ⟨z, htMiddleInj ?_⟩
      rw [hfcomp, hz, hw]
    · rintro ⟨z, rfl⟩
      apply htTargetInj
      have hzero : GM (FM (tSource z)) = 0 :=
        (hlocal (FM (tSource z))).mpr ⟨tSource z, rfl⟩
      calc
        tTarget (gA (fA z)) = GM (tMiddle (fA z)) := hgcomp (fA z)
        _ = GM (FM (tSource z)) := congrArg GM (hfcomp z)
        _ = 0 := hzero
        _ = tTarget 0 := htTargetZero.symm
  · have hpnot : p ∉ x.asHomogeneousIdeal.toIdeal := by
      intro hpx
      apply hx
      change x ∈ Set.range
        (quotientProjMap (equationIdeal p hp))
      rw [quotientProjMap_mem_range_iff]
      change Ideal.span ({p} : Set (MvPolynomial σ K)) ≤
        x.asHomogeneousIdeal.toIdeal
      rw [Ideal.span_le]
      simpa only [Set.singleton_subset_iff]
    have hsurj :=
      negativeToPositiveMulHomogeneous_stalkMap_surjective_of_mem_primeCompl
        𝒜 ⟨p, hp⟩ m hmd x (by
          rw [Ideal.mem_primeCompl_iff]
          exact hpnot)
    change Function.Surjective fA at hsurj
    let _ : Subsingleton
        (((Scheme.Modules.pushforward i).obj
          (positiveSheafOfModules ℬ (d - m))).presheaf.stalk x) :=
      schemeModulePushforward_stalk_subsingleton_off_range i
        (positiveSheafOfModules ℬ (d - m)) x hx
    intro v
    constructor
    · intro _
      exact hsurj v
    · intro _
      exact Subsingleton.elim _ _

/-- The mixed-sign hypersurface restriction complex
`O(-m) → O(d-m) → i_* O_S(d-m)`.  For a cubic and `m = 1`, this is
Voisin's `O(-1) → O(2) → i_*O_S(2)` complex. -/
noncomputable def hypersurfaceCrossingTwistRestrictionSequence
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ) (hmd : m ≤ d) : ShortComplex (Proj 𝒜).Modules :=
  ShortComplex.mk
    (negativeToPositiveMulHomogeneous 𝒜 ⟨p, hp⟩ m hmd)
    (hypersurfacePositiveTwistToPushforward p hp (d - m))
    (negativeToPositiveMulHomogeneous_comp_hypersurfacePositiveTwistToPushforward_eq_zero
      p hp m hmd)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The mixed-sign hypersurface restriction complex is exact. -/
theorem hypersurfaceCrossingTwistRestrictionSequence_exact
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) (hmd : m ≤ d) :
    (hypersurfaceCrossingTwistRestrictionSequence p hp m hmd).Exact := by
  let S := hypersurfaceCrossingTwistRestrictionSequence p hp m hmd
  let T := SheafOfModules.toSheaf.{u} (Proj 𝒜).ringCatSheaf
  haveI : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map T)).mpr
  intro x
  change (S.map (schemeModuleStalkFunctor (Proj 𝒜) x)).Exact
  exact (ShortComplex.ab_exact_iff_function_exact _).mpr
    (hypersurface_crossingTwist_stalk_exact_all p hp m hmd x)

/-- The first map in the mixed-sign hypersurface restriction complex is
monic when the defining form is nonzero. -/
theorem hypersurfaceCrossingTwistRestrictionSequence_mono
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (hp0 : p ≠ 0) (m : ℕ) (hmd : m ≤ d) :
    Mono (hypersurfaceCrossingTwistRestrictionSequence p hp m hmd).f := by
  change Mono (negativeToPositiveMulHomogeneous 𝒜 ⟨p, hp⟩ m hmd)
  exact negativeToPositiveMulHomogeneous_mono 𝒜 ⟨p, hp⟩ hp0 m hmd

/-- For a nonzero equation with domain coordinate ring, the mixed-sign
hypersurface restriction complex is short exact. -/
theorem hypersurfaceCrossingTwistRestrictionSequence_shortExact
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (hp0 : p ≠ 0) [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) (hmd : m ≤ d) :
    (hypersurfaceCrossingTwistRestrictionSequence p hp m hmd).ShortExact := by
  let S := hypersurfaceCrossingTwistRestrictionSequence p hp m hmd
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact hypersurfaceCrossingTwistRestrictionSequence_exact p hp m hmd
  · exact hypersurfaceCrossingTwistRestrictionSequence_mono p hp hp0 m hmd
  · change Epi (hypersurfacePositiveTwistToPushforward p hp (d - m))
    exact hypersurfacePositiveTwistToPushforward_epi p hp (d - m)

/-- The cubic specialization of the mixed-sign hypersurface restriction
complex has the literal terms `O(-1) → O(2) → i_*O_S(2)`. -/
noncomputable def cubicCrossingTwistRestrictionSequence
    (p : MvPolynomial σ K) (hp : p.IsHomogeneous 3) :
    ShortComplex (Proj 𝒜).Modules :=
  hypersurfaceCrossingTwistRestrictionSequence p hp 1 (by omega)

/-- The literal cubic sequence `O(-1) → O(2) → i_*O_S(2)` is short exact. -/
theorem cubicCrossingTwistRestrictionSequence_shortExact
    (p : MvPolynomial σ K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [IsDomain (CoordinateRing (equationIdeal p hp))] :
    (cubicCrossingTwistRestrictionSequence p hp).ShortExact := by
  exact hypersurfaceCrossingTwistRestrictionSequence_shortExact p hp hp0 1 (by omega)

/-- The cubic mixed-sign restriction sequence makes every global surface
quadratic section lift to a global ambient quadratic section. -/
theorem cubicCrossingTwistRestriction_sections_surjective
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules] :
    Function.Surjective (SheafOfModules.sectionsMap
      (cubicCrossingTwistRestrictionSequence p hp).g) := by
  let PS := MvPolynomial.homogeneousSubmodule (Fin 4) K
  let S := cubicCrossingTwistRestrictionSequence p hp
  haveI : Subsingleton (schemeModuleCohomology (Proj PS) S.X₁ 1) := by
    change Subsingleton (schemeModuleCohomology (Proj PS)
      (sheafOfModules PS 1) 1)
    exact (p3_negativeTwist_cohomology_one_and_two_subsingleton K 1).1
  have hcoh : Function.Surjective
      (schemeModuleCohomologyMap (Proj PS) S.g 0) :=
    schemeModuleCohomology_zero_map_surjective_of_one_subsingleton
      (Proj PS) S (cubicCrossingTwistRestrictionSequence_shortExact p hp hp0)
  exact sectionsMap_surjective_of_schemeModuleCohomologyMap_zero
    (Proj PS) S.g hcoh

/-- Restriction of ambient quadrics to the cubic-surface degree-two twist,
with the pushed-forward target identified with its intrinsic sections. -/
noncomputable def cubicCrossingTwistRestrictionSections
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    (positiveSheafOfModules
      (MvPolynomial.homogeneousSubmodule (Fin 4) K) 2).sections →
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2).sections :=
  fun s ↦ pushforwardModuleSectionsEquiv (hypersurfaceToAmbient p hp)
      (positiveSheafOfModules (grading (equationIdeal p hp)) 2)
      (SheafOfModules.sectionsMap
        (cubicCrossingTwistRestrictionSequence p hp).g s)

/-- Every degree-two section of a cubic surface is the restriction of an
ambient degree-two section. -/
theorem cubicCrossingTwistRestrictionSections_surjective
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules] :
    Function.Surjective (cubicCrossingTwistRestrictionSections K p hp) := by
  let i := hypersurfaceToAmbient p hp
  let M := positiveSheafOfModules (grading (equationIdeal p hp)) 2
  let e := pushforwardModuleSectionsEquiv i M
  obtain hsurj := cubicCrossingTwistRestriction_sections_surjective K p hp hp0
  intro t
  obtain ⟨s, hs⟩ := hsurj (e.symm t)
  refine ⟨s, ?_⟩
  change SheafOfModules.sectionsMap
    (hypersurfacePositiveTwistToPushforward p hp 2) s = e.symm t at hs
  change e (SheafOfModules.sectionsMap
    (hypersurfacePositiveTwistToPushforward p hp 2) s) = t
  exact e.eq_symm_apply.mp hs

/-- On a smooth cubic surface, the literal restriction sequence
`O(-1) → O(2) → i_*O_S(2)` is short exact.  Smoothness supplies the
coordinate-ring domain condition used by the homogeneous stalk computation. -/
theorem cubicCrossingTwistRestrictionSequence_shortExact_of_smooth
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)] :
    (cubicCrossingTwistRestrictionSequence p hp).ShortExact := by
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := by
    change IsDomain (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set _))
    exact (Ideal.Quotient.isDomain_iff_prime _).mpr
      (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)
  exact cubicCrossingTwistRestrictionSequence_shortExact p hp hp0

/-- On a smooth cubic surface, every global degree-two surface section lifts
to an ambient quadric. -/
theorem cubicCrossingTwistRestriction_sections_surjective_of_smooth
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules] :
    Function.Surjective (SheafOfModules.sectionsMap
      (cubicCrossingTwistRestrictionSequence p hp).g) := by
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := by
    change IsDomain (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set _))
    exact (Ideal.Quotient.isDomain_iff_prime _).mpr
      (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)
  exact cubicCrossingTwistRestriction_sections_surjective K p hp hp0

/-- On a smooth cubic surface, restriction of ambient quadrics onto the
intrinsic degree-two twist is surjective. -/
theorem cubicCrossingTwistRestrictionSections_surjective_of_smooth
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hp0 : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    [HasExt.{u} (Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)).Modules] :
    Function.Surjective (cubicCrossingTwistRestrictionSections K p hp) := by
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := by
    change IsDomain (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p} : Set _))
    exact (Ideal.Quotient.isDomain_iff_prime _).mpr
      (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)
  exact cubicCrossingTwistRestrictionSections_surjective K p hp hp0

end ProjectiveNegativeTwist
end PfaffianDescent
