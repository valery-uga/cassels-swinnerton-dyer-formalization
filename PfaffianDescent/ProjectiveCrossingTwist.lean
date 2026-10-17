import PfaffianDescent.ProjectivePositiveTwist

/-!
# Crossing multiplication between negative and positive projective twists

A homogeneous form of degree `d` sends `O(-m)` to `O(d-m)` when `m ≤ d`.
The existing positive and negative twist files construct the two ends as
concrete fraction sheaves; this file supplies the map crossing degree zero.
The cubic case `O(-1) → O(2)` is the left map in Voisin's twisted-cubic
restriction sequence.
-/

noncomputable section

namespace PfaffianDescent

open scoped DirectSum Pointwise
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

universe u

namespace ProjectiveNegativeTwist

variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

section Stalk

variable (𝔭 : Ideal A) [𝔭.IsPrime]

local notation "Rₚ" => Localization 𝔭.primeCompl

/-- Multiplication by a homogeneous form of degree `d` carries a negative
degree-`m` fraction to a positive degree-`d-m` fraction. -/
theorem fraction_mul_homogeneous_mem_positive_of_le {d : ℕ} (s : 𝒜 d)
    (m : ℕ) (hmd : m ≤ d) {z : Rₚ}
    (hz : IsFraction 𝒜 𝔭 m z) :
    IsPositiveFraction 𝒜 𝔭 (d - m)
      (algebraMap A Rₚ (s : A) * z) := by
  rcases hz with rfl | ⟨i, a, b, hb, rfl⟩
  · exact Or.inl (by rw [mul_zero])
  right
  let num : 𝒜 ((d - m) + (i + m)) := ⟨(s : A) * a, by
    have h : (s : A) * a ∈ 𝒜 (d + i) := mul_mem_graded s.2 a.2
    have hdeg : (d - m) + (i + m) = d + i := by omega
    simpa only [hdeg] using h⟩
  let den : 𝒜 (i + m) := b
  refine ⟨i + m, num, den, hb, ?_⟩
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
  congr 1
  simp [den]

/-- The concrete stalk map induced by crossing multiplication. -/
def negativeToPositiveMulHomogeneousStalk {d : ℕ} (s : 𝒜 d)
    (m : ℕ) (hmd : m ≤ d) :
    stalkSubmodule 𝒜 𝔭 m →ₗ[HomogeneousLocalization.AtPrime 𝒜 𝔭]
      positiveStalkSubmodule 𝒜 𝔭 (d - m) where
  toFun z := ⟨algebraMap A Rₚ (s : A) * z.1,
    fraction_mul_homogeneous_mem_positive_of_le 𝒜 𝔭 s m hmd z.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact mul_add _ _ _
  map_smul' r z := by
    apply Subtype.ext
    change algebraMap A Rₚ (s : A) * (r.val * z.1) =
      r.val * (algebraMap A Rₚ (s : A) * z.1)
    ring

/-- Away from the zero locus of the multiplier, crossing multiplication is
surjective on the concrete homogeneous-fraction stalks. -/
theorem negativeToPositiveMulHomogeneousStalk_surjective_of_mem_primeCompl
    {d : ℕ} (s : 𝒜 d) (m : ℕ) (hmd : m ≤ d)
    (hs : (s : A) ∈ 𝔭.primeCompl) :
    Function.Surjective
      (negativeToPositiveMulHomogeneousStalk 𝒜 𝔭 s m hmd) := by
  intro z
  rcases z.2 with hz0 | ⟨i, a, b, hb, hzrep⟩
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    rw [map_zero, hz0]
    rfl
  · let den : 𝒜 ((d - m + i) + m) := ⟨(s : A) * b, by
      have h : (s : A) * b ∈ 𝒜 (d + i) := mul_mem_graded s.2 b.2
      have hdeg : (d - m + i) + m = d + i := by omega
      simpa only [hdeg] using h⟩
    have hden : (den : A) ∈ 𝔭.primeCompl :=
      𝔭.primeCompl.mul_mem hs hb
    let w : stalkSubmodule 𝒜 𝔭 m :=
      ⟨Localization.mk (a : A) ⟨(den : A), hden⟩,
        Or.inr ⟨d - m + i, a, den, hden, rfl⟩⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    change algebraMap A Rₚ (s : A) *
        Localization.mk (a : A) ⟨(den : A), hden⟩ = z.1
    rw [hzrep, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_one, one_mul]
    dsimp [den]
    ring

end Stalk

local notation "X" => ProjectiveSpectrum.top 𝒜

/-- A fixed negative fraction becomes a fixed positive fraction after
multiplication by a form whose degree is at least its negative twist. -/
theorem isSectionFraction_mulHomogeneous_toPositive_of_le {d : ℕ} (s : 𝒜 d)
    (m : ℕ) (hmd : m ≤ d) {U : Opens X}
    {f : ∀ x : U, Fiber 𝒜 x.1}
    (hf : IsSectionFraction 𝒜 m f) :
    IsPositiveSectionFraction 𝒜 (d - m)
      (fun x ↦ algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * f x) := by
  rcases hf with rfl | ⟨i, a, b, hb, hf⟩
  · exact Or.inl (funext fun x ↦ by
      change algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * 0 = 0
      exact mul_zero _)
  right
  let num : 𝒜 ((d - m) + (i + m)) := ⟨(s : A) * a, by
    have h : (s : A) * a ∈ 𝒜 (d + i) := mul_mem_graded s.2 a.2
    have hdeg : (d - m) + (i + m) = d + i := by omega
    simpa only [hdeg] using h⟩
  let den : 𝒜 (i + m) := b
  refine ⟨i + m, num, den, hb, fun x ↦ ?_⟩
  change algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * f x = _
  rw [hf x, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
  congr 1
  simp [den]

/-- The preceding crossing multiplication respects the local fraction
conditions defining the two twist sheaves. -/
theorem isLocallySectionFraction_mulHomogeneous_toPositive_of_le
    {d : ℕ} (s : 𝒜 d) (m : ℕ) (hmd : m ≤ d) {U : Opens X}
    {f : ∀ x : U, Fiber 𝒜 x.1}
    (hf : (isLocallySectionFraction 𝒜 m).pred f) :
    (isLocallyPositiveSectionFraction 𝒜 (d - m)).pred
      (fun x ↦ algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * f x) := by
  intro x
  rcases hf x with ⟨V, hxV, i, hV⟩
  exact ⟨V, hxV, i,
    isSectionFraction_mulHomogeneous_toPositive_of_le 𝒜 s m hmd hV⟩

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by a degree-`d` form as a map `O(-m) → O(d-m)` whenever
`m ≤ d`. -/
def negativeToPositiveMulHomogeneous {d : ℕ} (s : 𝒜 d)
    (m : ℕ) (hmd : m ≤ d) :
    sheafOfModules 𝒜 m ⟶ positiveSheafOfModules 𝒜 (d - m) where
  val :=
    { app := fun U => by
        letI : Module ((Proj 𝒜).ringCatSheaf.obj.obj U)
            ((presheafInAddCommGrp 𝒜 m).obj U) := by
          change Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
            ((sheafInType 𝒜 m).1.obj U)
          infer_instance
        letI : Module ((Proj 𝒜).ringCatSheaf.obj.obj U)
            ((positivePresheafInAddCommGrp 𝒜 (d - m)).obj U) := by
          change Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
            ((positiveSheafInType 𝒜 (d - m)).1.obj U)
          infer_instance
        exact ModuleCat.ofHom
          { toFun := fun f ↦
              ⟨fun x ↦ algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * f.1 x,
                isLocallySectionFraction_mulHomogeneous_toPositive_of_le
                  𝒜 s m hmd f.2⟩
            map_add' := by
              intro f g
              apply Subtype.ext
              funext x
              exact mul_add _ _ _
            map_smul' := by
              intro r f
              apply Subtype.ext
              funext x
              change algebraMap A (PositiveFiber 𝒜 x.1) (s : A) *
                    ((r.1 x).val * f.1 x) =
                (r.1 x).val *
                  (algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * f.1 x)
              ring }
      naturality := by
        intro U V i
        ext f
        rfl }

set_option backward.isDefEq.respectTransparency false in
/-- Over a domain, nonzero crossing multiplication is injective on every
open set. -/
theorem negativeToPositiveMulHomogeneous_app_injective [IsDomain A]
    {d : ℕ} (s : 𝒜 d) (hs : (s : A) ≠ 0)
    (m : ℕ) (hmd : m ≤ d) (U : (Opens X)ᵒᵖ) :
    Function.Injective
      ((negativeToPositiveMulHomogeneous 𝒜 s m hmd).val.app U) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  have hx := congr_fun (congr_arg Subtype.val hfg) x
  apply mul_left_cancel₀ _ hx
  intro hzero
  apply hs
  apply IsLocalization.injective (Fiber 𝒜 x.1)
    (pointIdeal 𝒜 x.1).primeCompl_le_nonZeroDivisors
  simpa using hzero

set_option backward.isDefEq.respectTransparency false in
/-- The crossing multiplication map is a monomorphism when its homogeneous
form is nonzero in a domain. -/
theorem negativeToPositiveMulHomogeneous_mono [IsDomain A]
    {d : ℕ} (s : 𝒜 d) (hs : (s : A) ≠ 0)
    (m : ℕ) (hmd : m ≤ d) :
    Mono (negativeToPositiveMulHomogeneous 𝒜 s m hmd) := by
  apply (SheafOfModules.forget (Proj 𝒜).ringCatSheaf).mono_of_mono_map
  exact PresheafOfModules.mono_of_injective
    (fun {U} ↦ negativeToPositiveMulHomogeneous_app_injective 𝒜 s hs m hmd U)

/-- The additive presheaf morphism underlying crossing multiplication. -/
def negativeToPositiveMulHomogeneousPresheaf {d : ℕ} (s : 𝒜 d)
    (m : ℕ) (hmd : m ≤ d) :
    (modulePresheaf 𝒜 m).presheaf ⟶
      (positiveModulePresheaf 𝒜 (d - m)).presheaf :=
  (PresheafOfModules.toPresheaf _).map
    (negativeToPositiveMulHomogeneous 𝒜 s m hmd).val

/-- Evaluation of crossing multiplication is the literal product in the
ambient localization. -/
theorem sectionValue_negativeToPositiveMulHomogeneous {d : ℕ} (s : 𝒜 d)
    (m : ℕ) (hmd : m ≤ d) (U : (Opens X)ᵒᵖ)
    (z : (sheafOfModules 𝒜 m).val.obj U) (x : U.unop) :
    positiveSectionValue 𝒜 (d - m) U
        ((negativeToPositiveMulHomogeneous 𝒜 s m hmd).val.app U z) x =
      negativeToPositiveMulHomogeneousStalk 𝒜
        (pointIdeal 𝒜 x.1) s m hmd
        (sectionValue 𝒜 m U z x) :=
  rfl

/-- The map on categorical stalks induced by crossing multiplication agrees
with its homogeneous-fraction formula. -/
theorem stalkToPositiveStalk_negativeToPositiveMulHomogeneous
    {d : ℕ} (s : 𝒜 d) (m : ℕ) (hmd : m ≤ d) (x : X)
    (z : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
      (modulePresheaf 𝒜 m).presheaf x)) :
    positiveStalkToFractionModule 𝒜 (d - m) x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (negativeToPositiveMulHomogeneousPresheaf 𝒜 s m hmd) z) =
      negativeToPositiveMulHomogeneousStalk 𝒜
        (pointIdeal 𝒜 x) s m hmd
        (stalkToFractionModule 𝒜 m x z) := by
  obtain ⟨U, hxU, zU, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (modulePresheaf 𝒜 m).presheaf z
  have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
    (negativeToPositiveMulHomogeneousPresheaf 𝒜 s m hmd) zU
  have happ :
      (negativeToPositiveMulHomogeneousPresheaf 𝒜 s m hmd).app (op U) zU =
        (negativeToPositiveMulHomogeneous 𝒜 s m hmd).val.app (op U) zU :=
    PresheafOfModules.toPresheaf_map_app_apply
      (negativeToPositiveMulHomogeneous 𝒜 s m hmd).val (op U) zU
  have hmap' :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (negativeToPositiveMulHomogeneousPresheaf 𝒜 s m hmd)
          (TopCat.Presheaf.germ (C := AddCommGrpCat)
            (modulePresheaf 𝒜 m).presheaf U x hxU zU) =
        TopCat.Presheaf.germ (C := AddCommGrpCat)
          (positiveModulePresheaf 𝒜 (d - m)).presheaf U x hxU
            ((negativeToPositiveMulHomogeneous 𝒜 s m hmd).val.app (op U) zU) := by
    exact hmap.trans (congr_arg
      (fun q ↦ TopCat.Presheaf.germ (C := AddCommGrpCat)
        (positiveModulePresheaf 𝒜 (d - m)).presheaf U x hxU q) happ)
  calc
    _ = positiveStalkToFractionModule 𝒜 (d - m) x
        (TopCat.Presheaf.germ (C := AddCommGrpCat)
          (positiveModulePresheaf 𝒜 (d - m)).presheaf U x hxU
            ((negativeToPositiveMulHomogeneous 𝒜 s m hmd).val.app (op U) zU)) :=
      congr_arg (positiveStalkToFractionModule 𝒜 (d - m) x) hmap'
    _ = positiveSectionValue 𝒜 (d - m) (op U)
        ((negativeToPositiveMulHomogeneous 𝒜 s m hmd).val.app (op U) zU)
          ⟨x, hxU⟩ :=
      positiveStalkToFractionModule_germ 𝒜 (d - m) U x hxU _
    _ = negativeToPositiveMulHomogeneousStalk 𝒜
        (pointIdeal 𝒜 x) s m hmd
        (sectionValue 𝒜 m (op U) zU ⟨x, hxU⟩) :=
      sectionValue_negativeToPositiveMulHomogeneous 𝒜 s m hmd (op U) zU ⟨x, hxU⟩
    _ = negativeToPositiveMulHomogeneousStalk 𝒜
        (pointIdeal 𝒜 x) s m hmd
        (stalkToFractionModule 𝒜 m x
          (TopCat.Presheaf.germ (C := AddCommGrpCat)
            (modulePresheaf 𝒜 m).presheaf U x hxU zU)) :=
      congr_arg (negativeToPositiveMulHomogeneousStalk 𝒜
        (pointIdeal 𝒜 x) s m hmd)
        (stalkToFractionModule_germ 𝒜 m U x hxU zU).symm

/-- Away from the vanishing locus of its multiplier, the categorical stalk
map of crossing multiplication is surjective. -/
theorem negativeToPositiveMulHomogeneous_stalkMap_surjective_of_mem_primeCompl
    {d : ℕ} (s : 𝒜 d) (m : ℕ) (hmd : m ≤ d) (x : X)
    (hs : (s : A) ∈ (pointIdeal 𝒜 x).primeCompl) :
    Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (negativeToPositiveMulHomogeneousPresheaf 𝒜 s m hmd)) := by
  have hsourceSurj := stalkToFractionModule_surjective 𝒜 m x
  have htargetInj := positiveStalkToFractionModule_injective 𝒜 (d - m) x
  have hconcrete := negativeToPositiveMulHomogeneousStalk_surjective_of_mem_primeCompl
    𝒜 (pointIdeal 𝒜 x) s m hmd hs
  intro z
  obtain ⟨a, ha⟩ := hconcrete
    (positiveStalkToFractionModule 𝒜 (d - m) x z)
  obtain ⟨w, hw⟩ := hsourceSurj a
  refine ⟨w, htargetInj ?_⟩
  calc
    positiveStalkToFractionModule 𝒜 (d - m) x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (negativeToPositiveMulHomogeneousPresheaf 𝒜 s m hmd) w) =
      negativeToPositiveMulHomogeneousStalk 𝒜
        (pointIdeal 𝒜 x) s m hmd
        (stalkToFractionModule 𝒜 m x w) :=
      stalkToPositiveStalk_negativeToPositiveMulHomogeneous
        𝒜 s m hmd x w
    _ = negativeToPositiveMulHomogeneousStalk 𝒜
        (pointIdeal 𝒜 x) s m hmd a := congr_arg _ hw
    _ = positiveStalkToFractionModule 𝒜 (d - m) x z := ha

end ProjectiveNegativeTwist
end PfaffianDescent
