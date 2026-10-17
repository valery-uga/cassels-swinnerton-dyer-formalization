import PfaffianDescent.ProjectivePositiveTwist
import PfaffianDescent.VoisinHypersurfaceTwist

/-!
# Positive twists restricted to a projective hypersurface

The concrete positive twists used for the Serre part of Voisin's argument
also descend along a homogeneous quotient.  This is the positive counterpart
of `VoisinHypersurfaceTwist`: it begins with the actual map on homogeneous
fraction stalks, rather than assuming that restriction commutes with twists.
-/

noncomputable section
namespace PfaffianDescent

open scoped DirectSum Pointwise
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
namespace ProjectiveNegativeTwist

variable {A B σ₀ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ₀ A] [AddSubgroupClass σ₀ A]
  [SetLike τ B] [AddSubgroupClass τ B]
variable (𝒢 : ℕ → σ₀) (ℋ : ℕ → τ) [GradedRing 𝒢] [GradedRing ℋ]

/-- A graded ring map carries concrete positive-twist homogeneous fractions
to the corresponding positive-twist fractions on the target Proj. -/
noncomputable def gradedRingHomPositiveTwistStalkMap
    (f : 𝒢 →+*ᵍ ℋ)
    (hf : HomogeneousIdeal.irrelevant ℋ ≤
      (HomogeneousIdeal.irrelevant 𝒢).map f)
    (m : ℕ) (y : ProjectiveSpectrum ℋ) :
    let x := ProjectiveSpectrum.comap f hf y
    positiveStalkSubmodule 𝒢 x.asHomogeneousIdeal.toIdeal m →+
      positiveStalkSubmodule ℋ y.asHomogeneousIdeal.toIdeal m := by
  dsimp only
  let x := ProjectiveSpectrum.comap f hf y
  letI : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  letI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have hxy : x.asHomogeneousIdeal.toIdeal =
      Ideal.comap f.toRingHom y.asHomogeneousIdeal.toIdeal := rfl
  let hloc := Localization.localRingHom
    x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal f.toRingHom hxy
  exact
    { toFun := fun z => ⟨hloc z.1, by
        rcases z.2 with hz0 | ⟨i, a, b, hb, hz⟩
        · rw [hz0, map_zero]
          exact positiveFraction_zero_mem ℋ y.asHomogeneousIdeal.toIdeal m
        · right
          let a' : ℋ (m + i) := ⟨f a, f.2 a.2⟩
          let b' : ℋ i := ⟨f b, f.2 b.2⟩
          have hb' : (b' : B) ∈ y.asHomogeneousIdeal.toIdeal.primeCompl := by
            rw [Ideal.mem_primeCompl_iff]
            intro hmem
            have : (b : A) ∈ x.asHomogeneousIdeal.toIdeal := by
              change (b : A) ∈ Ideal.comap f.toRingHom y.asHomogeneousIdeal.toIdeal
              exact hmem
            exact hb this
          refine ⟨i, a', b', hb', ?_⟩
          rw [hz]
          dsimp only [hloc]
          rw [Localization.localRingHom_mk (hIJ := hxy)]
          rfl⟩
      map_zero' := Subtype.ext (map_zero hloc)
      map_add' := fun z w => Subtype.ext (map_add hloc z.1 w.1) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Positive-twist sections map pointwise along a graded map. -/
noncomputable def gradedRingHomPositiveTwistSection
    (f : 𝒢 →+*ᵍ ℋ)
    (hf : HomogeneousIdeal.irrelevant ℋ ≤
      (HomogeneousIdeal.irrelevant 𝒢).map f)
    (m : ℕ) (U : Opens (Proj 𝒢))
    (z : (positiveSheafOfModules 𝒢 m).val.obj (op U)) :
    (positiveSheafOfModules ℋ m).val.obj (op ((Proj.map f hf) ⁻¹ᵁ U)) := by
  refine ⟨fun y => ((gradedRingHomPositiveTwistStalkMap 𝒢 ℋ f hf m y.1)
    (positiveSectionValue 𝒢 m (op U) z ⟨Proj.map f hf y.1, y.2⟩)).1, ?_⟩
  intro y
  rcases z.2 ⟨Proj.map f hf y.1, y.2⟩ with ⟨V, hyV, j, hV⟩
  refine ⟨(Proj.map f hf) ⁻¹ᵁ V, ?_, ?_, ?_⟩
  · exact hyV
  · exact (Opens.map (Proj.map f hf).base).map j
  · rcases hV with hzero | ⟨i, a, b, hb, hval⟩
    · left
      funext x
      change Localization.localRingHom
          (positivePointIdeal 𝒢 (Proj.map f hf x.1))
          (positivePointIdeal ℋ x.1) f.toRingHom rfl
          (z.1 (j ⟨Proj.map f hf x.1, x.2⟩)) = 0
      rw [congrFun hzero ⟨Proj.map f hf x.1, x.2⟩]
      change Localization.localRingHom
          (positivePointIdeal 𝒢 (Proj.map f hf x.1))
          (positivePointIdeal ℋ x.1) f.toRingHom rfl 0 = 0
      exact map_zero _
    · right
      let a' : ℋ (m + i) := ⟨f a, f.2 a.2⟩
      let b' : ℋ i := ⟨f b, f.2 b.2⟩
      have hb' : ∀ x : (Proj.map f hf) ⁻¹ᵁ V,
          (b' : B) ∈ (positivePointIdeal ℋ x.1).primeCompl := by
        intro x
        rw [Ideal.mem_primeCompl_iff]
        intro hmem
        have hcomap : (b : A) ∈
            positivePointIdeal 𝒢 (Proj.map f hf x.1) := by
          change (b : A) ∈ Ideal.comap f.toRingHom
            (positivePointIdeal ℋ x.1)
          exact hmem
        exact (hb ⟨Proj.map f hf x.1, x.2⟩) hcomap
      refine ⟨i, a', b', hb', fun x => ?_⟩
      change Localization.localRingHom
          (positivePointIdeal 𝒢 (Proj.map f hf x.1))
          (positivePointIdeal ℋ x.1) f.toRingHom rfl
          (z.1 (j ⟨Proj.map f hf x.1, x.2⟩)) =
        Localization.mk (a' : B) ⟨(b' : B), hb' x⟩
      have hv := hval ⟨Proj.map f hf x.1, x.2⟩
      change z.1 (j ⟨Proj.map f hf x.1, x.2⟩) =
        Localization.mk (a : A) _ at hv
      rw [hv]
      rw [Localization.localRingHom_mk]
      rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Restriction of positive twists along a Proj map, as a genuine morphism
of module sheaves. -/
noncomputable def gradedRingHomPositiveTwistToPushforward
    (f : 𝒢 →+*ᵍ ℋ)
    (hf : HomogeneousIdeal.irrelevant ℋ ≤
      (HomogeneousIdeal.irrelevant 𝒢).map f)
    (m : ℕ) :
    positiveSheafOfModules 𝒢 m ⟶
      (Scheme.Modules.pushforward (Proj.map f hf)).obj
        (positiveSheafOfModules ℋ m) where
  val :=
    { app := fun U => by
        letI : Module ((Proj 𝒢).ringCatSheaf.obj.obj U)
            ((positivePresheafInAddCommGrp 𝒢 m).obj U) := by
          change Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒢).1.obj U)
            ((positiveSheafInType 𝒢 m).1.obj U)
          infer_instance
        let W := op ((Proj.map f hf) ⁻¹ᵁ U.unop)
        let N := (positiveModulePresheaf ℋ m).obj W
        letI : Module ((Proj ℋ).ringCatSheaf.obj.obj W) N := N.isModule
        letI : Module ((Proj 𝒢).ringCatSheaf.obj.obj U) N :=
          Module.compHom N ((Proj.map f hf).app U.unop).hom
        change (positiveModulePresheaf 𝒢 m).obj U ⟶
          (ModuleCat.restrictScalars ((Proj.map f hf).app U.unop).hom).obj
            ((positiveModulePresheaf ℋ m).obj
              (op ((Proj.map f hf) ⁻¹ᵁ U.unop)))
        exact ModuleCat.ofHom
          { toFun := gradedRingHomPositiveTwistSection 𝒢 ℋ f hf m U.unop
            map_add' := by
              intro z w
              apply Subtype.ext
              funext y
              change ((gradedRingHomPositiveTwistStalkMap 𝒢 ℋ f hf m y.1)
                (positiveSectionValue 𝒢 m U (z + w)
                  ⟨Proj.map f hf y.1, y.2⟩)).1 = _
              change ((gradedRingHomPositiveTwistStalkMap 𝒢 ℋ f hf m y.1)
                (positiveSectionValue 𝒢 m U z
                  ⟨Proj.map f hf y.1, y.2⟩ +
                 positiveSectionValue 𝒢 m U w
                  ⟨Proj.map f hf y.1, y.2⟩)).1 = _
              rw [map_add]
              rfl
            map_smul' := by
              intro r z
              apply Subtype.ext
              funext y
              change Localization.localRingHom
                  (positivePointIdeal 𝒢 (Proj.map f hf y.1))
                  (positivePointIdeal ℋ y.1) f.toRingHom rfl
                  ((r.1 ⟨Proj.map f hf y.1, y.2⟩).val *
                    z.1 ⟨Proj.map f hf y.1, y.2⟩) =
                (HomogeneousLocalization.localRingHom f
                  (positivePointIdeal 𝒢 (Proj.map f hf y.1))
                  (positivePointIdeal ℋ y.1) rfl
                    (r.1 ⟨Proj.map f hf y.1, y.2⟩)).val *
                  Localization.localRingHom
                    (positivePointIdeal 𝒢 (Proj.map f hf y.1))
                    (positivePointIdeal ℋ y.1) f.toRingHom rfl
                    (z.1 ⟨Proj.map f hf y.1, y.2⟩)
              rw [map_mul, HomogeneousLocalization.val_localRingHom]
              rfl }
      naturality := by
        intro U V j
        apply ConcreteCategory.hom_ext
        intro z
        apply Subtype.ext
        funext y
        rfl }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On categorical stalks, positive restriction is the concrete map on
positive homogeneous-fraction modules. -/
theorem gradedRingHomPositiveTwistToPushforward_stalkMap_compat
    (f : 𝒢 →+*ᵍ ℋ)
    (hf : HomogeneousIdeal.irrelevant ℋ ≤
      (HomogeneousIdeal.irrelevant 𝒢).map f)
    (m : ℕ) (y : Proj ℋ)
    (z : (positiveSheafOfModules 𝒢 m).presheaf.stalk (Proj.map f hf y)) :
    positiveStalkToFractionModule ℋ m y
      (TopCat.Presheaf.stalkPushforward AddCommGrpCat
        (Proj.map f hf).base
        (positiveSheafOfModules ℋ m).val.presheaf y
        (schemeModuleStalkLinearMap
          (gradedRingHomPositiveTwistToPushforward 𝒢 ℋ f hf m)
          (Proj.map f hf y) z)) =
      gradedRingHomPositiveTwistStalkMap 𝒢 ℋ f hf m y
        (positiveStalkToFractionModule 𝒢 m (Proj.map f hf y) z) := by
  obtain ⟨U, hyU, s, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq
      (positiveModulePresheaf 𝒢 m).presheaf z
  let g := gradedRingHomPositiveTwistToPushforward 𝒢 ℋ f hf m
  have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (C := AddCommGrpCat)
    (F := (positiveModulePresheaf 𝒢 m).presheaf)
    (G := ((Scheme.Modules.pushforward (Proj.map f hf)).obj
      (positiveSheafOfModules ℋ m)).presheaf)
    (f := g.mapPresheaf)
    U (Proj.map f hf y) hyU s
  have hmap' :
      schemeModuleStalkLinearMap g (Proj.map f hf y)
          (TopCat.Presheaf.germ (positiveModulePresheaf 𝒢 m).presheaf
            U (Proj.map f hf y) hyU s) =
        TopCat.Presheaf.germ
          ((Scheme.Modules.pushforward (Proj.map f hf)).obj
            (positiveSheafOfModules ℋ m)).presheaf
          U (Proj.map f hf y) hyU
          (g.val.app (op U) s) := by
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat
      (Proj.map f hf y)).map g.mapPresheaf
        (TopCat.Presheaf.germ (positiveModulePresheaf 𝒢 m).presheaf
          U (Proj.map f hf y) hyU s) = _
    convert hmap using 1 <;> rfl
  erw [hmap']
  have hpush := TopCat.Presheaf.stalkPushforward_germ_apply
    AddCommGrpCat (Proj.map f hf).base
    (positiveSheafOfModules ℋ m).val.presheaf U y hyU (g.val.app (op U) s)
  erw [hpush]
  have ht := positiveStalkToFractionModule_germ ℋ m
    ((Proj.map f hf) ⁻¹ᵁ U) y hyU (g.val.app (op U) s)
  erw [ht]
  have hs := positiveStalkToFractionModule_germ 𝒢 m U
    (Proj.map f hf y) hyU s
  rw [hs]
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} {σ : Type} [Field K]
local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ K

/-- Restriction from the ambient positive twist to the pushed-forward
positive twist on a projective hypersurface. -/
noncomputable def hypersurfacePositiveTwistToPushforward
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ) :
    positiveSheafOfModules 𝒜 m ⟶
      (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (positiveSheafOfModules (grading (equationIdeal p hp)) m) :=
  gradedRingHomPositiveTwistToPushforward 𝒜 (grading (equationIdeal p hp))
    (quotientGradedRingHom (equationIdeal p hp))
    (irrelevant_le_map_quotientGradedRingHom (equationIdeal p hp)) m

/-- The concrete positive-twist stalk map induced by restriction to a
projective hypersurface. -/
noncomputable def hypersurfacePositiveTwistStalkMap
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ) (y : ProjectiveSpectrum (grading (equationIdeal p hp))) :
    let I := equationIdeal p hp
    let ℬ := grading I
    let q := quotientGradedRingHom I
    let x := ProjectiveSpectrum.comap q
      (irrelevant_le_map_quotientGradedRingHom I) y
    positiveStalkSubmodule 𝒜 x.asHomogeneousIdeal.toIdeal m →+
      positiveStalkSubmodule ℬ y.asHomogeneousIdeal.toIdeal m :=
  gradedRingHomPositiveTwistStalkMap 𝒜 (grading (equationIdeal p hp))
    (quotientGradedRingHom (equationIdeal p hp))
    (irrelevant_le_map_quotientGradedRingHom (equationIdeal p hp)) m y

set_option backward.isDefEq.respectTransparency.types false in
/-- Underlying ordinary-localization formula for positive twist restriction. -/
theorem hypersurfacePositiveTwistStalkMap_coe
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ) (y : ProjectiveSpectrum (grading (equationIdeal p hp))) :
    let I := equationIdeal p hp
    let q := quotientGradedRingHom I
    let x := ProjectiveSpectrum.comap q
      (irrelevant_le_map_quotientGradedRingHom I) y
    ∀ z : positiveStalkSubmodule 𝒜 x.asHomogeneousIdeal.toIdeal m,
      ((hypersurfacePositiveTwistStalkMap p hp m y) z).1 =
        Localization.localRingHom x.asHomogeneousIdeal.toIdeal
          y.asHomogeneousIdeal.toIdeal q.toRingHom rfl z.1 := by
  dsimp only
  intro z
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient map is surjective on concrete positive-twist stalks. -/
theorem hypersurfacePositiveTwistStalkMap_surjective
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ)
    (y : ProjectiveSpectrum (grading (equationIdeal p hp))) :
    Function.Surjective (hypersurfacePositiveTwistStalkMap p hp m y) := by
  let I := equationIdeal p hp
  let ℬ := grading I
  let q := quotientGradedRingHom I
  let x := ProjectiveSpectrum.comap q
    (irrelevant_le_map_quotientGradedRingHom I) y
  letI : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  letI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have hxy : x.asHomogeneousIdeal.toIdeal =
      Ideal.comap q.toRingHom y.asHomogeneousIdeal.toIdeal := rfl
  rintro ⟨z, hz⟩
  rcases hz with hz0 | ⟨i, a, b, hb, hzrep⟩
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    calc
      ((hypersurfacePositiveTwistStalkMap p hp m y) 0).1 =
          (0 : positiveStalkSubmodule (grading (equationIdeal p hp))
            y.asHomogeneousIdeal.toIdeal m).1 :=
        congrArg Subtype.val
          (map_zero (hypersurfacePositiveTwistStalkMap p hp m y))
      _ = 0 := rfl
      _ = z := hz0.symm
  · have ha' := a.2
    change (a : CoordinateRing I) ∈ grading I (m + i) at ha'
    obtain ⟨a0, ha0, haeq⟩ := ha'
    have hb' := b.2
    change (b : CoordinateRing I) ∈ grading I i at hb'
    obtain ⟨b0, hb0, hbeq⟩ := hb'
    let aA : 𝒜 (m + i) := ⟨a0, ha0⟩
    let bA : 𝒜 i := ⟨b0, hb0⟩
    have hbA : (bA : MvPolynomial σ K) ∈
        x.asHomogeneousIdeal.toIdeal.primeCompl := by
      rw [Ideal.mem_primeCompl_iff]
      intro hbmem
      apply hb
      rw [← hbeq]
      exact hbmem
    let w : positiveStalkSubmodule 𝒜 x.asHomogeneousIdeal.toIdeal m :=
      ⟨Localization.mk (aA : MvPolynomial σ K)
          ⟨(bA : MvPolynomial σ K), hbA⟩,
        Or.inr ⟨i, aA, bA, hbA, rfl⟩⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    change Localization.localRingHom
        x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal
        q.toRingHom hxy
        (Localization.mk (aA : MvPolynomial σ K)
          ⟨(bA : MvPolynomial σ K), hbA⟩) = z
    rw [Localization.localRingHom_mk]
    rw [hzrep]
    congr 1
    apply Subtype.ext
    exact hbeq

set_option backward.isDefEq.respectTransparency.types false in
/-- The positive hypersurface restriction sequence is exact on concrete
homogeneous-fraction stalks. -/
theorem hypersurface_positiveTwistStalk_exact
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ)
    (y : ProjectiveSpectrum (grading (equationIdeal p hp))) :
    let I := equationIdeal p hp
    let ℬ := grading I
    let q := quotientGradedRingHom I
    let x := ProjectiveSpectrum.comap q
      (irrelevant_le_map_quotientGradedRingHom I) y
    Function.Exact
      (positiveMulHomogeneousStalk 𝒜 x.asHomogeneousIdeal.toIdeal ⟨p, hp⟩ m)
      (hypersurfacePositiveTwistStalkMap p hp (m + d) y) := by
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
  let F := positiveMulHomogeneousStalk 𝒜 x.asHomogeneousIdeal.toIdeal ⟨p, hp⟩ m
  let G := hypersurfacePositiveTwistStalkMap p hp (m + d) y
  change Function.Exact F G
  intro z
  constructor
  · intro hz
    rcases z.2 with hz0 | ⟨i, a, b, hb, hzrep⟩
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      change (F 0).1 = z.1
      rw [map_zero, hz0]
      rfl
    · have hzmap : Localization.localRingHom
          x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal
          q.toRingHom hxy (Localization.mk (a : MvPolynomial σ K)
            ⟨(b : MvPolynomial σ K), hb⟩) = 0 := by
        have hzval := congrArg Subtype.val hz
        change (G z).1 = 0 at hzval
        rw [hypersurfacePositiveTwistStalkMap_coe p hp (m + d) y] at hzval
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
      obtain ⟨c, hc⟩ := hfactor.1 (by omega)
      have hdeg : m + d + i - d = m + i := by omega
      let c' : 𝒜 (m + i) := ⟨c, by
        rw [← hdeg]
        exact c.2⟩
      have hc' : p * (c' : MvPolynomial σ K) = a := hc
      let w : positiveStalkSubmodule 𝒜 x.asHomogeneousIdeal.toIdeal m :=
        ⟨Localization.mk (c' : MvPolynomial σ K)
            ⟨(b : MvPolynomial σ K), hb⟩,
          Or.inr ⟨i, c', b, hb, rfl⟩⟩
      refine ⟨w, ?_⟩
      apply Subtype.ext
      change algebraMap (MvPolynomial σ K)
          (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) p *
          Localization.mk (c : MvPolynomial σ K)
            ⟨(b : MvPolynomial σ K), hb⟩ = z.1
      rw [hzrep, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
      rw [hc']
      congr 1
      apply Subtype.ext
      simp
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
/-- At a point of the hypersurface, the categorical positive-twist sequence
agrees with the concrete homogeneous-fraction calculation and is exact. -/
theorem hypersurface_positiveTwist_stalk_exact
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) (y : hypersurface p hp) :
    Function.Exact
      (schemeModuleStalkLinearMap
        (positiveMulHomogeneous 𝒜 ⟨p, hp⟩ m)
        (hypersurfaceAmbientPoint p hp y))
      (schemeModuleStalkLinearMap
        (hypersurfacePositiveTwistToPushforward p hp (m + d))
        (hypersurfaceAmbientPoint p hp y)) := by
  let I := equationIdeal p hp
  let ℬ := grading I
  let q := quotientGradedRingHom I
  let hq := irrelevant_le_map_quotientGradedRingHom I
  let i := quotientProjMap I
  let x := ProjectiveSpectrum.comap q hq y
  let fA := schemeModuleStalkLinearMap
    (positiveMulHomogeneous 𝒜 ⟨p, hp⟩ m) x
  let gA := schemeModuleStalkLinearMap
    (hypersurfacePositiveTwistToPushforward p hp (m + d)) x
  let tSource := positiveStalkToFractionModule 𝒜 m x
  let tMiddle := positiveStalkToFractionModule 𝒜 (m + d) x
  let push := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
    (positiveSheafOfModules ℬ (m + d)).val.presheaf y
  let tTarget := fun z => positiveStalkToFractionModule ℬ (m + d) y (push z)
  let F := positiveMulHomogeneousStalk 𝒜 x.asHomogeneousIdeal.toIdeal ⟨p, hp⟩ m
  let G := hypersurfacePositiveTwistStalkMap p hp (m + d) y
  haveI : IsIso push :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat i.isClosedEmbedding.isInducing
      (positiveSheafOfModules ℬ (m + d)).val.presheaf y
  have htSourceSurj : Function.Surjective tSource :=
    positiveStalkToFractionModule_surjective 𝒜 m x
  have htMiddleInj : Function.Injective tMiddle :=
    positiveStalkToFractionModule_injective 𝒜 (m + d) x
  have htTargetInj : Function.Injective tTarget := by
    intro a b hab
    apply (ConcreteCategory.bijective_of_isIso push).injective
    apply positiveStalkToFractionModule_injective ℬ (m + d) y
    exact hab
  have htTargetZero : tTarget 0 = 0 := by
    change positiveStalkToFractionModule ℬ (m + d) y (push 0) = 0
    rw [map_zero, map_zero]
  have hlocal : Function.Exact F G :=
    hypersurface_positiveTwistStalk_exact p hp m y
  have hfcomp (z) : tMiddle (fA z) = F (tSource z) := by
    exact positiveStalkToFractionModule_stalkMap 𝒜 ⟨p, hp⟩ m x z
  have hgcomp (z) : tTarget (gA z) = G (tMiddle z) := by
    exact gradedRingHomPositiveTwistToPushforward_stalkMap_compat
      𝒜 ℬ q hq (m + d) y z
  change Function.Exact fA gA
  intro v
  constructor
  · intro hgv
    have hG : G (tMiddle v) = 0 := by
      calc
        G (tMiddle v) = tTarget (gA v) := (hgcomp v).symm
        _ = tTarget 0 := congrArg tTarget hgv
        _ = 0 := htTargetZero
    obtain ⟨w, hw⟩ := (hlocal (tMiddle v)).mp hG
    obtain ⟨z, hz⟩ := htSourceSurj w
    refine ⟨z, htMiddleInj ?_⟩
    rw [hfcomp, hz, hw]
  · rintro ⟨z, rfl⟩
    apply htTargetInj
    have hzero : G (F (tSource z)) = 0 :=
      (hlocal (F (tSource z))).mpr ⟨tSource z, rfl⟩
    calc
      tTarget (gA (fA z)) = G (tMiddle (fA z)) := hgcomp (fA z)
      _ = G (F (tSource z)) := congrArg G (hfcomp z)
      _ = 0 := hzero
      _ = tTarget 0 := htTargetZero.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The categorical positive restriction sequence is exact at every ambient
point.  Away from the hypersurface, its multiplication map is invertible. -/
theorem hypersurface_positiveTwist_stalk_exact_all
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) (x : Proj 𝒜) :
    Function.Exact
      (schemeModuleStalkLinearMap
        (positiveMulHomogeneous 𝒜 ⟨p, hp⟩ m) x)
      (schemeModuleStalkLinearMap
        (hypersurfacePositiveTwistToPushforward p hp (m + d)) x) := by
  let I := equationIdeal p hp
  let ℬ := grading I
  let i := hypersurfaceToAmbient p hp
  let fA := schemeModuleStalkLinearMap
    (positiveMulHomogeneous 𝒜 ⟨p, hp⟩ m) x
  let gA := schemeModuleStalkLinearMap
    (hypersurfacePositiveTwistToPushforward p hp (m + d)) x
  change Function.Exact fA gA
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hx
    exact hypersurface_positiveTwist_stalk_exact p hp m y
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
    have hIso :=
      positiveMulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
        𝒜 ⟨p, hp⟩ m x (by
          rw [Ideal.mem_primeCompl_iff]
          exact hpnot)
        mvPolynomial_irrelevant_le_span_degreeOne_small
    letI : IsIso ((schemeModuleStalkFunctor (Proj 𝒜) x).map
        (positiveMulHomogeneous 𝒜 ⟨p, hp⟩ m)) := hIso
    have hsurj := (ConcreteCategory.bijective_of_isIso
      ((schemeModuleStalkFunctor (Proj 𝒜) x).map
        (positiveMulHomogeneous 𝒜 ⟨p, hp⟩ m))).surjective
    change Function.Surjective fA at hsurj
    let _ : Subsingleton
        (((Scheme.Modules.pushforward i).obj
          (positiveSheafOfModules ℬ (m + d))).presheaf.stalk x) :=
      schemeModulePushforward_stalk_subsingleton_off_range i
        (positiveSheafOfModules ℬ (m + d)) x hx
    intro v
    constructor
    · intro _
      exact hsurj v
    · intro _
      exact Subsingleton.elim _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by the defining equation maps to zero after positive
restriction to its hypersurface. -/
theorem positiveMulHomogeneous_comp_hypersurfacePositiveTwistToPushforward_eq_zero
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) :
    positiveMulHomogeneous 𝒜 ⟨p, hp⟩ m ≫
      hypersurfacePositiveTwistToPushforward p hp (m + d) = 0 := by
  apply schemeModule_hom_ext_of_stalkMap_eq
  intro x
  let F := schemeModuleStalkFunctor (Proj 𝒜) x
  letI : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive F
  change F.map (positiveMulHomogeneous 𝒜 ⟨p, hp⟩ m ≫
      hypersurfacePositiveTwistToPushforward p hp (m + d)) = F.map 0
  rw [F.map_comp, F.map_zero]
  apply ConcreteCategory.hom_ext
  intro z
  change (schemeModuleStalkLinearMap
      (hypersurfacePositiveTwistToPushforward p hp (m + d)) x)
      ((schemeModuleStalkLinearMap
        (positiveMulHomogeneous 𝒜 ⟨p, hp⟩ m) x) z) = 0
  have h := hypersurface_positiveTwist_stalk_exact_all p hp m x
  exact (h _).mpr ⟨z, rfl⟩

/-- The positive projective hypersurface restriction sequence. -/
noncomputable def hypersurfacePositiveTwistRestrictionSequence
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) : ShortComplex (Proj 𝒜).Modules :=
  ShortComplex.mk
    (positiveMulHomogeneous 𝒜 ⟨p, hp⟩ m)
    (hypersurfacePositiveTwistToPushforward p hp (m + d))
    (positiveMulHomogeneous_comp_hypersurfacePositiveTwistToPushforward_eq_zero
      p hp m)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The positive hypersurface restriction sequence is exact. -/
theorem hypersurfacePositiveTwistRestrictionSequence_exact
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) :
    (hypersurfacePositiveTwistRestrictionSequence p hp m).Exact := by
  let S := hypersurfacePositiveTwistRestrictionSequence p hp m
  let T := SheafOfModules.toSheaf.{u} (Proj 𝒜).ringCatSheaf
  letI : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map T)).mpr
  intro x
  change (S.map (schemeModuleStalkFunctor (Proj 𝒜) x)).Exact
  exact (ShortComplex.ab_exact_iff_function_exact _).mpr
    (hypersurface_positiveTwist_stalk_exact_all p hp m x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- At a point on the hypersurface, positive restriction is surjective on
the actual categorical stalk. -/
theorem hypersurfacePositiveTwistToPushforward_stalkMap_surjective
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ) (y : hypersurface p hp) :
    Function.Surjective
      (schemeModuleStalkLinearMap
        (hypersurfacePositiveTwistToPushforward p hp m)
        (hypersurfaceAmbientPoint p hp y)) := by
  let I := equationIdeal p hp
  let ℬ := grading I
  let q := quotientGradedRingHom I
  let hq := irrelevant_le_map_quotientGradedRingHom I
  let i := quotientProjMap I
  let x := ProjectiveSpectrum.comap q hq y
  let gA := schemeModuleStalkLinearMap
    (hypersurfacePositiveTwistToPushforward p hp m) x
  let tMiddle := positiveStalkToFractionModule 𝒜 m x
  let push := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
    (positiveSheafOfModules ℬ m).val.presheaf y
  let tTarget := fun z => positiveStalkToFractionModule ℬ m y (push z)
  let G := hypersurfacePositiveTwistStalkMap p hp m y
  haveI : IsIso push :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat i.isClosedEmbedding.isInducing
      (positiveSheafOfModules ℬ m).val.presheaf y
  have htMiddleSurj : Function.Surjective tMiddle :=
    positiveStalkToFractionModule_surjective 𝒜 m x
  have htTargetInj : Function.Injective tTarget := by
    intro a b hab
    apply (ConcreteCategory.bijective_of_isIso push).injective
    apply positiveStalkToFractionModule_injective ℬ m y
    exact hab
  have hGsurj : Function.Surjective G :=
    hypersurfacePositiveTwistStalkMap_surjective p hp m y
  have hgcomp (z) : tTarget (gA z) = G (tMiddle z) := by
    exact gradedRingHomPositiveTwistToPushforward_stalkMap_compat
      𝒜 ℬ q hq m y z
  change Function.Surjective gA
  intro c
  obtain ⟨b, hb⟩ := hGsurj (tTarget c)
  obtain ⟨v, hv⟩ := htMiddleSurj b
  refine ⟨v, htTargetInj ?_⟩
  calc
    tTarget (gA v) = G (tMiddle v) := hgcomp v
    _ = G b := congrArg G hv
    _ = tTarget c := hb

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Positive restriction is surjective on every ambient stalk; outside the
hypersurface the target pushforward stalk is zero. -/
theorem hypersurfacePositiveTwistToPushforward_stalkMap_surjective_all
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ) (x : Proj 𝒜) :
    Function.Surjective
      (schemeModuleStalkLinearMap
        (hypersurfacePositiveTwistToPushforward p hp m) x) := by
  let I := equationIdeal p hp
  let ℬ := grading I
  let i := hypersurfaceToAmbient p hp
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hx
    exact hypersurfacePositiveTwistToPushforward_stalkMap_surjective p hp m y
  · let _ : Subsingleton
        (((Scheme.Modules.pushforward i).obj
          (positiveSheafOfModules ℬ m)).presheaf.stalk x) :=
      schemeModulePushforward_stalk_subsingleton_off_range i
        (positiveSheafOfModules ℬ m) x hx
    intro z
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The restriction morphism to the positive hypersurface twist is an
epimorphism of module sheaves. -/
theorem hypersurfacePositiveTwistToPushforward_epi
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ) : Epi (hypersurfacePositiveTwistToPushforward p hp m) := by
  let g := hypersurfacePositiveTwistToPushforward p hp m
  let T := SheafOfModules.toSheaf.{u} (Proj 𝒜).ringCatSheaf
  have hepiSheaf : Epi (T.map g) := by
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
    apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mpr
    intro x
    change Function.Surjective (schemeModuleStalkLinearMap g x)
    exact hypersurfacePositiveTwistToPushforward_stalkMap_surjective_all p hp m x
  constructor
  intro Z a b hab
  apply T.map_injective
  rw [← cancel_epi (T.map g)]
  simpa only [← T.map_comp] using congrArg T.map hab

/-- For a nonzero homogeneous equation, the positive hypersurface
restriction sequence is short exact. -/
theorem hypersurfacePositiveTwistRestrictionSequence_shortExact
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) :
    (hypersurfacePositiveTwistRestrictionSequence p hp m).ShortExact := by
  let S := hypersurfacePositiveTwistRestrictionSequence p hp m
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact hypersurfacePositiveTwistRestrictionSequence_exact p hp m
  · change Mono (positiveMulHomogeneous 𝒜 ⟨p, hp⟩ m)
    exact positiveMulHomogeneous_mono 𝒜 ⟨p, hp⟩ hp0 m
  · change Epi (hypersurfacePositiveTwistToPushforward p hp (m + d))
    exact hypersurfacePositiveTwistToPushforward_epi p hp (m + d)
    
end ProjectiveNegativeTwist
end PfaffianDescent
