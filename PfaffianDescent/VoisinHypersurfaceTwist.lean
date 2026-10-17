import PfaffianDescent.VoisinHypersurfaceCokernel

/-!
# Negative twists restricted to a projective hypersurface

This file constructs the map on concrete homogeneous-fraction stalks from an
ambient negative twist to the corresponding negative twist on a projective
hypersurface.  It proves the general local exactness calculation

`O(-(m+d))_x -> O(-m)_x -> O_S(-m)_y`.

For a cubic and `m = 3`, this is the local algebra needed for Voisin's
restriction sequence `O(-6) -> O(-3) -> i_* O_S(-3)`.
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

/-- A graded ring map carries the concrete stalk model of `O(-m)` on the
source Proj to the corresponding stalk model on the target Proj. -/
noncomputable def gradedRingHomTwistStalkMap
    (f : 𝒢 →+*ᵍ ℋ)
    (hf : HomogeneousIdeal.irrelevant ℋ ≤
      (HomogeneousIdeal.irrelevant 𝒢).map f)
    (m : ℕ) (y : ProjectiveSpectrum ℋ) :
    let x := ProjectiveSpectrum.comap f hf y
    stalkSubmodule 𝒢 x.asHomogeneousIdeal.toIdeal m →+
      stalkSubmodule ℋ y.asHomogeneousIdeal.toIdeal m := by
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
          exact zero_mem ℋ y.asHomogeneousIdeal.toIdeal m
        · right
          let a' : ℋ i := ⟨f a, f.2 a.2⟩
          let b' : ℋ (i + m) := ⟨f b, f.2 b.2⟩
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
/-- A section of `O(-m)` maps pointwise along a graded ring map to a section
of `O(-m)` on the inverse-image open. -/
noncomputable def gradedRingHomTwistSection
    (f : 𝒢 →+*ᵍ ℋ)
    (hf : HomogeneousIdeal.irrelevant ℋ ≤
      (HomogeneousIdeal.irrelevant 𝒢).map f)
    (m : ℕ) (U : Opens (Proj 𝒢))
    (z : (sheafOfModules 𝒢 m).val.obj (op U)) :
    (sheafOfModules ℋ m).val.obj (op ((Proj.map f hf) ⁻¹ᵁ U)) := by
  refine ⟨fun y => ((gradedRingHomTwistStalkMap 𝒢 ℋ f hf m y.1)
    (sectionValue 𝒢 m (op U) z ⟨Proj.map f hf y.1, y.2⟩)).1, ?_⟩
  intro y
  rcases z.2 ⟨Proj.map f hf y.1, y.2⟩ with ⟨V, hyV, j, hV⟩
  refine ⟨(Proj.map f hf) ⁻¹ᵁ V, ?_, ?_, ?_⟩
  · exact hyV
  · exact (Opens.map (Proj.map f hf).base).map j
  · rcases hV with hzero | ⟨i, a, b, hb, hval⟩
    · left
      funext x
      change Localization.localRingHom
          (pointIdeal 𝒢 (Proj.map f hf x.1))
          (pointIdeal ℋ x.1) f.toRingHom rfl
          (z.1 (j ⟨Proj.map f hf x.1, x.2⟩)) = 0
      rw [congrFun hzero ⟨Proj.map f hf x.1, x.2⟩]
      change Localization.localRingHom
          (pointIdeal 𝒢 (Proj.map f hf x.1))
          (pointIdeal ℋ x.1) f.toRingHom rfl 0 = 0
      exact map_zero _
    · right
      let a' : ℋ i := ⟨f a, f.2 a.2⟩
      let b' : ℋ (i + m) := ⟨f b, f.2 b.2⟩
      have hb' : ∀ x : (Proj.map f hf) ⁻¹ᵁ V,
          (b' : B) ∈ (pointIdeal ℋ x.1).primeCompl := by
        intro x
        rw [Ideal.mem_primeCompl_iff]
        intro hmem
        have hcomap : (b : A) ∈
            pointIdeal 𝒢 (Proj.map f hf x.1) := by
          change (b : A) ∈ Ideal.comap f.toRingHom (pointIdeal ℋ x.1)
          exact hmem
        exact (hb ⟨Proj.map f hf x.1, x.2⟩) hcomap
      refine ⟨i, a', b', hb', fun x => ?_⟩
      change Localization.localRingHom
          (pointIdeal 𝒢 (Proj.map f hf x.1))
          (pointIdeal ℋ x.1) f.toRingHom rfl
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
/-- Restriction of negative twists along the Proj map induced by a graded
ring homomorphism, as a genuine morphism of module sheaves. -/
noncomputable def gradedRingHomTwistToPushforward
    (f : 𝒢 →+*ᵍ ℋ)
    (hf : HomogeneousIdeal.irrelevant ℋ ≤
      (HomogeneousIdeal.irrelevant 𝒢).map f)
    (m : ℕ) :
    sheafOfModules 𝒢 m ⟶
      (Scheme.Modules.pushforward (Proj.map f hf)).obj
        (sheafOfModules ℋ m) where
  val :=
    { app := fun U => by
        letI : Module ((Proj 𝒢).ringCatSheaf.obj.obj U)
            ((presheafInAddCommGrp 𝒢 m).obj U) := by
          change Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒢).1.obj U)
            ((sheafInType 𝒢 m).1.obj U)
          infer_instance
        let W := op ((Proj.map f hf) ⁻¹ᵁ U.unop)
        let N := (modulePresheaf ℋ m).obj W
        letI : Module ((Proj ℋ).ringCatSheaf.obj.obj W) N := N.isModule
        letI : Module ((Proj 𝒢).ringCatSheaf.obj.obj U) N :=
          Module.compHom N ((Proj.map f hf).app U.unop).hom
        change (modulePresheaf 𝒢 m).obj U ⟶
          (ModuleCat.restrictScalars ((Proj.map f hf).app U.unop).hom).obj
            ((modulePresheaf ℋ m).obj
              (op ((Proj.map f hf) ⁻¹ᵁ U.unop)))
        exact ModuleCat.ofHom
          { toFun := gradedRingHomTwistSection 𝒢 ℋ f hf m U.unop
            map_add' := by
              intro z w
              apply Subtype.ext
              funext y
              change ((gradedRingHomTwistStalkMap 𝒢 ℋ f hf m y.1)
                (sectionValue 𝒢 m U (z + w)
                  ⟨Proj.map f hf y.1, y.2⟩)).1 = _
              change ((gradedRingHomTwistStalkMap 𝒢 ℋ f hf m y.1)
                (sectionValue 𝒢 m U z
                  ⟨Proj.map f hf y.1, y.2⟩ +
                 sectionValue 𝒢 m U w
                  ⟨Proj.map f hf y.1, y.2⟩)).1 = _
              rw [map_add]
              rfl
            map_smul' := by
              intro r z
              apply Subtype.ext
              funext y
              change Localization.localRingHom
                  (pointIdeal 𝒢 (Proj.map f hf y.1))
                  (pointIdeal ℋ y.1) f.toRingHom rfl
                  ((r.1 ⟨Proj.map f hf y.1, y.2⟩).val *
                    z.1 ⟨Proj.map f hf y.1, y.2⟩) =
                (HomogeneousLocalization.localRingHom f
                  (pointIdeal 𝒢 (Proj.map f hf y.1))
                  (pointIdeal ℋ y.1) rfl
                    (r.1 ⟨Proj.map f hf y.1, y.2⟩)).val *
                  Localization.localRingHom
                    (pointIdeal 𝒢 (Proj.map f hf y.1))
                    (pointIdeal ℋ y.1) f.toRingHom rfl
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
/-- On categorical stalks, the graded restriction morphism is the concrete
map on homogeneous-fraction stalk models. -/
theorem gradedRingHomTwistToPushforward_stalkMap_compat
    (f : 𝒢 →+*ᵍ ℋ)
    (hf : HomogeneousIdeal.irrelevant ℋ ≤
      (HomogeneousIdeal.irrelevant 𝒢).map f)
    (m : ℕ) (y : Proj ℋ)
    (z : (sheafOfModules 𝒢 m).presheaf.stalk (Proj.map f hf y)) :
    stalkToFractionModule ℋ m y
      (TopCat.Presheaf.stalkPushforward AddCommGrpCat
        (Proj.map f hf).base
        (sheafOfModules ℋ m).val.presheaf y
        (schemeModuleStalkLinearMap
          (gradedRingHomTwistToPushforward 𝒢 ℋ f hf m)
          (Proj.map f hf y) z)) =
      gradedRingHomTwistStalkMap 𝒢 ℋ f hf m y
        (stalkToFractionModule 𝒢 m (Proj.map f hf y) z) := by
  obtain ⟨U, hyU, s, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq
      (modulePresheaf 𝒢 m).presheaf z
  let g := gradedRingHomTwistToPushforward 𝒢 ℋ f hf m
  have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (C := AddCommGrpCat)
    (F := (modulePresheaf 𝒢 m).presheaf)
    (G := ((Scheme.Modules.pushforward (Proj.map f hf)).obj
      (sheafOfModules ℋ m)).presheaf)
    (f := g.mapPresheaf)
    U (Proj.map f hf y) hyU s
  have hmap' :
      schemeModuleStalkLinearMap g (Proj.map f hf y)
          (TopCat.Presheaf.germ (modulePresheaf 𝒢 m).presheaf
            U (Proj.map f hf y) hyU s) =
        TopCat.Presheaf.germ
          ((Scheme.Modules.pushforward (Proj.map f hf)).obj
            (sheafOfModules ℋ m)).presheaf
          U (Proj.map f hf y) hyU
          (g.val.app (op U) s) := by
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat
      (Proj.map f hf y)).map g.mapPresheaf
        (TopCat.Presheaf.germ (modulePresheaf 𝒢 m).presheaf
          U (Proj.map f hf y) hyU s) = _
    convert hmap using 1 <;> rfl
  erw [hmap']
  have hpush := TopCat.Presheaf.stalkPushforward_germ_apply
    AddCommGrpCat (Proj.map f hf).base
    (sheafOfModules ℋ m).val.presheaf U y hyU (g.val.app (op U) s)
  erw [hpush]
  have ht := stalkToFractionModule_germ ℋ m
    ((Proj.map f hf) ⁻¹ᵁ U) y hyU (g.val.app (op U) s)
  erw [ht]
  have hs := stalkToFractionModule_germ 𝒢 m U
    (Proj.map f hf y) hyU s
  rw [hs]
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type u} {σ : Type} [Field K]
local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ K

/-- Restriction from the ambient negative twist to the pushed-forward
negative twist on the projective hypersurface. -/
noncomputable def hypersurfaceTwistToPushforward
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ) :
    sheafOfModules 𝒜 m ⟶
      (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (sheafOfModules (grading (equationIdeal p hp)) m) :=
  gradedRingHomTwistToPushforward 𝒜 (grading (equationIdeal p hp))
    (quotientGradedRingHom (equationIdeal p hp))
    (irrelevant_le_map_quotientGradedRingHom (equationIdeal p hp)) m

noncomputable def hypersurfaceTwistStalkMap
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ) (y : ProjectiveSpectrum (grading (equationIdeal p hp))) :
    let I := equationIdeal p hp
    let ℬ := grading I
    let q := quotientGradedRingHom I
    let x := ProjectiveSpectrum.comap q
      (irrelevant_le_map_quotientGradedRingHom I) y
    stalkSubmodule 𝒜 x.asHomogeneousIdeal.toIdeal m →+
      stalkSubmodule ℬ y.asHomogeneousIdeal.toIdeal m := by
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
  let hloc := Localization.localRingHom
    x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal q.toRingHom hxy
  exact
    { toFun := fun z => ⟨hloc z.1, by
        rcases z.2 with hz0 | ⟨i, a, b, hb, hz⟩
        · rw [hz0, map_zero]
          exact zero_mem (grading (equationIdeal p hp))
            y.asHomogeneousIdeal.toIdeal m
        · right
          let a' : ℬ i := ⟨q a, q.2 a.2⟩
          let b' : ℬ (i + m) := ⟨q b, q.2 b.2⟩
          have hb' : (b' : CoordinateRing I) ∈
              y.asHomogeneousIdeal.toIdeal.primeCompl := by
            rw [Ideal.mem_primeCompl_iff]
            intro hmem
            have : (b : MvPolynomial σ K) ∈
                x.asHomogeneousIdeal.toIdeal := by
              change (b : MvPolynomial σ K) ∈
                Ideal.comap q.toRingHom y.asHomogeneousIdeal.toIdeal
              exact hmem
            exact hb this
          refine ⟨i, a', b', hb', ?_⟩
          rw [hz]
          dsimp only [hloc]
          rw [Localization.localRingHom_mk (hIJ := hxy)]
          rfl⟩
      map_zero' := Subtype.ext (map_zero hloc)
      map_add' := fun z w => Subtype.ext (map_add hloc z.1 w.1) }

set_option backward.isDefEq.respectTransparency.types false in
/-- Underlying ordinary-localization formula for the twist restriction map. -/
theorem hypersurfaceTwistStalkMap_coe
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ) (y : ProjectiveSpectrum (grading (equationIdeal p hp))) :
    let I := equationIdeal p hp
    let q := quotientGradedRingHom I
    let x := ProjectiveSpectrum.comap q
      (irrelevant_le_map_quotientGradedRingHom I) y
    ∀ z : stalkSubmodule 𝒜 x.asHomogeneousIdeal.toIdeal m,
      ((hypersurfaceTwistStalkMap p hp m y) z).1 =
        Localization.localRingHom x.asHomogeneousIdeal.toIdeal
          y.asHomogeneousIdeal.toIdeal q.toRingHom rfl z.1 := by
  dsimp only
  intro z
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient restriction map on concrete negative-twist stalks is
surjective. -/
theorem hypersurfaceTwistStalkMap_surjective
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ)
    (y : ProjectiveSpectrum (grading (equationIdeal p hp))) :
    Function.Surjective (hypersurfaceTwistStalkMap p hp m y) := by
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
      ((hypersurfaceTwistStalkMap p hp m y) 0).1 =
          (0 : stalkSubmodule (grading (equationIdeal p hp))
            y.asHomogeneousIdeal.toIdeal m).1 :=
        congrArg Subtype.val (map_zero (hypersurfaceTwistStalkMap p hp m y))
      _ = 0 := rfl
      _ = z := hz0.symm
  · have ha' := a.2
    change (a : CoordinateRing I) ∈ grading I i at ha'
    obtain ⟨a0, ha0, haeq⟩ := ha'
    have hb' := b.2
    change (b : CoordinateRing I) ∈ grading I (i + m) at hb'
    obtain ⟨b0, hb0, hbeq⟩ := hb'
    let aA : 𝒜 i := ⟨a0, ha0⟩
    let bA : 𝒜 (i + m) := ⟨b0, hb0⟩
    have hbA : (bA : MvPolynomial σ K) ∈
        x.asHomogeneousIdeal.toIdeal.primeCompl := by
      rw [Ideal.mem_primeCompl_iff]
      intro hbmem
      apply hb
      rw [← hbeq]
      exact hbmem
    let w : stalkSubmodule 𝒜 x.asHomogeneousIdeal.toIdeal m :=
      ⟨Localization.mk (aA : MvPolynomial σ K)
          ⟨(bA : MvPolynomial σ K), hbA⟩,
        Or.inr ⟨i, aA, bA, hbA, rfl⟩⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    rw [hypersurfaceTwistStalkMap_coe p hp m y]
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

theorem map_num_eq_zero_of_localRingHom_localization_mk_eq_zero
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime]
    (f : A →+* B) (hPQ : P = Ideal.comap f Q)
    (a : A) (b : P.primeCompl)
    (hzero : Localization.localRingHom P Q f hPQ
      (Localization.mk a b) = 0) :
    f a = 0 := by
  rw [Localization.localRingHom_mk, Localization.mk_eq_mk'] at hzero
  obtain ⟨c, hc⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hzero
  have hcne : (c : B) ≠ 0 := by
    intro hc0
    exact c.2 (hc0 ▸ Q.zero_mem)
  exact (mul_eq_zero.mp hc).resolve_left hcne

set_option backward.isDefEq.respectTransparency.types false in
/-- The degree `-m` hypersurface restriction sequence is exact on the
concrete homogeneous-fraction stalks. -/
theorem hypersurface_twistStalk_exact
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
      (mulHomogeneousStalk 𝒜 x.asHomogeneousIdeal.toIdeal ⟨p, hp⟩ m)
      (hypersurfaceTwistStalkMap p hp m y) := by
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
  let F := mulHomogeneousStalk 𝒜 x.asHomogeneousIdeal.toIdeal ⟨p, hp⟩ m
  let G := hypersurfaceTwistStalkMap p hp m y
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
        rw [hypersurfaceTwistStalkMap_coe p hp m y] at hzval
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
      by_cases hdi : d ≤ i
      · obtain ⟨c, hc⟩ := hfactor.1 hdi
        have hdeg : (i - d) + (m + d) = i + m := by omega
        let den : 𝒜 ((i - d) + (m + d)) := ⟨(b : MvPolynomial σ K), by
          rw [hdeg]
          exact b.2⟩
        have hden : (den : MvPolynomial σ K) ∈
            x.asHomogeneousIdeal.toIdeal.primeCompl := by
          simpa only [den] using hb
        let w : stalkSubmodule 𝒜 x.asHomogeneousIdeal.toIdeal (m + d) :=
          ⟨Localization.mk (c : MvPolynomial σ K)
              ⟨(den : MvPolynomial σ K), hden⟩,
            Or.inr ⟨i - d, c, den, hden, rfl⟩⟩
        refine ⟨w, ?_⟩
        apply Subtype.ext
        change algebraMap (MvPolynomial σ K)
            (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) p *
            Localization.mk (c : MvPolynomial σ K)
              ⟨(den : MvPolynomial σ K), hden⟩ = z.1
        rw [hzrep, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
        rw [hc]
        congr 1
        apply Subtype.ext
        simp [den]
      · have hnum : (a : MvPolynomial σ K) = 0 := hfactor.2 hdi
        refine ⟨0, ?_⟩
        apply Subtype.ext
        rw [map_zero F, hzrep, hnum, Localization.mk_zero]
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
/-- At a point of the hypersurface, the actual categorical stalk sequence
`O(-(m+d)) -> O(-m) -> i_* O_S(-m)` agrees with the concrete homogeneous
fraction calculation and is exact. -/
theorem hypersurface_twist_stalk_exact
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) (y : hypersurface p hp) :
    Function.Exact
      (schemeModuleStalkLinearMap
        (mulHomogeneous 𝒜 ⟨p, hp⟩ m)
        (hypersurfaceAmbientPoint p hp y))
      (schemeModuleStalkLinearMap
        (hypersurfaceTwistToPushforward p hp m)
        (hypersurfaceAmbientPoint p hp y)) := by
  let I := equationIdeal p hp
  let ℬ := grading I
  let q := quotientGradedRingHom I
  let hq := irrelevant_le_map_quotientGradedRingHom I
  let i := quotientProjMap I
  let x := ProjectiveSpectrum.comap q hq y
  let fA := schemeModuleStalkLinearMap
    (mulHomogeneous 𝒜 ⟨p, hp⟩ m) x
  let gA := schemeModuleStalkLinearMap
    (hypersurfaceTwistToPushforward p hp m) x
  let tSource := stalkToFractionModule 𝒜 (m + d) x
  let tMiddle := stalkToFractionModule 𝒜 m x
  let push := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
    (sheafOfModules ℬ m).val.presheaf y
  let tTarget := fun z => stalkToFractionModule ℬ m y (push z)
  let F := mulHomogeneousStalk 𝒜 x.asHomogeneousIdeal.toIdeal ⟨p, hp⟩ m
  let G := hypersurfaceTwistStalkMap p hp m y
  haveI : IsIso push :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat i.isClosedEmbedding.isInducing
      (sheafOfModules ℬ m).val.presheaf y
  have htSourceSurj : Function.Surjective tSource :=
    stalkToFractionModule_surjective 𝒜 (m + d) x
  have htMiddleInj : Function.Injective tMiddle :=
    stalkToFractionModule_injective 𝒜 m x
  have htTargetInj : Function.Injective tTarget := by
    intro a b hab
    apply (ConcreteCategory.bijective_of_isIso push).injective
    apply stalkToFractionModule_injective ℬ m y
    exact hab
  have htTargetZero : tTarget 0 = 0 := by
    change stalkToFractionModule ℬ m y (push 0) = 0
    rw [map_zero, map_zero]
  have hlocal : Function.Exact F G :=
    hypersurface_twistStalk_exact p hp m y
  have hfcomp (z) : tMiddle (fA z) = F (tSource z) := by
    exact stalkToFractionModule_stalkMap 𝒜 ⟨p, hp⟩ m x z
  have hgcomp (z) : tTarget (gA z) = G (tMiddle z) := by
    exact gradedRingHomTwistToPushforward_stalkMap_compat
      𝒜 ℬ q hq m y z
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
/-- The actual categorical twisted hypersurface sequence is exact at every
ambient point. On the hypersurface this is the homogeneous-fraction
calculation; off it, multiplication by the equation is an isomorphism and
the pushforward stalk is zero. -/
theorem hypersurface_twist_stalk_exact_all
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) (x : Proj 𝒜) :
    Function.Exact
      (schemeModuleStalkLinearMap
        (mulHomogeneous 𝒜 ⟨p, hp⟩ m) x)
      (schemeModuleStalkLinearMap
        (hypersurfaceTwistToPushforward p hp m) x) := by
  let I := equationIdeal p hp
  let ℬ := grading I
  let i := hypersurfaceToAmbient p hp
  let fA := schemeModuleStalkLinearMap
    (mulHomogeneous 𝒜 ⟨p, hp⟩ m) x
  let gA := schemeModuleStalkLinearMap
    (hypersurfaceTwistToPushforward p hp m) x
  change Function.Exact fA gA
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hx
    exact hypersurface_twist_stalk_exact p hp m y
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
      mulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
        𝒜 ⟨p, hp⟩ m x (by
          rw [Ideal.mem_primeCompl_iff]
          exact hpnot)
        mvPolynomial_irrelevant_le_span_degreeOne_small
    letI : IsIso ((schemeModuleStalkFunctor (Proj 𝒜) x).map
        (mulHomogeneous 𝒜 ⟨p, hp⟩ m)) := hIso
    have hsurj := (ConcreteCategory.bijective_of_isIso
      ((schemeModuleStalkFunctor (Proj 𝒜) x).map
        (mulHomogeneous 𝒜 ⟨p, hp⟩ m))).surjective
    change Function.Surjective fA at hsurj
    let _ : Subsingleton
        (((Scheme.Modules.pushforward i).obj
          (sheafOfModules ℬ m)).presheaf.stalk x) :=
      schemeModulePushforward_stalk_subsingleton_off_range i
        (sheafOfModules ℬ m) x hx
    intro v
    constructor
    · intro _
      exact hsurj v
    · intro _
      exact Subsingleton.elim _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by the defining equation maps to zero under restriction
to the corresponding negative twist on the projective hypersurface. -/
theorem mulHomogeneous_comp_hypersurfaceTwistToPushforward_eq_zero
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) :
    mulHomogeneous 𝒜 ⟨p, hp⟩ m ≫
      hypersurfaceTwistToPushforward p hp m = 0 := by
  apply schemeModule_hom_ext_of_stalkMap_eq
  intro x
  let F := schemeModuleStalkFunctor (Proj 𝒜) x
  letI : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive F
  change F.map (mulHomogeneous 𝒜 ⟨p, hp⟩ m ≫
      hypersurfaceTwistToPushforward p hp m) = F.map 0
  rw [F.map_comp, F.map_zero]
  apply ConcreteCategory.hom_ext
  intro z
  change (schemeModuleStalkLinearMap
      (hypersurfaceTwistToPushforward p hp m) x)
      ((schemeModuleStalkLinearMap
        (mulHomogeneous 𝒜 ⟨p, hp⟩ m) x) z) = 0
  have h := hypersurface_twist_stalk_exact_all p hp m x
  exact (h _).mpr ⟨z, rfl⟩

/-- The twisted projective hypersurface restriction sequence with the actual
pushed-forward negative twist as its third term. -/
noncomputable def hypersurfaceTwistRestrictionSequence
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) : ShortComplex (Proj 𝒜).Modules :=
  ShortComplex.mk
    (mulHomogeneous 𝒜 ⟨p, hp⟩ m)
    (hypersurfaceTwistToPushforward p hp m)
    (mulHomogeneous_comp_hypersurfaceTwistToPushforward_eq_zero p hp m)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual twisted hypersurface restriction sequence is exact. -/
theorem hypersurfaceTwistRestrictionSequence_exact
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) :
    (hypersurfaceTwistRestrictionSequence p hp m).Exact := by
  let S := hypersurfaceTwistRestrictionSequence p hp m
  let T := SheafOfModules.toSheaf.{u} (Proj 𝒜).ringCatSheaf
  letI : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map T)).mpr
  intro x
  change (S.map (schemeModuleStalkFunctor (Proj 𝒜) x)).Exact
  exact (ShortComplex.ab_exact_iff_function_exact _).mpr
    (hypersurface_twist_stalk_exact_all p hp m x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- At a point on the hypersurface, restriction to the pushed-forward
negative twist is surjective on the actual categorical stalk. -/
theorem hypersurfaceTwistToPushforward_stalkMap_surjective
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ) (y : hypersurface p hp) :
    Function.Surjective
      (schemeModuleStalkLinearMap
        (hypersurfaceTwistToPushforward p hp m)
        (hypersurfaceAmbientPoint p hp y)) := by
  let I := equationIdeal p hp
  let ℬ := grading I
  let q := quotientGradedRingHom I
  let hq := irrelevant_le_map_quotientGradedRingHom I
  let i := quotientProjMap I
  let x := ProjectiveSpectrum.comap q hq y
  let gA := schemeModuleStalkLinearMap
    (hypersurfaceTwistToPushforward p hp m) x
  let tMiddle := stalkToFractionModule 𝒜 m x
  let push := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base
    (sheafOfModules ℬ m).val.presheaf y
  let tTarget := fun z => stalkToFractionModule ℬ m y (push z)
  let G := hypersurfaceTwistStalkMap p hp m y
  haveI : IsIso push :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat i.isClosedEmbedding.isInducing
      (sheafOfModules ℬ m).val.presheaf y
  have htMiddleSurj : Function.Surjective tMiddle :=
    stalkToFractionModule_surjective 𝒜 m x
  have htTargetInj : Function.Injective tTarget := by
    intro a b hab
    apply (ConcreteCategory.bijective_of_isIso push).injective
    apply stalkToFractionModule_injective ℬ m y
    exact hab
  have hGsurj : Function.Surjective G :=
    hypersurfaceTwistStalkMap_surjective p hp m y
  have hgcomp (z) : tTarget (gA z) = G (tMiddle z) := by
    exact gradedRingHomTwistToPushforward_stalkMap_compat
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

/-- Restriction to the pushed-forward negative twist is surjective on every
ambient categorical stalk. Off the hypersurface the target stalk is zero. -/
theorem hypersurfaceTwistToPushforward_stalkMap_surjective_all
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ) (x : Proj 𝒜) :
    Function.Surjective
      (schemeModuleStalkLinearMap
        (hypersurfaceTwistToPushforward p hp m) x) := by
  let I := equationIdeal p hp
  let ℬ := grading I
  let i := hypersurfaceToAmbient p hp
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hx
    exact hypersurfaceTwistToPushforward_stalkMap_surjective p hp m y
  · let _ : Subsingleton
        (((Scheme.Modules.pushforward i).obj
          (sheafOfModules ℬ m)).presheaf.stalk x) :=
      schemeModulePushforward_stalk_subsingleton_off_range i
        (sheafOfModules ℬ m) x hx
    intro z
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The restriction morphism to a pushed-forward hypersurface twist is an
epimorphism of module sheaves. -/
theorem hypersurfaceTwistToPushforward_epi
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (m : ℕ) : Epi (hypersurfaceTwistToPushforward p hp m) := by
  let g := hypersurfaceTwistToPushforward p hp m
  let T := SheafOfModules.toSheaf.{u} (Proj 𝒜).ringCatSheaf
  have hepiSheaf : Epi (T.map g) := by
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
    apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mpr
    intro x
    change Function.Surjective (schemeModuleStalkLinearMap g x)
    exact hypersurfaceTwistToPushforward_stalkMap_surjective_all p hp m x
  constructor
  intro Z a b hab
  apply T.map_injective
  rw [← cancel_epi (T.map g)]
  simpa only [← T.map_comp] using congrArg T.map hab

/-- For a nonzero equation, the actual twisted hypersurface restriction
sequence is short exact. -/
theorem hypersurfaceTwistRestrictionSequence_shortExact
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) :
    (hypersurfaceTwistRestrictionSequence p hp m).ShortExact := by
  let S := hypersurfaceTwistRestrictionSequence p hp m
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact hypersurfaceTwistRestrictionSequence_exact p hp m
  · change Mono (mulHomogeneous 𝒜 ⟨p, hp⟩ m)
    exact mulHomogeneous_mono 𝒜 ⟨p, hp⟩ hp0 m
  · change Epi (hypersurfaceTwistToPushforward p hp m)
    exact hypersurfaceTwistToPushforward_epi p hp m

/-- The cokernel of multiplication by a nonzero homogeneous equation on a
negative twist is the pushed-forward corresponding twist on the projective
hypersurface. -/
noncomputable def hypersurfaceTwistCokernelIsoPushforward
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (m : ℕ) :
    cokernel (mulHomogeneous 𝒜 ⟨p, hp⟩ m) ≅
      (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (sheafOfModules (grading (equationIdeal p hp)) m) := by
  let S := hypersurfaceTwistRestrictionSequence p hp m
  have hS : S.ShortExact :=
    hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 m
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel S.f) hS.gIsCokernel

/-- Concrete cubic-surface form of Voisin's `l = 2` negative-twist
cohomology reduction. The only remaining inputs are the two indicated
ambient projective-space vanishings. -/
theorem cubicHypersurface_negativeThree_cohomology_one_subsingleton
    (p : MvPolynomial σ K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj 𝒜).Modules]
    [HasExt.{u} (hypersurface p hp).Modules]
    [EnoughInjectives (hypersurface p hp).Modules]
    [Subsingleton (schemeModuleCohomology (Proj 𝒜)
      (sheafOfModules 𝒜 3) 1)]
    [Subsingleton (schemeModuleCohomology (Proj 𝒜)
      (sheafOfModules 𝒜 6) 2)] :
    Subsingleton (schemeModuleCohomology (hypersurface p hp)
      (sheafOfModules (grading (equationIdeal p hp)) 3) 1) := by
  let R := hypersurfaceTwistRestrictionSequence p hp 3
  have hR : R.ShortExact :=
    hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 3
  exact voisin_l2_negativeThree_cohomology_of_ambientRestriction
    (hypersurfaceToAmbient p hp)
    (sheafOfModules (grading (equationIdeal p hp)) 3)
    (sheafOfModules 𝒜 6) (sheafOfModules 𝒜 3)
    R hR (Iso.refl _) (Iso.refl _) (Iso.refl _)

/-- Concrete cubic-surface form of Voisin's `l = 2` structure-sheaf
cohomology reduction. The only remaining inputs are `H¹(P³,O)=0` and
`H²(P³,O(-3))=0`. -/
theorem cubicHypersurface_structure_cohomology_one_subsingleton
    (p : MvPolynomial σ K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj 𝒜).Modules]
    [HasExt.{u} (hypersurface p hp).Modules]
    [EnoughInjectives (hypersurface p hp).Modules]
    [Subsingleton (schemeModuleCohomology (Proj 𝒜)
      (SheafOfModules.unit (Proj 𝒜).ringCatSheaf) 1)]
    [Subsingleton (schemeModuleCohomology (Proj 𝒜)
      (sheafOfModules 𝒜 3) 2)] :
    Subsingleton (schemeModuleCohomology (hypersurface p hp)
      (SheafOfModules.unit (hypersurface p hp).ringCatSheaf) 1) := by
  let R := hypersurfaceRestrictionSequence p hp
  have hR : R.ShortExact :=
    hypersurfaceRestrictionSequence_shortExact p hp hp0
  exact voisin_l2_structure_cohomology_of_ambientRestriction
    (hypersurfaceToAmbient p hp)
    (sheafOfModules 𝒜 3)
    (SheafOfModules.unit (Proj 𝒜).ringCatSheaf)
    R hR (Iso.refl _) (Iso.refl _) (Iso.refl _)

end ProjectiveNegativeTwist
end PfaffianDescent
