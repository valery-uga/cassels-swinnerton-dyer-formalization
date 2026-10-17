import PfaffianDescent.SheafModuleFlasque
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Filtration
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.Sheaves.Flasque

/-!
# Affine quasicoherent acyclicity in degrees one and two

This file proves the low-degree affine vanishing theorem needed for the
standard affine cover of projective three-space.  The main algebraic input is
an Artin--Rees and Baer extension argument showing that the sheaf associated
to an injective module over a noetherian ring is flasque.  Exactness of the
tilde functor then gives vanishing for all tilde modules, and the affine
tilde--Gamma equivalence transfers the result to arbitrary quasicoherent
module sheaves on `Spec`.
-/

noncomputable section
universe u

open Submodule

namespace PfaffianDescent

open CategoryTheory.Limits

variable {R M : Type u} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M]

lemma stabilized_torsion_disjoint [Module.Finite R M] (J : Ideal R) :
    ∃ k m : ℕ,
      let H := torsionBySet R M ((J ^ k : Ideal R) : Set R)
      (∀ n, torsionBySet R M ((J ^ n : Ideal R) : Set R) ≤ H) ∧
      (J ^ m • (⊤ : Submodule R M)) ⊓ H = ⊥ := by
  let T : ℕ →o Submodule R M :=
    { toFun := fun n => torsionBySet R M ((J ^ n : Ideal R) : Set R)
      monotone' := fun n m h => torsionBySet_le_torsionBySet_pow n m h J }
  obtain ⟨k, hk⟩ : ∃ k, ∀ m, k ≤ m → T k = T m :=
    monotone_stabilizes_iff_noetherian.mpr inferInstance T
  let H := T k
  have hle (n : ℕ) : T n ≤ H := by
    rcases le_total n k with hnk | hkn
    · exact T.monotone hnk
    · change T n ≤ T k
      rw [← hk n hkn]
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul J H
  refine ⟨k, k + c, hle, ?_⟩
  change J ^ (k + c) • (⊤ : Submodule R M) ⊓ H = ⊥
  rw [hc (k + c) (by omega)]
  have hkill : J ^ k • H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y hy
      change y ∈ torsionBySet R M ((J ^ k : Ideal R) : Set R) at hy
      rw [mem_torsionBySet_iff] at hy
      simpa only [Submodule.mem_bot] using hy ⟨r, hr⟩
    · intro x y hx hy
      change x = 0 at hx
      change y = 0 at hy
      simpa [hx, hy]
  have hsub : J ^ c • (⊤ : Submodule R M) ⊓ H ≤ H := inf_le_right
  rw [show k + c - c = k by omega]
  exact le_antisymm
    ((Submodule.smul_mono le_rfl hsub).trans (le_of_eq hkill)) bot_le

lemma lincomb_cross {ι : Type u} (A : ι → M) (C : ι → R)
    (h : ∀ i j, C j • A i = C i • A j)
    (v : ι →₀ R) (j : ι) :
    C j • (Finsupp.linearCombination R A v) =
      (Finsupp.linearCombination R C v) • A j := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [map_add, hv, hw, add_smul, smul_add]
  | single i r =>
      simp only [Finsupp.linearCombination_single]
      calc
        C j • (r • A i) = r • (C j • A i) := by
          simp [smul_smul, mul_comm]
        _ = r • (C i • A j) := congrArg (fun x : M => r • x) (h i j)
        _ = (r • C i) • A j := by simp [smul_smul]

lemma lincomb_smul_eq_zero {ι : Type u} (C : ι → R) (z : M)
    (hz : ∀ i, C i • z = 0) (v : ι →₀ R) :
    Finsupp.linearCombination R C v • z = 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [map_add, hv, hw, add_smul]
  | single i r =>
      simp only [Finsupp.linearCombination_single]
      change (r * C i) • z = 0
      rw [mul_smul, hz i, smul_zero]

variable {I : Type u} [AddCommGroup I] [Module R I] [Module.Injective R I]
variable {ι : Type u} [Finite ι]

lemma exists_global_of_finite_fraction_data
    (a : ι → I) (b : ι → R)
    (hcross : ∀ i j, b j • a i = b i • a j) :
    ∃ m : ℕ, ∃ y : I, ∀ i,
      b i ^ (m + 1) • y = b i ^ m • a i := by
  let F : Submodule R I := Submodule.span R (Set.range a)
  have hFfg : F.FG := Submodule.fg_span (Set.finite_range a)
  letI : Module.Finite R F := Module.Finite.of_fg hFfg
  let aF (i : ι) : F := ⟨a i, Submodule.subset_span (Set.mem_range_self i)⟩
  let J : Ideal R := Ideal.span (Set.range b)
  obtain ⟨k, m, hle, hdisj⟩ := stabilized_torsion_disjoint (M := F) J
  let H : Submodule R F :=
    torsionBySet R F (((J ^ k : Ideal R) : Set R))
  let F' : Submodule R F := J ^ m • (⊤ : Submodule R F)
  let C (i : ι) : R := b i ^ (m + 1)
  have hbi (i : ι) : b i ∈ J :=
    Ideal.subset_span (Set.mem_range_self i)
  have hAi_mem (i : ι) : b i ^ m • aF i ∈ F' := by
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (hbi i) m) (by simp)
  let A (i : ι) : F' := ⟨b i ^ m • aF i, hAi_mem i⟩
  have hAC : ∀ i j, C j • A i = C i • A j := by
    intro i j
    apply Subtype.ext
    apply Subtype.ext
    change b j ^ (m + 1) • (b i ^ m • a i) =
      b i ^ (m + 1) • (b j ^ m • a j)
    calc
      b j ^ (m + 1) • (b i ^ m • a i) =
          (b i ^ m * b j ^ m) • (b j • a i) := by
            simp only [pow_succ, smul_smul]
            congr 1
            ring
      _ = (b i ^ m * b j ^ m) • (b i • a j) :=
        congrArg (fun x : I => (b i ^ m * b j ^ m) • x) (hcross i j)
      _ = b i ^ (m + 1) • (b j ^ m • a j) := by
        simp only [pow_succ, smul_smul]
        congr 1
        ring
  let B : (ι →₀ R) →ₗ[R] R := Finsupp.linearCombination R C
  let D : (ι →₀ R) →ₗ[R] F' := Finsupp.linearCombination R A
  have hker : LinearMap.ker B ≤ LinearMap.ker D := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    let z : F' := D v
    have hCkill (j : ι) : C j • z = 0 := by
      change C j • D v = 0
      rw [show C j • D v = B v • A j from lincomb_cross A C hAC v j]
      simp [hv]
    let K : Ideal R := B.range
    have hKkill : ∀ r ∈ K, r • z = 0 := by
      intro r hr
      rw [LinearMap.mem_range] at hr
      obtain ⟨w, rfl⟩ := hr
      exact lincomb_smul_eq_zero C z hCkill w
    have hJrad : J ≤ K.radical := by
      rw [Ideal.span_le]
      rintro x ⟨i, rfl⟩
      change ∃ n : ℕ, b i ^ n ∈ K
      refine ⟨m + 1, ?_⟩
      rw [LinearMap.mem_range]
      refine ⟨Finsupp.single i 1, ?_⟩
      simp [B, C]
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJrad
      (Submodule.fg_span (Set.finite_range b))
    have hzH : z.1 ∈ H := by
      apply hle n
      rw [Submodule.mem_torsionBySet_iff]
      rintro ⟨r, hr⟩
      exact congrArg Subtype.val (hKkill r (hn hr))
    have hzF' : z.1 ∈ F' := z.2
    have hzbot : z.1 ∈ (⊥ : Submodule R F) := by
      rw [← hdisj]
      exact ⟨hzF', hzH⟩
    exact Subtype.ext ((Submodule.mem_bot R).mp hzbot)
  let DbarF' : B.range →ₗ[R] F' :=
    (Submodule.liftQ (LinearMap.ker B) D hker).comp
      (LinearMap.quotKerEquivRange B).symm.toLinearMap
  let Dbar : B.range →ₗ[R] I :=
    F.subtype.comp (F'.subtype.comp DbarF')
  obtain ⟨g, hg⟩ := Module.Baer.of_injective (R := R)
    (show Module.Injective R I from inferInstance) B.range Dbar
  let y : I := g 1
  refine ⟨m, y, fun i => ?_⟩
  have hCi : C i ∈ B.range := by
    rw [LinearMap.mem_range]
    refine ⟨Finsupp.single i 1, ?_⟩
    simp [B]
  have hDbar : Dbar ⟨C i, hCi⟩ = b i ^ m • a i := by
    have hq : (LinearMap.quotKerEquivRange B).symm ⟨C i, hCi⟩ =
        Submodule.Quotient.mk (Finsupp.single i 1) := by
      apply (LinearMap.quotKerEquivRange B).injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      simpa [B] using
        (LinearMap.quotKerEquivRange_apply_mk B (Finsupp.single i 1)).symm
    simp only [Dbar, DbarF', LinearMap.comp_apply, LinearEquiv.coe_coe, hq,
      Submodule.liftQ_apply, D, Finsupp.linearCombination_single]
    simp [A, aF]
  have hgi : g (C i) = b i ^ m • a i := by
    exact (hg (C i) hCi).trans hDbar
  calc
    b i ^ (m + 1) • y = C i • g 1 := by rfl
    _ = g (C i • 1) := (g.map_smul (C i) 1).symm
    _ = g (C i) := by simp
    _ = b i ^ m • a i := hgi


open TopCat TopologicalSpace CategoryTheory Opposite
open PrimeSpectrum (basicOpen)
open AlgebraicGeometry

local notation "Γ(" N ", " U ")" =>
  (Functor.obj (ObjectProperty.FullSubcategory.obj (structureSheafInType R N))) (Opposite.op U)

set_option backward.isDefEq.respectTransparency false in
lemma finite_normalized_fraction_cover
    (U : Opens (PrimeSpectrum.Top R)) (hU : IsCompact (U : Set (PrimeSpectrum.Top R)))
    (s : Γ(M, U)) :
    ∃ (ι : Type u) (_ : Fintype ι) (a : ι → M) (b : ι → R)
      (ibU : ∀ i, basicOpen (b i) ≤ U),
      (U ≤ ⨆ i, basicOpen (b i)) ∧ (∀ i j, b j • a i = b i • a j) ∧
        ∀ i, (structureSheafInType R M).presheaf.map (ibU i).hom.op s =
          StructureSheaf.const (a i) (b i) _ le_rfl := by
  choose g hxg igU f H using fun x : U ↦ StructureSheaf.exists_const U s x.1 x.2
  have hpairs (i j : U) : ∃ n : ℕ,
      (g i * g j) ^ n • (g i • f j) = (g i * g j) ^ n • (g j • f i) := by
    let W := basicOpen (g i * g j)
    let q := StructureSheaf.toOpenₗ R M W
    have hsec :
        StructureSheaf.const (g i • f j) (g i * g j) W le_rfl =
          StructureSheaf.const (g j • f i) (g i * g j) W le_rfl := by
      trans (structureSheafInType R M).obj.map
        (homOfLE (((PrimeSpectrum.basicOpen_mul (g i) (g j)).trans_le inf_le_right).trans
          (igU j))).op s
      · refine .trans (StructureSheaf.const_ext (R := R) (M := M)
          (f₁ := g i • f j) (g₁ := g i * g j) (f₂ := f j) (g₂ := g j)
          (U := W) (hu₁ := le_rfl)
          (hu₂ := (PrimeSpectrum.basicOpen_mul (g i) (g j)).trans_le inf_le_right)
          (by module)) ?_
        exact congrArg
          ((structureSheafInType R M).obj.map
            (homOfLE ((PrimeSpectrum.basicOpen_mul (g i) (g j)).trans_le inf_le_right)).op)
          (H j)
      · refine (congrArg
          ((structureSheafInType R M).obj.map
            (homOfLE ((PrimeSpectrum.basicOpen_mul (g i) (g j)).trans_le inf_le_left)).op)
          (H i)).symm.trans ?_
        exact StructureSheaf.const_ext (R := R) (M := M)
          (f₁ := f i) (g₁ := g i) (f₂ := g j • f i) (g₂ := g i * g j)
          (U := W)
          (hu₁ := (PrimeSpectrum.basicOpen_mul (g i) (g j)).trans_le inf_le_left)
          (hu₂ := le_rfl) (by module)
    have hq : q (g i • f j) = q (g j • f i) := by
      rw [StructureSheaf.toOpenₗ_eq_const, StructureSheaf.toOpenₗ_eq_const]
      have hd := congrArg (fun t => (g i * g j) • t) hsec
      calc
        StructureSheaf.const (g i • f j) 1 W (by simp) =
            StructureSheaf.const ((g i * g j) • (g i • f j)) (g i * g j) W le_rfl :=
          StructureSheaf.const_ext (R := R) (M := M) (by module)
        _ = StructureSheaf.const ((g i * g j) • (g j • f i)) (g i * g j) W le_rfl := by
          simpa only [StructureSheaf.smul_const] using hd
        _ = StructureSheaf.const (g j • f i) 1 W (by simp) :=
          StructureSheaf.const_ext (R := R) (M := M) (by module)
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (.powers (g i * g j)) q).mp hq
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff c.1 (g i * g j)).mp c.2
    refine ⟨n, ?_⟩
    simpa only [Submonoid.smul_def, ← hn] using hc
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun i ↦ (basicOpen (g i) : Set (PrimeSpectrum R)))
    (fun _ ↦ (basicOpen _).2) (fun x hx ↦ Set.mem_iUnion_of_mem ⟨x, hx⟩ (hxg _))
  choose n hn using hpairs
  let N := (t ×ˢ t).sup fun x ↦ n x.1 x.2
  refine ⟨t, inferInstance, fun i ↦ g i ^ N • f i, fun i ↦ (g i) ^ (N + 1),
    fun x ↦ by simpa using igU x.1, fun x hx ↦ by simpa using ht hx, fun i j ↦ ?_, fun i ↦ ?_⟩
  · dsimp
    convert_to (g i * g ↑j) ^ N • g j • f i = (g i * g ↑j) ^ N • g i • f j
    · module
    · module
    have hle : n i j ≤ N := (t ×ˢ t).le_sup
      (f := fun x ↦ n x.1 x.2) (b := ⟨_, _⟩) (by simp)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, mul_smul]
    congr 1
    exact (hn i j).symm
  · convert! congr((structureSheafInType R M).presheaf.map (homOfLE ?_).op $((H i).symm)) using 1
    · refine Subtype.ext <| funext fun x ↦ LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
      simp [Submonoid.smul_def, pow_succ', mul_smul]
    · simp


variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {I : Type u} [AddCommGroup I] [Module R I] [Module.Injective R I]

set_option backward.isDefEq.respectTransparency false in
lemma structureSheaf_toOpen_surjective
    (U : Opens (PrimeSpectrum.Top R)) :
    Function.Surjective (StructureSheaf.toOpenₗ R I U) := by
  letI : NoetherianSpace (PrimeSpectrum.Top R) := PrimeSpectrum.instNoetherianSpace R
  intro s
  obtain ⟨ι, _, a, b, ibU, hcover, hcross, hs⟩ :=
    finite_normalized_fraction_cover U (NoetherianSpace.isCompact _) s
  obtain ⟨m, y, hy⟩ := exists_global_of_finite_fraction_data a b hcross
  refine ⟨y, ?_⟩
  apply (structureSheafInType R I).eq_of_locally_eq'
    (fun i : ι ↦ basicOpen (b i)) U (fun i ↦ (ibU i).hom) hcover
      (StructureSheaf.toOpenₗ R I U y) s
  intro i
  calc
    (structureSheafInType R I).presheaf.map (ibU i).hom.op
        (StructureSheaf.toOpenₗ R I U y) =
        StructureSheaf.const y 1 (basicOpen (b i)) (by simp) := by
          rw [StructureSheaf.toOpenₗ_eq_const, StructureSheaf.res_const]
    _ = StructureSheaf.const (a i) (b i) (basicOpen (b i)) le_rfl := by
      apply Subtype.ext
      funext x
      simp only [StructureSheaf.const_apply]
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨b i ^ m, Submonoid.pow_mem _ x.2 m⟩, ?_⟩
      simpa only [Submonoid.smul_def, one_smul, smul_smul, mul_one, pow_succ] using hy i
    _ = (structureSheafInType R I).presheaf.map (ibU i).hom.op s := (hs i).symm


open scoped Pointwise

variable {A : CommRingCat.{u}} [IsNoetherianRing A]

lemma tilde_toOpen_surjective
    (I : ModuleCat.{u} A) [CategoryTheory.Injective I]
    (U : (Spec A).Opens) :
    Function.Surjective (tilde.toOpen I U).hom := by
  letI : Module.Injective A I :=
    Module.injective_module_of_injective_object A I
  exact ((tilde.modulesSpecToSheafIso I).app (op U)).toLinearEquiv.symm.surjective.comp
    (structureSheaf_toOpen_surjective U)

lemma tilde_restrict_surjective
    (I : ModuleCat.{u} A) [CategoryTheory.Injective I]
    {U V : ((Spec A).Opens)ᵒᵖ} (i : U ⟶ V) :
    Function.Surjective
      ((modulesSpecToSheaf.obj (tilde I)).presheaf.map i).hom := by
  intro y
  obtain ⟨x, hx⟩ := tilde_toOpen_surjective I V.unop y
  refine ⟨(tilde.toOpen I U.unop).hom x, ?_⟩
  have hres := tilde.toOpen_res I U.unop V.unop i.unop
  have happ := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hres) x
  exact happ.trans hx

/-- The quasicoherent sheaf associated to an injective module over a noetherian
ring is flasque. -/
theorem tilde_injective_isFlasque
    (I : ModuleCat.{u} A) [CategoryTheory.Injective I] :
    TopCat.Presheaf.IsFlasque (tilde I).val.presheaf where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).2
    exact tilde_restrict_surjective I i




variable {R : CommRingCat.{u}}

lemma localizations_comapFun_injective
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (hf : Function.Injective f.hom)
    (x : PrimeSpectrum.Top R) :
    Function.Injective (StructureSheaf.Localizations.comapFun f.hom x) := by
  intro a b hab
  induction a using LocalizedModule.induction_on with | h a s =>
  induction b using LocalizedModule.induction_on with | h b t =>
  simp only [StructureSheaf.Localizations.comapFun_mk] at hab ⊢
  rw [LocalizedModule.mk_eq] at hab ⊢
  obtain ⟨c, hc⟩ := hab
  let c' : (x.comap (RingHom.id R)).asIdeal.primeCompl :=
    ⟨c.1, by simpa only [PrimeSpectrum.comap_id] using c.2⟩
  refine ⟨c', ?_⟩
  apply hf
  simp only [Submonoid.smul_def]
  rw [map_smul, map_smul, map_smul, map_smul]
  simpa only [c', RingHom.id_apply, Submonoid.smul_def] using hc


set_option backward.isDefEq.respectTransparency false in
lemma structureSheaf_comap_id_injective
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (hf : Function.Injective f.hom)
    (U : (Spec R).Opens) :
    Function.Injective
      (StructureSheaf.comapₗ f.hom U U (by
        intro x hx
        rw [PrimeSpectrum.comap_id]
        exact hx)) := by
  intro s t hst
  apply Subtype.ext
  funext x
  apply localizations_comapFun_injective f hf x.1
  have h := congrArg (fun q => q.1 x) hst
  have hxid : x.1.comap (RingHom.id R) = x.1 :=
    congrFun PrimeSpectrum.comap_id x.1
  have hyU : x.1.comap (RingHom.id R) ∈ U := hxid.symm ▸ x.2
  let y : U := ⟨x.1.comap (RingHom.id R), hyU⟩
  have hyx : y = x := Subtype.ext hxid
  change StructureSheaf.Localizations.comapFun f.hom x.1 (s.1 y) =
    StructureSheaf.Localizations.comapFun f.hom x.1 (t.1 y) at h
  subst y
  exact h



set_option backward.isDefEq.respectTransparency.types false in
instance tilde_map_mono {M N : ModuleCat.{u} R} (f : M ⟶ N) [Mono f] :
    Mono (tilde.map f) := by
  apply Functor.mono_of_mono_map (modulesSpecToSheaf (R := R))
  apply Functor.mono_of_mono_map
    (TopCat.Sheaf.forget (ModuleCat R) (Spec R))
  rw [NatTrans.mono_iff_mono_app]
  intro V
  apply ConcreteCategory.mono_of_injective
  let U := V.unop
  intro s t h
  change ((modulesSpecToSheaf.map (tilde.map f)).hom.app V) s =
    ((modulesSpecToSheaf.map (tilde.map f)).hom.app V) t at h
  have hf : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).mp inferInstance
  have hmid :
      StructureSheaf.comapₗ f.hom U U .rfl
        ((tilde.modulesSpecToSheafIso M).hom.app V s) =
      StructureSheaf.comapₗ f.hom U U .rfl
        ((tilde.modulesSpecToSheafIso M).hom.app V t) := by
    apply (ModuleCat.mono_iff_injective
      ((tilde.modulesSpecToSheafIso N).inv.app V)).mp inferInstance
    change (((tilde.modulesSpecToSheafIso M).hom.app V ≫
      ModuleCat.ofHom (StructureSheaf.comapₗ f.hom U U .rfl) ≫
      (tilde.modulesSpecToSheafIso N).inv.app V) s) =
      (((tilde.modulesSpecToSheafIso M).hom.app V ≫
      ModuleCat.ofHom (StructureSheaf.comapₗ f.hom U U .rfl) ≫
      (tilde.modulesSpecToSheafIso N).inv.app V) t)
    change (((tilde.modulesSpecToSheafIso M).hom.app V ≫
      ModuleCat.ofHom (StructureSheaf.comapₗ f.hom V.unop V.unop .rfl) ≫
      (tilde.modulesSpecToSheafIso N).inv.app V) s) =
      (((tilde.modulesSpecToSheafIso M).hom.app V ≫
      ModuleCat.ofHom (StructureSheaf.comapₗ f.hom V.unop V.unop .rfl) ≫
      (tilde.modulesSpecToSheafIso N).inv.app V) t) at h
    exact h
  apply (ModuleCat.mono_iff_injective
    ((tilde.modulesSpecToSheafIso M).hom.app V)).mp inferInstance
  exact structureSheaf_comap_id_injective f hf U hmid



instance tilde_preservesMonomorphisms :
    (tilde.functor R).PreservesMonomorphisms where
  preserves {M N} f _ := tilde_map_mono f

instance tilde_preservesFiniteLimits :
    PreservesFiniteLimits (tilde.functor R) := by
  letI : (tilde.functor R).PreservesHomology :=
    (tilde.functor R).preservesHomology_of_preservesMonos_and_cokernels
  have h : PreservesFiniteLimits (tilde.functor R) ∧
      PreservesFiniteColimits (tilde.functor R) :=
    ((tilde.functor R).exact_tfae.out 2 3).mp
      (show (tilde.functor R).PreservesHomology from inferInstance)
  exact h.1




variable {R : CommRingCat.{u}}

lemma tilde_toOpen_top_surjective (M : ModuleCat.{u} R) :
    Function.Surjective (tilde.toOpen M ⊤).hom := by
  exact ((tilde.modulesSpecToSheafIso M).app (op (⊤ : (Spec R).Opens))).toLinearEquiv.symm.surjective.comp
    StructureSheaf.toOpenₗ_top_bijective.2

lemma tilde_map_app_top_surjective {M N : ModuleCat.{u} R}
    (f : M ⟶ N) [Epi f] :
    Function.Surjective ((tilde.map f).val.app (op (⊤ : (Spec R).Opens))) := by
  intro y
  obtain ⟨n, hn⟩ := tilde_toOpen_top_surjective N y
  obtain ⟨m, hm⟩ := (ModuleCat.epi_iff_surjective f).mp inferInstance n
  refine ⟨(tilde.toOpen M ⊤).hom m, ?_⟩
  have hnat := tilde.toOpen_map_app f (⊤ : (Spec R).Opens)
  have happ := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hnat) m
  change ((modulesSpecToSheaf.map (tilde.map f)).hom.app
    (op (⊤ : (Spec R).Opens))) ((tilde.toOpen M ⊤).hom m) = y
  have happ' :
      ((modulesSpecToSheaf.map (tilde.map f)).hom.app
        (op (⊤ : (Spec R).Opens))) ((tilde.toOpen M ⊤).hom m) =
      (tilde.toOpen N ⊤).hom (f.hom m) := by
    simpa only [ConcreteCategory.comp_apply] using happ
  exact happ'.trans (by simpa only [hm] using hn)


open CategoryTheory.Abelian

variable {R : CommRingCat.{u}} [IsNoetherianRing R]
variable [EnoughInjectives (Spec R).Modules] [HasExt.{u} (Spec R).Modules]

/-- Degree-one cohomology of a tilde module on a noetherian affine scheme vanishes. -/
theorem affine_tilde_cohomology_one (M : ModuleCat.{u} R) :
    Subsingleton (schemeModuleCohomology (Spec R) (tilde M) 1) := by
  letI : (tilde.functor R).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive (tilde.functor R)
  let ip : InjectivePresentation M :=
    Classical.choice (EnoughInjectives.presentation M)
  let S : ShortComplex (ModuleCat.{u} R) := ip.shortComplex
  let T : ShortComplex (Spec R).Modules := S.map (tilde.functor R)
  have hS : S.ShortExact := by
    dsimp [S]
    exact ip.shortExact_shortComplex
  have hT : T.ShortExact := by
    dsimp [T]
    exact hS.map_of_exact (tilde.functor R)
  letI : TopCat.Presheaf.IsFlasque T.X₂.val.presheaf := by
    dsimp [T, S]
    exact tilde_injective_isFlasque ip.J
  letI : Subsingleton (schemeModuleCohomology (Spec R) T.X₂ 1) :=
    flasque_schemeModuleCohomology_one (Spec R) T.X₂
  have htop : Function.Surjective
      (T.g.val.app (op (⊤ : (Spec R).Opens))) := by
    dsimp [T]
    exact tilde_map_app_top_surjective S.g
  have hsections : Function.Surjective (SheafOfModules.sectionsMap T.g) :=
    sectionsMap_surjective_of_top_surjective (Spec R) T.g htop
  have hzero : Function.Surjective
      (schemeModuleCohomologyMap (Spec R) T.g 0) :=
    schemeModuleCohomologyMap_zero_surjective_of_sectionsMap (Spec R) T.g hsections
  have hvan := schemeModuleCohomology_one_subsingleton_of_zero_map_surjective
    (Spec R) T hT hzero
  simpa only [T, S, ShortComplex.map_X₁, tilde.functor_obj] using hvan


/-- Degree-two cohomology of a tilde module on a noetherian affine scheme vanishes. -/
theorem affine_tilde_cohomology_two (M : ModuleCat.{u} R) :
    Subsingleton (schemeModuleCohomology (Spec R) (tilde M) 2) := by
  letI : (tilde.functor R).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive (tilde.functor R)
  let ip : InjectivePresentation M :=
    Classical.choice (EnoughInjectives.presentation M)
  let S : ShortComplex (ModuleCat.{u} R) := ip.shortComplex
  let T : ShortComplex (Spec R).Modules := S.map (tilde.functor R)
  have hS : S.ShortExact := by
    dsimp [S]
    exact ip.shortExact_shortComplex
  have hT : T.ShortExact := by
    dsimp [T]
    exact hS.map_of_exact (tilde.functor R)
  letI : TopCat.Presheaf.IsFlasque T.X₂.val.presheaf := by
    dsimp [T, S]
    exact tilde_injective_isFlasque ip.J
  letI : Subsingleton (schemeModuleCohomology (Spec R) T.X₂ 2) :=
    flasque_schemeModuleCohomology_two (Spec R) T.X₂
  letI : Subsingleton (schemeModuleCohomology (Spec R) T.X₃ 1) := by
    simpa only [T, ShortComplex.map_X₃, tilde.functor_obj] using
      affine_tilde_cohomology_one S.X₃
  have hsurj : Function.Surjective
      (schemeModuleCohomologyMap (Spec R) T.g 1) := by
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  have hvan := schemeModuleCohomology_succ_subsingleton_of_map_surjective
    (Spec R) T hT 1 hsurj
  simpa only [T, S, ShortComplex.map_X₁, tilde.functor_obj] using hvan

/-- Every positive cohomology group of a tilde module on a noetherian
affine scheme vanishes. -/
theorem affine_tilde_cohomology_succ (M : ModuleCat.{u} R) (n : ℕ) :
    Subsingleton (schemeModuleCohomology (Spec R) (tilde M) (n + 1)) := by
  induction n generalizing M with
  | zero =>
      simpa using affine_tilde_cohomology_one M
  | succ n ih =>
      letI : (tilde.functor R).PreservesZeroMorphisms :=
        Functor.preservesZeroMorphisms_of_additive (tilde.functor R)
      let ip : InjectivePresentation M :=
        Classical.choice (EnoughInjectives.presentation M)
      let S : ShortComplex (ModuleCat.{u} R) := ip.shortComplex
      let T : ShortComplex (Spec R).Modules := S.map (tilde.functor R)
      have hS : S.ShortExact := by
        dsimp [S]
        exact ip.shortExact_shortComplex
      have hT : T.ShortExact := by
        dsimp [T]
        exact hS.map_of_exact (tilde.functor R)
      letI : TopCat.Presheaf.IsFlasque T.X₂.val.presheaf := by
        dsimp [T, S]
        exact tilde_injective_isFlasque ip.J
      letI : Subsingleton
          (schemeModuleCohomology (Spec R) T.X₂ (n + 1)) :=
        flasque_schemeModuleCohomology_succ (Spec R) T.X₂ n
      letI : Subsingleton
          (schemeModuleCohomology (Spec R) T.X₃ (n + 1)) := by
        simpa only [T, ShortComplex.map_X₃, tilde.functor_obj] using
          ih S.X₃
      have hsurj : Function.Surjective
          (schemeModuleCohomologyMap (Spec R) T.g (n + 1)) := by
        intro y
        exact ⟨0, Subsingleton.elim _ _⟩
      letI : Subsingleton
          (schemeModuleCohomology (Spec R) T.X₂ ((n + 1) + 1)) :=
        flasque_schemeModuleCohomology_succ (Spec R) T.X₂ (n + 1)
      have hvan := schemeModuleCohomology_succ_subsingleton_of_map_surjective
        (Spec R) T hT (n + 1) hsurj
      simpa only [T, S, ShortComplex.map_X₁, tilde.functor_obj,
        Nat.succ_eq_add_one, add_assoc] using hvan


/-- Degree-one affine vanishing for an arbitrary quasicoherent module sheaf. -/
theorem affine_quasicoherent_cohomology_one
    (F : (Spec R).Modules) [F.IsQuasicoherent] :
    Subsingleton (schemeModuleCohomology (Spec R) F 1) := by
  letI : IsIso F.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F
  let M : ModuleCat.{u} R :=
    (modulesSpecToSheaf.obj F).presheaf.obj (op (⊤ : (Spec R).Opens))
  letI : Subsingleton (schemeModuleCohomology (Spec R) (tilde M) 1) :=
    affine_tilde_cohomology_one M
  exact schemeModuleCohomology_subsingleton_of_iso
    (Spec R) (asIso F.fromTildeΓ) 1

/-- Degree-two affine vanishing for an arbitrary quasicoherent module sheaf. -/
theorem affine_quasicoherent_cohomology_two
    (F : (Spec R).Modules) [F.IsQuasicoherent] :
    Subsingleton (schemeModuleCohomology (Spec R) F 2) := by
  letI : IsIso F.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F
  let M : ModuleCat.{u} R :=
    (modulesSpecToSheaf.obj F).presheaf.obj (op (⊤ : (Spec R).Opens))
  letI : Subsingleton (schemeModuleCohomology (Spec R) (tilde M) 2) :=
    affine_tilde_cohomology_two M
  exact schemeModuleCohomology_subsingleton_of_iso
    (Spec R) (asIso F.fromTildeΓ) 2

/-- Every positive cohomology group of a quasicoherent module on a
noetherian affine scheme vanishes. -/
theorem affine_quasicoherent_cohomology_succ
    (F : (Spec R).Modules) [F.IsQuasicoherent] (n : ℕ) :
    Subsingleton (schemeModuleCohomology (Spec R) F (n + 1)) := by
  letI : IsIso F.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent F
  let M : ModuleCat.{u} R :=
    (modulesSpecToSheaf.obj F).presheaf.obj (op (⊤ : (Spec R).Opens))
  letI : Subsingleton
      (schemeModuleCohomology (Spec R) (tilde M) (n + 1)) :=
    affine_tilde_cohomology_succ M n
  exact schemeModuleCohomology_subsingleton_of_iso
    (Spec R) (asIso F.fromTildeΓ) (n + 1)

end PfaffianDescent
