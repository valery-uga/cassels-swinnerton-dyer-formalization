import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u v w

variable {C : Type v} [Category.{u} C] [Abelian C]

noncomputable def pullbackShortComplex
    {A : C} {S : ShortComplex C} (_hS : S.ShortExact) (a : A ⟶ S.X₃) :
    ShortComplex C :=
  ShortComplex.mk
    (pullback.lift (0 : S.X₁ ⟶ A) S.f (by simp [S.zero]))
    (pullback.fst a S.g)
    (by rw [pullback.lift_fst])

theorem pullbackShortExact
    {A : C} {S : ShortComplex C} (hS : S.ShortExact) (a : A ⟶ S.X₃) :
    (pullbackShortComplex hS a).ShortExact := by
  let _ : Mono S.f := hS.mono_f
  let _ : Epi S.g := hS.epi_g
  let i : S.X₁ ⟶ pullback a S.g :=
    pullback.lift (0 : S.X₁ ⟶ A) S.f (by simp [S.zero])
  let q : pullback a S.g ⟶ A := pullback.fst a S.g
  have hi_fst : i ≫ pullback.fst a S.g = 0 := pullback.lift_fst _ _ _
  have hi_snd : i ≫ pullback.snd a S.g = S.f := pullback.lift_snd _ _ _
  have hker : IsLimit (KernelFork.ofι i (by rw [hi_fst])) := by
    refine Fork.IsLimit.mk _ ?_ ?_ ?_
    · intro s
      exact hS.fIsKernel.lift (KernelFork.ofι (Fork.ι s ≫ pullback.snd a S.g) (by
        rw [Category.assoc, ← pullback.condition, ← Category.assoc, s.condition]
        simp))
    · intro s
      apply pullback.hom_ext
      · rw [KernelFork.ι_ofι]
        dsimp
        rw [Category.assoc, hi_fst, comp_zero]
        simp [s.condition]
      · rw [KernelFork.ι_ofι]
        dsimp
        rw [Category.assoc, hi_snd]
        change hS.fIsKernel.lift _ ≫ S.f =
          (KernelFork.ofι (s.ι ≫ pullback.snd a S.g) _).ι
        exact Fork.IsLimit.lift_ι hS.fIsKernel
    · intro s m hm
      rw [KernelFork.ι_ofι] at hm
      apply Fork.IsLimit.hom_ext hS.fIsKernel
      change m ≫ S.f = _
      calc
        m ≫ S.f = m ≫ i ≫ pullback.snd a S.g := by simp only [hi_snd]
        _ = s.ι ≫ pullback.snd a S.g := by rw [← Category.assoc, hm]
        _ = hS.fIsKernel.lift (KernelFork.ofι (s.ι ≫ pullback.snd a S.g) _) ≫ S.f := by
          change (KernelFork.ofι (s.ι ≫ pullback.snd a S.g) _).ι =
            hS.fIsKernel.lift _ ≫ S.f
          exact (Fork.IsLimit.lift_ι hS.fIsKernel).symm
  change (ShortComplex.mk i q _).ShortExact
  apply ShortComplex.ShortExact.mk'
  · apply ShortComplex.exact_of_f_is_kernel
    exact hker
  · exact mono_of_isLimit_fork hker
  · change Epi (pullback.fst a S.g)
    exact Abelian.epi_pullback_of_epi_g a S.g


noncomputable def pullbackShortComplexToOriginal
    {A : C} {S : ShortComplex C} (hS : S.ShortExact) (a : A ⟶ S.X₃) :
    pullbackShortComplex hS a ⟶ S :=
  ShortComplex.homMk (𝟙 _) (pullback.snd a S.g) a
    (by
      dsimp [pullbackShortComplex]
      simpa only [Category.id_comp] using (pullback.lift_snd (0 : S.X₁ ⟶ A) S.f _).symm)
    (by
      dsimp [pullbackShortComplex]
      exact pullback.condition.symm)

@[simp]
theorem pullbackShortExact_extClass
    {A : C} {S : ShortComplex C} (hS : S.ShortExact) (a : A ⟶ S.X₃)
    [HasExt.{w} C] :
    (pullbackShortExact hS a).extClass =
      (Ext.mk₀ a).comp hS.extClass (zero_add 1) := by
  let f := pullbackShortComplexToOriginal hS a
  have h := ShortComplex.ShortExact.extClass_naturality
    (pullbackShortExact hS a) hS f
  dsimp [pullbackShortComplex] at h ⊢
  change (pullbackShortExact hS a).extClass.comp
      (Ext.mk₀ (𝟙 (pullbackShortComplex hS a).X₁)) (add_zero 1) =
    (Ext.mk₀ a).comp hS.extClass (zero_add 1) at h
  rw [Ext.comp_mk₀_id] at h
  exact h

/-- In an abelian category with enough injectives, every degree-one Ext class is
represented by a short exact sequence. -/
theorem exists_shortExact_of_ext_one
    [EnoughInjectives C] [HasExt.{w} C] {X Y : C} (z : Ext X Y 1) :
    ∃ (E : C) (i : Y ⟶ E) (p : E ⟶ X) (hi : i ≫ p = 0)
      (hS : (ShortComplex.mk i p hi).ShortExact), hS.extClass = z := by
  let p₀ := (EnoughInjectives.presentation Y).some
  let _ : Injective p₀.J := p₀.injective
  let _ : Mono p₀.f := p₀.mono
  let B : ShortComplex C :=
    ShortComplex.mk p₀.f (cokernel.π p₀.f) (cokernel.condition p₀.f)
  have hB : B.ShortExact := by
    change (ShortComplex.mk p₀.f (cokernel.π p₀.f) _).ShortExact
    refine ShortComplex.ShortExact.mk' ?_ (by exact p₀.mono) (by infer_instance)
    apply ShortComplex.exact_of_g_is_cokernel
    exact cokernelIsCokernel p₀.f
  let _ : Injective B.X₂ := by
    change Injective p₀.J
    infer_instance
  change Ext X B.X₁ 1 at z
  have hzI : z.comp (Ext.mk₀ B.f) (add_zero 1) = 0 :=
    Ext.eq_zero_of_injective _
  obtain ⟨u, hu⟩ := Ext.covariant_sequence_exact₁ X hB z hzI
    (show 0 + 1 = 1 by rfl)
  let a : X ⟶ B.X₃ := Ext.homEquiv₀ u
  let T : ShortComplex C := pullbackShortComplex hB a
  let hT : T.ShortExact := pullbackShortExact hB a
  let i : Y ⟶ T.X₂ := T.f
  let q : T.X₂ ⟶ X := T.g
  have hi : i ≫ q = 0 := T.zero
  refine ⟨T.X₂, i, q, hi, ?_, ?_⟩
  · change T.ShortExact
    exact hT
  · change hT.extClass = z
    rw [show hT.extClass =
      (Ext.mk₀ a).comp hB.extClass (zero_add 1) by
        exact pullbackShortExact_extClass hB a]
    change (Ext.mk₀ (Ext.homEquiv₀ u)).comp hB.extClass _ = z
    rw [Ext.mk₀_homEquiv₀_apply u, hu]


end PfaffianDescent
