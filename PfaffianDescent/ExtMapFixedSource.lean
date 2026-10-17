import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Ext comparison from a fixed source

Mathlib proves that a fully faithful exact functor preserving injectives is
bijective on all Ext groups.  For a sheaf supported at one closed point, the
stalk functor is not globally fully faithful, but only the maps whose source
is that supported sheaf matter.  This file records the corresponding fixed
source dimension-shifting theorem.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀
  Ext.mapExactFunctor_extClass

/-- The derived adjunction map from `Ext X (G Y)` to `Ext (F X) Y`.
It is obtained by applying the exact functor `F` and then composing with the
adjunction counit. -/
noncomputable def adjunctionExtAddHom
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasExt.{w} C] [HasExt.{w'} D]
    (X : C) (Y : D) (n : ℕ) :
    Ext X (G.obj Y) n →+ Ext (F.obj X) Y n :=
  ((Ext.mk₀ (adj.counit.app Y)).postcomp (F.obj X) (add_zero n)).comp
    (F.mapExtAddHom X (G.obj Y) n)

attribute [local instance] Ext.subsingleton_of_injective in
set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- An exact adjunction whose right adjoint preserves injectives induces the
expected bijection `Ext X (G Y) ≃ Ext (F X) Y` in every degree. -/
theorem adjunctionExtAddHom_bijective
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives D] [G.PreservesInjectiveObjects]
    (X : C) (Y : D) (n : ℕ) :
    Function.Bijective (adjunctionExtAddHom F G adj X Y n) := by
  induction n generalizing Y with
  | zero =>
      let e : Ext X (G.obj Y) 0 ≃ Ext (F.obj X) Y 0 :=
        Ext.homEquiv₀.trans
          ((adj.homEquiv X Y).symm.trans Ext.homEquiv₀.symm)
      have heq : (adjunctionExtAddHom F G adj X Y 0 :
          Ext X (G.obj Y) 0 → Ext (F.obj X) Y 0) = e := by
        funext z
        apply Ext.homEquiv₀.injective
        simp [adjunctionExtAddHom, Ext.mapExactFunctor₀, e,
          Adjunction.homEquiv_counit]
      rw [heq]
      exact e.bijective
  | succ n hn =>
      let I : InjectivePresentation Y := Classical.arbitrary _
      let S := ShortComplex.mk _ _ (cokernel.condition I.f)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
      have hSG : (S.map G).ShortExact := hS.map G
      have : Injective (S.map G).X₂ :=
        Functor.PreservesInjectiveObjects.injective_obj I.injective
      exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
        (adjunctionExtAddHom F G adj X S.X₂ n)
        (adjunctionExtAddHom F G adj X S.X₃ n)
        (adjunctionExtAddHom F G adj X S.X₁ (n + 1))
        (by
          apply AddMonoidHom.ext
          intro z
          dsimp [adjunctionExtAddHom]
          simp only [Ext.bilinearComp_apply_apply]
          change
            ((z.mapExactFunctor F).comp
                (Ext.mk₀ (adj.counit.app S.X₂)) (add_zero n)).comp
              (Ext.mk₀ S.g) (add_zero n) =
            ((z.comp (Ext.mk₀ (G.map S.g)) (add_zero n)).mapExactFunctor F).comp
              (Ext.mk₀ (adj.counit.app S.X₃)) (add_zero n)
          rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
            Ext.comp_assoc_of_third_deg_zero,
            Ext.comp_assoc_of_third_deg_zero]
          rw [Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
          have hc := adj.counit.naturality S.g
          change F.map (G.map S.g) ≫ adj.counit.app S.X₃ =
            adj.counit.app S.X₂ ≫ S.g at hc
          rw [hc])
        (by
          apply AddMonoidHom.ext
          intro z
          dsimp [adjunctionExtAddHom]
          simp only [Ext.bilinearComp_apply_apply]
          change
            ((z.mapExactFunctor F).comp
                (Ext.mk₀ (adj.counit.app S.X₃)) (add_zero n)).comp
              hS.extClass rfl =
            ((z.comp hSG.extClass rfl).mapExactFunctor F).comp
              (Ext.mk₀ (adj.counit.app S.X₁)) (add_zero (n + 1))
          rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
            Ext.comp_assoc, Ext.comp_assoc]
          have hc := ShortComplex.ShortExact.extClass_naturality
            (hSG.map_of_exact F) hS (S.mapNatTrans adj.counit)
          change
            (hSG.map_of_exact F).extClass.comp
                (Ext.mk₀ (adj.counit.app S.X₁)) (add_zero 1) =
              (Ext.mk₀ (adj.counit.app S.X₃)).comp hS.extClass
                (zero_add 1) at hc
          rw [← hc]
          all_goals omega)
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (Ext.covariant_sequence_exact₃' X hSG n (n + 1) rfl))
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (Ext.covariant_sequence_exact₃' (F.obj X) hS n (n + 1) rfl))
        (hn S.X₂).surjective (hn S.X₃)
        (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hSG x₁ (by subsingleton) rfl)
        (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ hS y₁ (by subsingleton) rfl)

/-- The derived Ext adjunction as an additive equivalence. -/
noncomputable def adjunctionExtAddEquiv
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives D] [G.PreservesInjectiveObjects]
    (X : C) (Y : D) (n : ℕ) :
    Ext.{w} X (G.obj Y) n ≃+ Ext.{w'} (F.obj X) Y n :=
  AddEquiv.ofBijective (adjunctionExtAddHom F G adj X Y n)
    (adjunctionExtAddHom_bijective F G adj X Y n)

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀ in
/-- Naturality of the derived Ext adjunction in its contravariant source. -/
theorem adjunctionExtAddEquiv_precomp
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives D] [G.PreservesInjectiveObjects]
    {X' X : C} (f : X' ⟶ X) (Y : D) (n : ℕ)
    (z : Ext.{w} X (G.obj Y) n) :
    adjunctionExtAddEquiv F G adj X' Y n
        ((Ext.mk₀ f).comp z (zero_add n)) =
      (Ext.mk₀ (F.map f)).comp
        (adjunctionExtAddEquiv F G adj X Y n z) (zero_add n) := by
  change ((((Ext.mk₀ f).comp z (zero_add n)).mapExactFunctor F).comp
      (Ext.mk₀ (adj.counit.app Y)) (add_zero n)) =
    (Ext.mk₀ (F.map f)).comp
      ((z.mapExactFunctor F).comp (Ext.mk₀ (adj.counit.app Y)) (add_zero n))
      (zero_add n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]

attribute [local instance] Ext.subsingleton_of_injective in
/-- Degree-one Ext vanishing descends across an exact right adjoint.  This
uses only the ordinary adjunction on morphisms: the left adjoint need not be
exact, and the right adjoint need not preserve injectives.

Indeed, choose an injective presentation of `Y`.  Vanishing of
`Ext¹(X, G.obj Y)` makes the mapped presentation surjective on morphisms out
of `X`; the adjunction transports that surjectivity to morphisms out of
`F.obj X`, which kills `Ext¹(F.obj X, Y)`. -/
theorem ext_one_subsingleton_of_exact_right_adjoint
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives D]
    (X : C) (Y : D)
    [Subsingleton (Ext X (G.obj Y) 1)] :
    Subsingleton (Ext (F.obj X) Y 1) := by
  let I : InjectivePresentation Y := Classical.arbitrary _
  let S := ShortComplex.mk _ _ (cokernel.condition I.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
  have hSG : (S.map G).ShortExact := hS.map G
  let _ : Subsingleton (Ext X (S.map G).X₁ 1) := by
    change Subsingleton (Ext X (G.obj Y) 1)
    infer_instance
  have hsurjC : Function.Surjective
      ((Ext.mk₀ ((S.map G).g)).postcomp X (add_zero 0)) := by
    intro q
    have hq : q.comp hSG.extClass rfl = 0 := Subsingleton.elim _ _
    exact Ext.covariant_sequence_exact₃ X hSG q rfl hq
  have hsurjD : Function.Surjective
      ((Ext.mk₀ S.g).postcomp (F.obj X) (add_zero 0)) := by
    intro q
    let fq : F.obj X ⟶ S.X₃ := Ext.addEquiv₀ q
    let qC : X ⟶ (S.map G).X₃ := adj.homEquiv X S.X₃ fq
    obtain ⟨pCext, hp⟩ := hsurjC (Ext.mk₀ qC)
    let pC : X ⟶ (S.map G).X₂ := Ext.addEquiv₀ pCext
    let pD : F.obj X ⟶ S.X₂ := (adj.homEquiv X S.X₂).symm pC
    refine ⟨Ext.mk₀ pD, ?_⟩
    change (Ext.mk₀ pD).comp (Ext.mk₀ S.g) (add_zero 0) = q
    rw [Ext.mk₀_comp_mk₀, ← Ext.mk₀_addEquiv₀_apply q]
    apply congrArg Ext.mk₀
    apply (adj.homEquiv X S.X₃).injective
    rw [adj.homEquiv_naturality_right]
    have hpD : (adj.homEquiv X S.X₂) pD = pC := by
      exact Equiv.apply_symm_apply (adj.homEquiv X S.X₂) pC
    have hqC : (adj.homEquiv X S.X₃) fq = qC := rfl
    rw [hpD, hqC]
    change pC ≫ (S.map G).g = qC
    apply (Ext.mk₀_bijective X (S.map G).X₃).injective
    calc
      Ext.mk₀ (pC ≫ (S.map G).g) =
          (Ext.mk₀ pC).comp (Ext.mk₀ (S.map G).g) (add_zero 0) := by
        rw [Ext.mk₀_comp_mk₀]
      _ = pCext.comp (Ext.mk₀ (S.map G).g) (add_zero 0) := by
        rw [Ext.mk₀_addEquiv₀_apply]
      _ = Ext.mk₀ qC := hp
  constructor
  intro x y
  suffices hzero : ∀ z : Ext (F.obj X) Y 1, z = 0 by
    exact (hzero x).trans (hzero y).symm
  intro z
  have hz : z.comp (Ext.mk₀ S.f) (add_zero 1) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨z₀, hz₀⟩ := Ext.covariant_sequence_exact₁
    (F.obj X) hS z hz rfl
  obtain ⟨z₂, hz₂⟩ := hsurjD z₀
  rw [← hz₀, ← hz₂]
  change (z₂.comp (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass rfl = 0
  rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

attribute [local instance] Ext.subsingleton_of_injective in
/-- Fixed-source version of bijectivity of the Ext map induced by an exact
functor.  Global fullness and faithfulness are replaced by the precise
degree-zero comparison needed for morphisms out of `X`. -/
theorem mapExt_bijective_fixed_source
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives C] [F.PreservesInjectiveObjects]
    (X : C)
    (hHom : ∀ Y : C, Function.Bijective
      (fun f : X ⟶ Y ↦ F.map f))
    (Y : C) (n : ℕ) :
    Function.Bijective (F.mapExtAddHom X Y n) := by
  induction n generalizing Y with
  | zero => simpa [Ext.mapExactFunctor₀] using hHom Y
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective (S.map F).X₂ :=
      Functor.PreservesInjectiveObjects.injective_obj I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (F.mapExtAddHom X S.X₂ n) (F.mapExtAddHom X S.X₃ n)
      (F.mapExtAddHom X S.X₁ (n + 1))
      (by cat_disch) (by cat_disch)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (F.obj X) (hS.map F) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map F) y₁
        (by subsingleton) rfl)

attribute [local instance] Ext.subsingleton_of_injective in
/-- Fixed-source Ext comparison with the preservation-of-injectives
hypothesis weakened to the acyclicity that dimension shifting actually uses.
For every injective `I` of the source category, only the positive-degree
groups `Ext (F.obj X) (F.obj I)` must vanish. -/
theorem mapExt_bijective_fixed_source_of_injective_acyclic
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives C]
    (X : C)
    (hHom : ∀ Y : C, Function.Bijective
      (fun f : X ⟶ Y ↦ F.map f))
    (hAcyclic : ∀ (I : C), Injective I → ∀ n : ℕ, 0 < n →
      Subsingleton (Ext (F.obj X) (F.obj I) n))
    (Y : C) (n : ℕ) :
    Function.Bijective (F.mapExtAddHom X Y n) := by
  induction n generalizing Y with
  | zero => simpa [Ext.mapExactFunctor₀] using hHom Y
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    letI : Subsingleton (Ext (F.obj X) (S.map F).X₂ (n + 1)) := by
      change Subsingleton (Ext (F.obj X) (F.obj S.X₂) (n + 1))
      exact hAcyclic S.X₂ I.injective (n + 1) (by omega)
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (F.mapExtAddHom X S.X₂ n) (F.mapExtAddHom X S.X₃ n)
      (F.mapExtAddHom X S.X₁ (n + 1))
      (by cat_disch) (by cat_disch)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (F.obj X) (hS.map F) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map F) y₁
        (by subsingleton) rfl)

attribute [local instance] Ext.subsingleton_of_injective in
/-- Injectivity needs one degree less acyclicity than bijectivity.  In the
successor step, the first vertical map in the four-lemma diagram is
surjective because it is the degree-zero Hom comparison, or because its
target `Ext` group is zero in positive degree.  In particular, injectivity in
degree two only needs degree-one acyclicity of images of injectives. -/
theorem mapExt_injective_fixed_source_of_injective_acyclic
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives C]
    (X : C)
    (hHom : ∀ Y : C, Function.Bijective
      (fun f : X ⟶ Y ↦ F.map f))
    (hAcyclic : ∀ (I : C), Injective I → ∀ n : ℕ, 0 < n →
      Subsingleton (Ext (F.obj X) (F.obj I) n))
    (Y : C) (n : ℕ) :
    Function.Injective (F.mapExtAddHom X Y n) := by
  induction n generalizing Y with
  | zero => simpa [Ext.mapExactFunctor₀] using (hHom Y).injective
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    apply AddMonoidHom.injective_of_surjective_of_injective_of_right_exact _ _ _ _
      (F.mapExtAddHom X S.X₂ n) (F.mapExtAddHom X S.X₃ n)
      (F.mapExtAddHom X S.X₁ (n + 1))
      (by cat_disch) (by cat_disch)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (F.obj X) (hS.map F) n (n + 1) rfl))
    · rcases n with _ | n
      · simpa [Ext.mapExactFunctor₀] using (hHom S.X₂).surjective
      · have hsub : Subsingleton (Ext (F.obj X) (F.obj S.X₂) (n + 1)) :=
          hAcyclic S.X₂ I.injective (n + 1) (by omega)
        intro y
        exact ⟨0, hsub.elim _ _⟩
    · exact hn _
    · exact fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁
        (by subsingleton) rfl

attribute [local instance] Ext.subsingleton_of_injective in
/-- Bounded form of the fixed-source injectivity theorem.  To compare Ext in
degree `n`, it is enough to know acyclicity of images of injectives in the
strictly smaller positive degrees. -/
theorem mapExt_injective_fixed_source_of_injective_acyclic_below
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives C]
    (X : C)
    (hHomInjective : ∀ Y : C, Function.Injective
      (fun f : X ⟶ Y ↦ F.map f))
    (hHomSurjectiveOnInjectives : ∀ (I : C), Injective I →
      Function.Surjective (fun f : X ⟶ I ↦ F.map f))
    (Y : C) (n : ℕ)
    (hAcyclic : ∀ (I : C), Injective I → ∀ k : ℕ, 0 < k → k < n →
      Subsingleton (Ext (F.obj X) (F.obj I) k)) :
    Function.Injective (F.mapExtAddHom X Y n) := by
  induction n generalizing Y with
  | zero => simpa [Ext.mapExactFunctor₀] using hHomInjective Y
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hi₁ : Function.Surjective (F.mapExtAddHom X S.X₂ n) := by
      rcases n with _ | n
      · simpa [Ext.mapExactFunctor₀] using
          hHomSurjectiveOnInjectives S.X₂ I.injective
      · have hsub : Subsingleton (Ext (F.obj X) (F.obj S.X₂) (n + 1)) :=
          hAcyclic S.X₂ I.injective (n + 1) (by omega) (by omega)
        intro y
        exact ⟨0, hsub.elim _ _⟩
    have hi₂ : Function.Injective (F.mapExtAddHom X S.X₃ n) := by
      apply hn
      intro J hJ k hk hkn
      exact hAcyclic J hJ k hk (by omega)
    exact AddMonoidHom.injective_of_surjective_of_injective_of_right_exact _ _ _ _
      (F.mapExtAddHom X S.X₂ n) (F.mapExtAddHom X S.X₃ n)
      (F.mapExtAddHom X S.X₁ (n + 1))
      (by
        clear hi₁ hi₂ hAcyclic hn
        cat_disch)
      (by
        clear hi₁ hi₂ hAcyclic hn
        cat_disch)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (F.obj X) (hS.map F) n (n + 1) rfl))
      hi₁ hi₂
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁
        (by subsingleton) rfl)

/-- Degree-two fixed-source comparison in its minimal dimension-shifting
form: besides the degree-zero Hom comparison, only `Ext¹`-acyclicity of the
images of injectives is required. -/
theorem mapExt_two_injective_fixed_source_of_injective_ext_one_subsingleton
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives C]
    (X : C)
    (hHomInjective : ∀ Y : C, Function.Injective
      (fun f : X ⟶ Y ↦ F.map f))
    (hHomSurjectiveOnInjectives : ∀ (I : C), Injective I →
      Function.Surjective (fun f : X ⟶ I ↦ F.map f))
    (hExtOne : ∀ (I : C), Injective I →
      Subsingleton (Ext (F.obj X) (F.obj I) 1))
    (Y : C) :
    Function.Injective (F.mapExtAddHom X Y 2) := by
  apply mapExt_injective_fixed_source_of_injective_acyclic_below
    F X hHomInjective hHomSurjectiveOnInjectives Y 2
  intro I hI k hk hkTwo
  have hkOne : k = 1 := by omega
  subst k
  exact hExtOne I hI

attribute [local instance] Ext.subsingleton_of_injective in
/-- A fixed injective presentation of `Y` gives injectivity in degree one.
Only Hom-surjectivity into the chosen injective object and Hom-injectivity
into its cokernel are used. -/
theorem mapExt_one_injective_fixed_source_of_presentation
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasExt.{w} C] [HasExt.{w'} D]
    (X Y : C) (I : InjectivePresentation Y)
    (hHomSurjective : Function.Surjective
      (fun f : X ⟶ I.J ↦ F.map f))
    (hHomInjective : Function.Injective
      (fun f : X ⟶ cokernel I.f ↦ F.map f)) :
    Function.Injective (F.mapExtAddHom X Y 1) := by
  let S := ShortComplex.mk _ _ (cokernel.condition I.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
  exact AddMonoidHom.injective_of_surjective_of_injective_of_right_exact _ _ _ _
    (F.mapExtAddHom X S.X₂ 0) (F.mapExtAddHom X S.X₃ 0)
    (F.mapExtAddHom X S.X₁ 1)
    (by
      clear hHomSurjective hHomInjective
      cat_disch)
    (by
      clear hHomSurjective hHomInjective
      cat_disch)
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₃' X hS 0 1 rfl))
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₃' (F.obj X) (hS.map F) 0 1 rfl))
    (by simpa [Ext.mapExactFunctor₀] using hHomSurjective)
    (by simpa [Ext.mapExactFunctor₀] using hHomInjective)
    (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁
      (by subsingleton) rfl)

attribute [local instance] Ext.subsingleton_of_injective in
/-- Degree-two injectivity from two specified injective presentations.  This
is the exact two-step dimension-shifting interface: local `Ext¹` must vanish
only for the first chosen injective, and the Hom comparison is needed only
for the injective and cokernel in the second presentation. -/
theorem mapExt_two_injective_fixed_source_of_two_presentations
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasExt.{w} C] [HasExt.{w'} D]
    (X Y : C) (I₀ : InjectivePresentation Y)
    (I₁ : InjectivePresentation (cokernel I₀.f))
    (hExtOne : Subsingleton (Ext (F.obj X) (F.obj I₀.J) 1))
    (hHomSurjective : Function.Surjective
      (fun f : X ⟶ I₁.J ↦ F.map f))
    (hHomInjective : Function.Injective
      (fun f : X ⟶ cokernel I₁.f ↦ F.map f)) :
    Function.Injective (F.mapExtAddHom X Y 2) := by
  let S := ShortComplex.mk _ _ (cokernel.condition I₀.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I₀.f }
  have hi₁ : Function.Surjective (F.mapExtAddHom X S.X₂ 1) := by
    intro y
    exact ⟨0, hExtOne.elim _ _⟩
  have hi₂ : Function.Injective (F.mapExtAddHom X S.X₃ 1) := by
    exact mapExt_one_injective_fixed_source_of_presentation
      F X (cokernel I₀.f) I₁ hHomSurjective hHomInjective
  exact AddMonoidHom.injective_of_surjective_of_injective_of_right_exact _ _ _ _
    (F.mapExtAddHom X S.X₂ 1) (F.mapExtAddHom X S.X₃ 1)
    (F.mapExtAddHom X S.X₁ 2)
    (by
      clear hi₁ hi₂ hExtOne hHomSurjective hHomInjective
      cat_disch)
    (by
      clear hi₁ hi₂ hExtOne hHomSurjective hHomInjective
      cat_disch)
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₃' X hS 1 2 rfl))
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₃' (F.obj X) (hS.map F) 1 2 rfl))
    hi₁ hi₂
    (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁
      (by subsingleton) rfl)

/-- Subsingleton Ext groups transport contravariantly across an isomorphism
in their first variable. -/
theorem ext_subsingleton_of_iso_left [HasExt.{w} C]
    {A B Y : C} (e : A ≅ B) (n : ℕ)
    [Subsingleton (Ext A Y n)] : Subsingleton (Ext B Y n) := by
  constructor
  intro x x'
  have h : (Ext.mk₀ e.hom).comp x (zero_add n) =
      (Ext.mk₀ e.hom).comp x' (zero_add n) := Subsingleton.elim _ _
  calc
    x = (Ext.mk₀ (𝟙 B)).comp x (zero_add n) := (Ext.mk₀_id_comp x).symm
    _ = (Ext.mk₀ (e.inv ≫ e.hom)).comp x (zero_add n) := by rw [e.inv_hom_id]
    _ = (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x (zero_add n))
        (zero_add n) := by
      rw [Ext.mk₀_comp_mk₀_assoc]
    _ = (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x' (zero_add n))
        (zero_add n) := by rw [h]
    _ = (Ext.mk₀ (e.inv ≫ e.hom)).comp x' (zero_add n) := by
      rw [Ext.mk₀_comp_mk₀_assoc]
    _ = (Ext.mk₀ (𝟙 B)).comp x' (zero_add n) := by rw [e.inv_hom_id]
    _ = x' := Ext.mk₀_id_comp x'

/-- Precomposition by an isomorphism gives an additive equivalence of Ext
groups in the contravariant variable. -/
noncomputable def extPrecompIsoOfIso [HasExt.{w} C]
    {X X' Y : C} {n : ℕ} (e : X ≅ X') :
    Ext X Y n ≃+ Ext X' Y n where
  toFun a := (Ext.mk₀ e.inv).comp a (zero_add n)
  invFun b := (Ext.mk₀ e.hom).comp b (zero_add n)
  left_inv a := by
    change (Ext.mk₀ e.hom).comp
      ((Ext.mk₀ e.inv).comp a (zero_add n)) (zero_add n) = a
    rw [Ext.mk₀_comp_mk₀_assoc]
    simp
  right_inv b := by
    change (Ext.mk₀ e.inv).comp
      ((Ext.mk₀ e.hom).comp b (zero_add n)) (zero_add n) = b
    rw [Ext.mk₀_comp_mk₀_assoc]
    simp
  map_add' a b := by simp

/-- Postcomposition by an isomorphism gives an additive equivalence of Ext
groups. -/
noncomputable def extPostcompIsoOfIso [HasExt.{w} C]
    {X Y Y' : C} {n : ℕ} (e : Y ≅ Y') :
    Ext X Y n ≃+ Ext X Y' n where
  toFun a := a.comp (Ext.mk₀ e.hom) (add_zero n)
  invFun b := b.comp (Ext.mk₀ e.inv) (add_zero n)
  left_inv a := by
    change (a.comp (Ext.mk₀ e.hom) (add_zero n)).comp
      (Ext.mk₀ e.inv) (add_zero n) = a
    rw [Ext.comp_assoc_of_second_deg_zero]
    simp
  right_inv b := by
    change (b.comp (Ext.mk₀ e.inv) (add_zero n)).comp
      (Ext.mk₀ e.hom) (add_zero n) = b
    rw [Ext.comp_assoc_of_second_deg_zero]
    simp
  map_add' a b := by simp

/-- Subsingleton Ext groups transport covariantly across an isomorphism in
their second variable. -/
theorem ext_subsingleton_of_iso_right [HasExt.{w} C]
    {X Y Y' : C} (e : Y ≅ Y') (n : ℕ)
    [Subsingleton (Ext X Y n)] : Subsingleton (Ext X Y' n) :=
  (extPostcompIsoOfIso e).toEquiv.subsingleton_congr.mp inferInstance

/-- A fully faithful exact functor which preserves injectives reflects Ext
vanishing.  This is the categorical step used when an invertible twist is
removed by tensoring with its inverse. -/
theorem ext_subsingleton_of_exact_fully_faithful_functor
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful]
    [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives C] [F.PreservesInjectiveObjects]
    (X Y : C) (n : ℕ)
    [Subsingleton (Ext (F.obj X) (F.obj Y) n)] :
    Subsingleton (Ext X Y n) := by
  constructor
  intro a b
  apply (Functor.mapExt_bijective_of_preservesInjectiveObjects F X Y n).injective
  exact Subsingleton.elim _ _

/-- An additive equivalence between abelian categories reflects Ext
vanishing. -/
theorem ext_subsingleton_of_exact_equivalence
    (E : C ≌ D) [E.functor.Additive]
    [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives C]
    (X Y : C) (n : ℕ)
    [Subsingleton (Ext (E.functor.obj X) (E.functor.obj Y) n)] :
    Subsingleton (Ext X Y n) := by
  exact ext_subsingleton_of_exact_fully_faithful_functor E.functor X Y n

/-- An additive equivalence between abelian categories induces an additive
equivalence on Ext groups in every degree.  This is the data-bearing version
of `ext_subsingleton_of_exact_equivalence`: it retains the transported class,
which is needed for naturality arguments rather than only for vanishing. -/
noncomputable def extAddEquivOfExactEquivalence
    (E : C ≌ D) [E.functor.Additive]
    [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives C]
    (X Y : C) (n : ℕ) :
    Ext.{w} X Y n ≃+ Ext.{w'} (E.functor.obj X) (E.functor.obj Y) n :=
  AddEquiv.ofBijective (E.functor.mapExtAddHom X Y n)
    (Functor.mapExt_bijective_of_preservesInjectiveObjects
      E.functor X Y n)

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀ in
/-- The Ext equivalence induced by an exact categorical equivalence respects
contravariant precomposition. -/
theorem extAddEquivOfExactEquivalence_precomp
    (E : C ≌ D) [E.functor.Additive]
    [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives C]
    {M Q : C} (Y : C) (g : M ⟶ Q) (n : ℕ)
    (z : Ext.{w} Q Y n) :
    extAddEquivOfExactEquivalence E M Y n
        ((Ext.mk₀ g).comp z (zero_add n)) =
      (Ext.mk₀ (E.functor.map g)).comp
        (extAddEquivOfExactEquivalence E Q Y n z) (zero_add n) := by
  change (((Ext.mk₀ g).comp z (zero_add n)).mapExactFunctor E.functor) =
    (Ext.mk₀ (E.functor.map g)).comp (z.mapExactFunctor E.functor)
      (zero_add n)
  simp

/-- The preceding Ext equivalence followed by chosen identifications of the
two transported objects. -/
noncomputable def extAddEquivOfExactEquivalenceOfIsos
    (E : C ≌ D) [E.functor.Additive]
    [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives C]
    (X Y : C) (X' Y' : D)
    (eX : E.functor.obj X ≅ X') (eY : E.functor.obj Y ≅ Y')
    (n : ℕ) : Ext.{w} X Y n ≃+ Ext.{w'} X' Y' n :=
  (extAddEquivOfExactEquivalence E X Y n).trans
    ((extPrecompIsoOfIso eX).trans (extPostcompIsoOfIso eY))

attribute [local simp] Ext.comp_assoc_of_second_deg_zero
  Ext.mk₀_comp_mk₀_assoc in
/-- Naturality of the Ext equivalence induced by an exact equivalence after
identifying its transported objects by chosen isomorphisms.  The commutative
square is oriented so that `g'` is the concrete model of `E.map g`. -/
theorem extAddEquivOfExactEquivalenceOfIsos_precomp
    (E : C ≌ D) [E.functor.Additive]
    [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives C]
    {M Q Y : C} {M' Q' Y' : D}
    (g : M ⟶ Q) (g' : M' ⟶ Q')
    (eM : E.functor.obj M ≅ M') (eQ : E.functor.obj Q ≅ Q')
    (eY : E.functor.obj Y ≅ Y')
    (hsquare : E.functor.map g ≫ eQ.hom = eM.hom ≫ g')
    (n : ℕ) (z : Ext.{w} Q Y n) :
    extAddEquivOfExactEquivalenceOfIsos E M Y M' Y' eM eY n
        ((Ext.mk₀ g).comp z (zero_add n)) =
      (Ext.mk₀ g').comp
        (extAddEquivOfExactEquivalenceOfIsos E Q Y Q' Y' eQ eY n z)
        (zero_add n) := by
  change
    (((Ext.mk₀ eM.inv).comp
      (extAddEquivOfExactEquivalence E M Y n
        ((Ext.mk₀ g).comp z (zero_add n))) (zero_add n)).comp
        (Ext.mk₀ eY.hom) (add_zero n)) = _
  rw [extAddEquivOfExactEquivalence_precomp]
  rw [Ext.mk₀_comp_mk₀_assoc]
  have hsource : eM.inv ≫ E.functor.map g = g' ≫ eQ.inv := by
    rw [← cancel_mono eQ.hom]
    simp only [Category.assoc, hsquare]
    simp
  rw [hsource]
  change
    (((Ext.mk₀ (g' ≫ eQ.inv)).comp
      (extAddEquivOfExactEquivalence E Q Y n z) (zero_add n)).comp
        (Ext.mk₀ eY.hom) (add_zero n)) =
      (Ext.mk₀ g').comp
        (((Ext.mk₀ eQ.inv).comp
          (extAddEquivOfExactEquivalence E Q Y n z) (zero_add n)).comp
            (Ext.mk₀ eY.hom) (add_zero n)) (zero_add n)
  rw [← Ext.mk₀_comp_mk₀_assoc]
  exact Ext.comp_assoc_of_third_deg_zero _ _ _ _

set_option linter.style.haveILetI false in
/-- Ext vanishing can be pulled back through an additive equivalence after
identifying the images of both arguments.  For a line bundle `L`, take the
equivalence to be tensoring by `L⁻¹`; then `L` maps to the tensor unit and
the tensor unit maps to `L⁻¹`. -/
theorem ext_subsingleton_of_exact_equivalence_of_isos
    (E : C ≌ D) [E.functor.Additive]
    [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives C]
    (X Y : C) (X' Y' : D)
    (eX : E.functor.obj X ≅ X') (eY : E.functor.obj Y ≅ Y')
    (n : ℕ) [Subsingleton (Ext X' Y' n)] :
    Subsingleton (Ext X Y n) := by
  letI : Subsingleton (Ext (E.functor.obj X) Y' n) :=
    ext_subsingleton_of_iso_left (Y := Y') eX.symm n
  letI : Subsingleton
      (Ext (E.functor.obj X) (E.functor.obj Y) n) :=
    ext_subsingleton_of_iso_right eY.symm n
  exact ext_subsingleton_of_exact_equivalence E X Y n

/-- Postcomposition with an epimorphism is injective on degree-`n` Ext from
a fixed source when every degree-`n` class into the kernel becomes zero after
composition with the kernel inclusion.  Exactness shows that this is the
precise condition: the kernel of postcomposition is the image of that map. -/
theorem ext_postcomp_epi_injective_of_kernel_image_zero
    [HasExt.{w} C] (X : C) {Y Z : C} (f : Y ⟶ Z) [Epi f] (n : ℕ)
    (hzero : ∀ k : Ext X (kernel f) n,
      k.comp (Ext.mk₀ (kernel.ι f)) (add_zero n) = 0) :
    Function.Injective
      (fun z : Ext X Y n ↦ z.comp (Ext.mk₀ f) (add_zero n)) := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel f }
  let δ := (Ext.mk₀ f).postcomp X (add_zero n)
  change Function.Injective δ
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨k, hk⟩ := Ext.covariant_sequence_exact₂ X hS z hz
  rw [← hk]
  exact hzero k

/-- Exact characterization of injectivity after postcomposition with an
epimorphism: every class coming from the kernel must die after the kernel
inclusion. -/
theorem ext_postcomp_epi_injective_iff_kernel_image_zero
    [HasExt.{w} C] (X : C) {Y Z : C} (f : Y ⟶ Z) [Epi f] (n : ℕ) :
    Function.Injective
      (fun z : Ext X Y n ↦ z.comp (Ext.mk₀ f) (add_zero n)) ↔
      ∀ k : Ext X (kernel f) n,
        k.comp (Ext.mk₀ (kernel.ι f)) (add_zero n) = 0 := by
  constructor
  · intro hinj k
    apply hinj
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      kernel.condition, Ext.mk₀_zero, Ext.comp_zero, Ext.zero_comp]
  · exact ext_postcomp_epi_injective_of_kernel_image_zero X f n

attribute [local instance] Ext.subsingleton_of_injective in
/-- Vanishing of degree-`n` Ext into the kernel is a convenient sufficient
condition for the exact kernel-image criterion. -/
theorem ext_postcomp_epi_injective_of_kernel_ext_subsingleton
    [HasExt.{w} C] (X : C) {Y Z : C} (f : Y ⟶ Z) [Epi f] (n : ℕ)
    [Subsingleton (Ext X (kernel f) n)] :
    Function.Injective
      (fun z : Ext X Y n ↦ z.comp (Ext.mk₀ f) (add_zero n)) := by
  apply ext_postcomp_epi_injective_of_kernel_image_zero X f n
  intro k
  rw [Subsingleton.elim k 0]
  exact Ext.zero_comp _ _ _ _ _

end PfaffianDescent
