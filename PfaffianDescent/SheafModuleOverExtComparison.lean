import PfaffianDescent.SheafModuleFlasque
import PfaffianDescent.SheafModulePushforwardExact
import PfaffianDescent.ExtMapFixedSource

/-!
# Comparing Ext with cohomology on an open over-site

For an open `U` of a scheme `X`, the free module sheaf
`sectionRepresenter X.ringCatSheaf U` represents sections on `U`.  This file
compares its low-degree Ext groups on `X` with Ext from the unit module on the
over-site of `U`.

The degree-two comparison uses an injective presentation.  Restriction to the
over-site preserves short exact sequences, and a restricted injective is
flasque, hence acyclic in degree one.  No injectivity-preservation statement
for restriction is needed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopCat TopologicalSpace Opposite AlgebraicGeometry

namespace PfaffianDescent

universe z

variable {X : Scheme.{z}}

/-- Restricting a flasque scheme module to an open subscheme is flasque. -/
instance schemeModule_restrictFunctor_isFlasque (I : X.Modules)
    [TopCat.Presheaf.IsFlasque I.val.presheaf] (U : X.Opens) :
    TopCat.Presheaf.IsFlasque
      (((Scheme.Modules.restrictFunctor U.ι).obj I).val.presheaf) where
  epi {V W} i := by
    letI : TopCat.Presheaf.IsFlasque I.presheaf := by
      change TopCat.Presheaf.IsFlasque I.val.presheaf
      infer_instance
    change Epi ((I.restrict U.ι).presheaf.map i)
    rw [show i = i.unop.op by simp, Scheme.Modules.restrict_map]
    exact TopCat.Presheaf.IsFlasque.epi _

/-- Restricting a globally injective scheme module to an open over-site is
acyclic in degree one for the local unit. -/
theorem overFunctor_obj_injective_ext_one_subsingleton
    (X : Scheme.{z})
    (U : X.Opens)
    [HasExt.{z} (SheafOfModules (X.ringCatSheaf.over U))]
    (I : X.Modules) [Injective I] :
    Subsingleton
      (Ext
        (SheafOfModules.unit (X.ringCatSheaf.over U))
        ((SheafOfModules.overFunctor X.ringCatSheaf U).obj I) 1) := by
  let E := Scheme.Modules.overEquiv U
  let L : SheafOfModules (X.ringCatSheaf.over U) :=
    SheafOfModules.unit (X.ringCatSheaf.over U)
  let FI : SheafOfModules (X.ringCatSheaf.over U) :=
    (SheafOfModules.overFunctor X.ringCatSheaf U).obj I
  let IU : (U : Scheme).Modules :=
    (Scheme.Modules.restrictFunctor U.ι).obj I
  let OU : (U : Scheme).Modules :=
    SheafOfModules.unit (U : Scheme).ringCatSheaf
  letI : E.functor.IsEquivalence := E.isEquivalence_functor
  letI : E.functor.PreservesZeroMorphisms := by infer_instance
  letI : E.functor.Additive :=
    Functor.additive_of_preserves_binary_products E.functor
  letI : EnoughInjectives (SheafOfModules (X.ringCatSheaf.over U)) :=
    sheafOfModules_enoughInjectives (X.ringCatSheaf.over U)
  letI : EnoughInjectives (U : Scheme).Modules :=
    sheafOfModules_enoughInjectives (U : Scheme).ringCatSheaf
  letI : HasExt.{z} (U : Scheme).Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{z, z, z + 1}
      (U : Scheme).Modules
  letI : TopCat.Presheaf.IsFlasque I.val.presheaf :=
    injective_isFlasque_scheme X I
  letI : TopCat.Presheaf.IsFlasque IU.val.presheaf := by
    dsimp [IU]
    infer_instance
  letI : Subsingleton (Ext OU IU 1) := by
    exact flasque_schemeModuleCohomology_one (U : Scheme) IU
  change Subsingleton (Ext L FI 1)
  exact ext_subsingleton_of_exact_equivalence_of_isos
    E L FI OU IU
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf)
      ((Scheme.Modules.overFunctorEquiv U).app I) 1

universe a b

variable {C : Type a} [Category.{b} C]
variable {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{a}}

/-- Sections of a module sheaf on a category with a terminal object are its
value at that terminal object. -/
noncomputable def moduleSectionsEquivTerminal (T : C) (hT : IsTerminal T)
    (M : SheafOfModules.{a} R) :
    M.sections ≃ M.val.obj (op T) where
  toFun s := s.val _
  invFun x := M.val.sectionsMk
    (fun V => M.val.map (hT.from V.unop).op x)
    (by
      intro V W f
      rw [← M.val.map_comp_apply,
        show (hT.from V.unop).op ≫ f = (hT.from W.unop).op by
          exact congrArg Quiver.Hom.op (hT.hom_ext
            (f.unop ≫ hT.from V.unop) (hT.from W.unop))])
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro V
    exact M.val.sections_property s (hT.from V.unop).op
  right_inv x := by
    change M.val.map (hT.from T).op x = x
    rw [show (hT.from T).op = 𝟙 (op T) from
      congrArg Quiver.Hom.op (hT.hom_ext _ _)]
    simpa using ConcreteCategory.congr_hom (M.val.map_id (op T)) x

lemma moduleSectionsEquivTerminal_naturality
    (T : C) (hT : IsTerminal T)
    {M N : SheafOfModules.{a} R} (f : M ⟶ N) (s : M.sections) :
    moduleSectionsEquivTerminal T hT N (SheafOfModules.sectionsMap f s) =
      f.val.app (op T) (moduleSectionsEquivTerminal T hT M s) := rfl

universe v u w

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- In a short exact sequence, vanishing of `Ext¹` from `L` to the kernel
makes postcomposition onto the cokernel surjective on ordinary morphisms. -/
theorem hom_postcomp_surjective_of_ext_one_subsingleton
    (L : A) (S : ShortComplex A) (hS : S.ShortExact)
    [Subsingleton (Ext L S.X₁ 1)] :
    Function.Surjective (fun f : L ⟶ S.X₂ => f ≫ S.g) := by
  intro q
  let q₀ : Ext L S.X₃ 0 := Ext.mk₀ q
  have hq : q₀.comp hS.extClass rfl = 0 := Subsingleton.elim _ _
  obtain ⟨p₀, hp₀⟩ := Ext.covariant_sequence_exact₃ L hS q₀ rfl hq
  let p : L ⟶ S.X₂ := Ext.addEquiv₀ p₀
  refine ⟨p, ?_⟩
  apply (Ext.mk₀_bijective L S.X₃).injective
  calc
    Ext.mk₀ (p ≫ S.g) =
        (Ext.mk₀ p).comp (Ext.mk₀ S.g) (add_zero 0) := by
      rw [Ext.mk₀_comp_mk₀]
    _ = p₀.comp (Ext.mk₀ S.g) (add_zero 0) := by
      rw [Ext.mk₀_addEquiv₀_apply]
    _ = q₀ := hp₀
    _ = Ext.mk₀ q := rfl

/-- Generic four-term Ext consequence: surjectivity at degree `n` and
vanishing on the middle term in degree `n+1` force vanishing on the left. -/
theorem ext_succ_subsingleton_of_postcomp_surjective
    (P : A) (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ)
    (hsurj : Function.Surjective
      ((Ext.mk₀ S.g).postcomp P (add_zero n)))
    [Subsingleton (Ext P S.X₂ (n + 1))] :
    Subsingleton (Ext P S.X₁ (n + 1)) := by
  constructor
  intro x y
  suffices hzero : ∀ z : Ext P S.X₁ (n + 1), z = 0 by
    exact (hzero x).trans (hzero y).symm
  intro z
  have hz : z.comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨z₀, hz₀⟩ := Ext.covariant_sequence_exact₁
    P hS z hz (show n + 1 = n + 1 by rfl)
  obtain ⟨z₂, hz₂⟩ := hsurj z₀
  rw [← hz₀, ← hz₂]
  change (z₂.comp (Ext.mk₀ S.g) (add_zero n)).comp hS.extClass
    (show n + 1 = n + 1 by rfl) = 0
  rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

/-- If the middle term vanishes in degree `n` and the left term in degree
`n+1`, then the right term vanishes in degree `n`. -/
theorem ext_subsingleton_of_middle_and_next_left
    (P : A) (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext P S.X₂ n)]
    [Subsingleton (Ext P S.X₁ (n + 1))] :
    Subsingleton (Ext P S.X₃ n) := by
  constructor
  intro x y
  suffices hzero : ∀ z : Ext P S.X₃ n, z = 0 by
    exact (hzero x).trans (hzero y).symm
  intro z
  have hz : z.comp hS.extClass (show n + 1 = n + 1 by rfl) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨z₂, hz₂⟩ := Ext.covariant_sequence_exact₃
    P hS z (show n + 1 = n + 1 by rfl) hz
  rw [← hz₂, show z₂ = 0 by exact Subsingleton.elim _ _]
  exact Ext.zero_comp P n (Ext.mk₀ S.g) n (add_zero n)

/-- Ordinary Hom surjectivity is the degree-zero Ext surjectivity used by
`ext_succ_subsingleton_of_postcomp_surjective`. -/
theorem ext_zero_postcomp_surjective_of_hom
    (P : A) (S : ShortComplex A)
    (hsurj : Function.Surjective (fun f : P ⟶ S.X₂ => f ≫ S.g)) :
    Function.Surjective ((Ext.mk₀ S.g).postcomp P (add_zero 0)) := by
  intro q
  let fq : P ⟶ S.X₃ := Ext.addEquiv₀ q
  obtain ⟨p, hp⟩ := hsurj fq
  change p ≫ S.g = fq at hp
  refine ⟨Ext.mk₀ p, ?_⟩
  change (Ext.mk₀ p).comp (Ext.mk₀ S.g) (add_zero 0) = q
  rw [Ext.mk₀_comp_mk₀, hp, ← Ext.mk₀_addEquiv₀_apply q]

attribute [local instance] Ext.subsingleton_of_injective in
/-- For a short exact sequence with injective middle term, surjectivity on
ordinary Hom kills `Ext¹` into the left term. -/
theorem ext_one_subsingleton_of_hom_postcomp_surjective
    (P : A) (S : ShortComplex A) (hS : S.ShortExact)
    [Injective S.X₂]
    (hsurj : Function.Surjective (fun f : P ⟶ S.X₂ => f ≫ S.g)) :
    Subsingleton (Ext P S.X₁ 1) := by
  exact ext_succ_subsingleton_of_postcomp_surjective P S hS 0
    (ext_zero_postcomp_surjective_of_hom P S hsurj)

variable {X : Scheme.{z}} (U : X.Opens)

private lemma sectionRepresenterHomEquiv_postcomp
    {M N : X.Modules}
    (f : sectionRepresenter X.ringCatSheaf U ⟶ M) (g : M ⟶ N) :
    sectionRepresenterHomEquiv X.ringCatSheaf U N (f ≫ g) =
      g.val.app (op U)
        (sectionRepresenterHomEquiv X.ringCatSheaf U M f) := by
  rfl

/-- Surjectivity on morphisms from the local unit after restricting to `U`
transfers to surjectivity on morphisms from the global section representer. -/
theorem sectionRepresenter_postcomp_surjective_of_over_unit
    {M N : X.Modules} (g : M ⟶ N)
    (hsurj : Function.Surjective
      (fun f : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
          (SheafOfModules.overFunctor X.ringCatSheaf U).obj M =>
        f ≫ (SheafOfModules.overFunctor X.ringCatSheaf U).map g)) :
    Function.Surjective
      (fun f : sectionRepresenter X.ringCatSheaf U ⟶ M => f ≫ g) := by
  let F : X.Modules ⥤ SheafOfModules.{z} (X.ringCatSheaf.over U) :=
    SheafOfModules.overFunctor X.ringCatSheaf U
  let L : SheafOfModules (X.ringCatSheaf.over U) :=
    SheafOfModules.unit (X.ringCatSheaf.over U)
  let T : Over U := Over.mk (𝟙 U)
  let hT : IsTerminal T := Over.mkIdTerminal
  intro q
  let y : N.val.obj (op U) :=
    sectionRepresenterHomEquiv X.ringCatSheaf U N q
  let yLocal : (F.obj N).val.obj (op T) := y
  let qLocal : L ⟶ F.obj N :=
    (F.obj N).unitHomEquiv.symm
      ((moduleSectionsEquivTerminal T hT (F.obj N)).symm yLocal)
  obtain ⟨pLocal, hpLocal⟩ := hsurj qLocal
  let xLocal : (F.obj M).val.obj (op T) :=
    moduleSectionsEquivTerminal T hT (F.obj M)
      ((F.obj M).unitHomEquiv pLocal)
  let x : M.val.obj (op U) := xLocal
  let p : sectionRepresenter X.ringCatSheaf U ⟶ M :=
    (sectionRepresenterHomEquiv X.ringCatSheaf U M).symm x
  refine ⟨p, ?_⟩
  apply (sectionRepresenterHomEquiv X.ringCatSheaf U N).injective
  rw [sectionRepresenterHomEquiv_postcomp]
  change g.val.app (op U)
      ((sectionRepresenterHomEquiv X.ringCatSheaf U M)
        ((sectionRepresenterHomEquiv X.ringCatSheaf U M).symm x)) = y
  rw [Equiv.apply_symm_apply]
  have hpSections := congrArg (fun k => (F.obj N).unitHomEquiv k) hpLocal
  rw [SheafOfModules.unitHomEquiv_comp_apply] at hpSections
  have hpValue := congrArg
    (moduleSectionsEquivTerminal T hT (F.obj N)) hpSections
  rw [moduleSectionsEquivTerminal_naturality] at hpValue
  dsimp only [qLocal] at hpValue
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hpValue
  have hcomponent :
      ((SheafOfModules.overFunctor X.ringCatSheaf U).map g).val.app (op T) =
        g.val.app (op U) := rfl
  rw [hcomponent] at hpValue
  change g.val.app (op U) x = y
  exact hpValue

/-- Local degree-one vanishing on the over-site implies degree-one vanishing
for the global section representer. -/
private theorem sectionRepresenter_ext_one_subsingleton_of_over_aux
    [EnoughInjectives X.Modules]
    [HasExt.{z} X.Modules]
    [HasExt.{z} (SheafOfModules (X.ringCatSheaf.over U))]
    (M : X.Modules)
    [Subsingleton
      (Ext.{z}
        (SheafOfModules.unit (X.ringCatSheaf.over U))
        ((SheafOfModules.overFunctor X.ringCatSheaf U).obj M) 1)] :
    Subsingleton (Ext.{z}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 1) := by
  let F : X.Modules ⥤ SheafOfModules.{z} (X.ringCatSheaf.over U) :=
    SheafOfModules.overFunctor X.ringCatSheaf U
  letI : F.PreservesZeroMorphisms :=
    SheafOfModules.overFunctor_preservesZeroMorphisms X.ringCatSheaf U
  let L : SheafOfModules (X.ringCatSheaf.over U) :=
    SheafOfModules.unit (X.ringCatSheaf.over U)
  let I : InjectivePresentation M := Classical.arbitrary _
  let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
  have hS : S.ShortExact := by
    dsimp [S]
    exact { exact := ShortComplex.exact_cokernel I.f }
  have hSF : (S.map F).ShortExact :=
    SheafOfModules.ShortComplex.shortExact_map_overFunctor
      X.ringCatSheaf U S hS
  letI : Subsingleton (Ext.{z} L (S.map F).X₁ 1) := by
    change Subsingleton (Ext.{z} L (F.obj M) 1)
    infer_instance
  have hsurjLocal : Function.Surjective
      (fun f : L ⟶ F.obj S.X₂ => f ≫ F.map S.g) := by
    change Function.Surjective
      (fun f : L ⟶ (S.map F).X₂ => f ≫ (S.map F).g)
    exact hom_postcomp_surjective_of_ext_one_subsingleton L (S.map F) hSF
  have hsurjGlobal : Function.Surjective
      (fun f : (show X.Modules from sectionRepresenter X.ringCatSheaf U) ⟶
          S.X₂ => f ≫ S.g) := by
    apply sectionRepresenter_postcomp_surjective_of_over_unit U S.g
    simpa only [F, L, ShortComplex.map_g] using hsurjLocal
  exact ext_one_subsingleton_of_hom_postcomp_surjective
    (show X.Modules from sectionRepresenter X.ringCatSheaf U)
    S hS hsurjGlobal

/-- Local degree-one vanishing on the over-site implies degree-one vanishing
for the global section representer.  The canonical enough-injectives structure
is installed locally. -/
theorem sectionRepresenter_ext_one_subsingleton_of_over
    [HasExt.{z} X.Modules]
    [HasExt.{z} (SheafOfModules (X.ringCatSheaf.over U))]
    (M : X.Modules)
    [Subsingleton
      (Ext.{z}
        (SheafOfModules.unit (X.ringCatSheaf.over U))
        ((SheafOfModules.overFunctor X.ringCatSheaf U).obj M) 1)] :
    Subsingleton (Ext.{z}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 1) := by
  letI : EnoughInjectives X.Modules :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  exact sectionRepresenter_ext_one_subsingleton_of_over_aux U M

attribute [local instance] Ext.subsingleton_of_injective

/-- Local vanishing in degrees one and two on the over-site implies the
corresponding vanishings for the global object representing sections on `U`.
Degree two uses only degree-one acyclicity of restricted injectives. -/
private theorem sectionRepresenter_ext_one_and_two_subsingleton_of_over_aux
    [EnoughInjectives X.Modules]
    [HasExt.{z} X.Modules]
    [HasExt.{z} (SheafOfModules (X.ringCatSheaf.over U))]
    [HasExt.{z} (U : Scheme).Modules]
    (M : X.Modules)
    (h₁ : Subsingleton
      (Ext.{z}
        (SheafOfModules.unit (X.ringCatSheaf.over U))
        ((SheafOfModules.overFunctor X.ringCatSheaf U).obj M) 1))
    (h₂ : Subsingleton
      (Ext.{z}
        (SheafOfModules.unit (X.ringCatSheaf.over U))
        ((SheafOfModules.overFunctor X.ringCatSheaf U).obj M) 2)) :
    Subsingleton (Ext.{z}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 1) ∧
    Subsingleton (Ext.{z}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 2) := by
  let F : X.Modules ⥤ SheafOfModules.{z} (X.ringCatSheaf.over U) :=
    SheafOfModules.overFunctor X.ringCatSheaf U
  letI : F.PreservesZeroMorphisms :=
    SheafOfModules.overFunctor_preservesZeroMorphisms X.ringCatSheaf U
  let L : SheafOfModules.{z} (X.ringCatSheaf.over U) :=
    SheafOfModules.unit (X.ringCatSheaf.over U)
  let P : X.Modules := sectionRepresenter X.ringCatSheaf U
  letI : Subsingleton (Ext.{z} L (F.obj M) 1) := h₁
  have hGlobalOne : Subsingleton (Ext.{z} P M 1) := by
    exact sectionRepresenter_ext_one_subsingleton_of_over U M
  let I : InjectivePresentation M := Classical.arbitrary _
  let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
  have hS : S.ShortExact := by
    dsimp [S]
    exact { exact := ShortComplex.exact_cokernel I.f }
  have hSF : (S.map F).ShortExact :=
    SheafOfModules.ShortComplex.shortExact_map_overFunctor
      X.ringCatSheaf U S hS
  letI hFIone : Subsingleton (Ext.{z} L (F.obj I.J) 1) := by
    exact overFunctor_obj_injective_ext_one_subsingleton X U I.J
  letI : Subsingleton (Ext.{z} L (S.map F).X₂ 1) := by
    change Subsingleton (Ext.{z} L (F.obj I.J) 1)
    exact hFIone
  letI : Subsingleton (Ext.{z} L (S.map F).X₁ 2) := by
    change Subsingleton (Ext.{z} L (F.obj M) 2)
    exact h₂
  letI hFQone : Subsingleton (Ext.{z} L (F.obj (cokernel I.f)) 1) := by
    change Subsingleton (Ext.{z} L (S.map F).X₃ 1)
    exact ext_subsingleton_of_middle_and_next_left L (S.map F) hSF 1
  have hGlobalQone :
      Subsingleton (Ext.{z} P (cokernel I.f) 1) := by
    exact sectionRepresenter_ext_one_subsingleton_of_over U (cokernel I.f)
  letI : Subsingleton (Ext.{z} P S.X₃ 1) := by
    change Subsingleton (Ext.{z} P (cokernel I.f) 1)
    exact hGlobalQone
  have hsurjOne : Function.Surjective
      ((Ext.mk₀ S.g).postcomp P (add_zero 1)) := by
    intro q
    exact ⟨0, Subsingleton.elim _ _⟩
  letI : Subsingleton (Ext.{z} P S.X₂ 2) := by
    dsimp [S]
    exact Ext.subsingleton_of_injective P I.J 1
  have hGlobalTwo : Subsingleton (Ext.{z} P S.X₁ 2) :=
    ext_succ_subsingleton_of_postcomp_surjective P S hS 1 hsurjOne
  constructor
  · exact hGlobalOne
  · change Subsingleton (Ext.{z} P S.X₁ 2) at hGlobalTwo
    exact hGlobalTwo

/-- Low-degree comparison with the canonical enough-injectives structures
installed locally.  Callers only provide the Ext contexts in which the local
and global groups are stated. -/
theorem sectionRepresenter_ext_one_and_two_subsingleton_of_over
    [HasExt.{z} X.Modules]
    [HasExt.{z} (SheafOfModules (X.ringCatSheaf.over U))]
    (M : X.Modules)
    (h₁ : Subsingleton
      (Ext.{z}
        (SheafOfModules.unit (X.ringCatSheaf.over U))
        ((SheafOfModules.overFunctor X.ringCatSheaf U).obj M) 1))
    (h₂ : Subsingleton
      (Ext.{z}
        (SheafOfModules.unit (X.ringCatSheaf.over U))
        ((SheafOfModules.overFunctor X.ringCatSheaf U).obj M) 2)) :
    Subsingleton (Ext.{z}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 1) ∧
    Subsingleton (Ext.{z}
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) M 2) := by
  letI : EnoughInjectives X.Modules :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : EnoughInjectives (U : Scheme).Modules :=
    sheafOfModules_enoughInjectives (U : Scheme).ringCatSheaf
  letI : HasExt.{z} (U : Scheme).Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{z, z, z + 1}
      (U : Scheme).Modules
  exact sectionRepresenter_ext_one_and_two_subsingleton_of_over_aux U M h₁ h₂

end PfaffianDescent
