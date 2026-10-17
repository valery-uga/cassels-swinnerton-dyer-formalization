import PfaffianDescent.SerreExtensionFoundation
import PfaffianDescent.IdealSheafModule

/-!
# Injectivity on global sections of a twisted Serre extension

For the direct proof of Voisin's Lemma 3.3, tensoring a Serre extension by
the inverse of an effective divisor gives a short exact sequence whose left
term has no global sections. The projection from the twisted bundle to its
ideal-sheaf quotient is therefore injective on global sections. This file
proves that assertion for any short exact sequence of module sheaves.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

/-- If the left term of a short exact sequence of module sheaves has at most
one global section, the quotient projection is injective on global sections.
This is the section-level fact used to bound `h⁰(E(-D))` by
`h⁰(I_Z(3H-D))` in the direct Serre argument. -/
theorem sectionsMap_injective_of_shortExact_of_subsingleton_left
    {X : Scheme.{u}}
    (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
    (hS : S.ShortExact)
    [Subsingleton S.X₁.sections] :
    Function.Injective (SheafOfModules.sectionsMap S.g) := by
  intro s t h
  have hg : S.X₂.unitHomEquiv.symm s ≫ S.g =
      S.X₂.unitHomEquiv.symm t ≫ S.g := by
    calc
      S.X₂.unitHomEquiv.symm s ≫ S.g =
          S.X₃.unitHomEquiv.symm (SheafOfModules.sectionsMap S.g s) :=
        S.X₂.unitHomEquiv_symm_comp s S.g
      _ = S.X₃.unitHomEquiv.symm (SheafOfModules.sectionsMap S.g t) := by rw [h]
      _ = S.X₂.unitHomEquiv.symm t ≫ S.g :=
        (S.X₂.unitHomEquiv_symm_comp t S.g).symm
  let d : SheafOfModules.unit X.ringCatSheaf ⟶ S.X₂ :=
    S.X₂.unitHomEquiv.symm s - S.X₂.unitHomEquiv.symm t
  have hd : d ≫ S.g = 0 := by
    dsimp [d]
    rw [Preadditive.sub_comp, sub_eq_zero.mpr hg]
  let z : SheafOfModules.unit X.ringCatSheaf ⟶ S.X₁ :=
    hS.fIsKernel.lift (KernelFork.ofι d hd)
  have hz : z ≫ S.f = d :=
    hS.fIsKernel.fac (KernelFork.ofι d hd) WalkingParallelPair.zero
  have hz0 : z = 0 := by
    apply S.X₁.unitHomEquiv.injective
    exact Subsingleton.elim _ _
  have hd0 : d = 0 := by
    calc
      d = z ≫ S.f := hz.symm
      _ = 0 := by rw [hz0]; simp
  apply S.X₂.unitHomEquiv.symm.injective
  exact sub_eq_zero.mp hd0

/-- Vanishing of `Ext¹(𝒪_X,A)` makes `H⁰(B) → H⁰(C)` surjective for any
short exact sequence `0 → A → B → C → 0`. -/
theorem sectionsMap_surjective_of_shortExact_of_ext_one_subsingleton_left
    {X : Scheme.{u}} [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
    (hS : S.ShortExact)
    [Subsingleton (Ext.{u} (SheafOfModules.unit X.ringCatSheaf) S.X₁ 1)] :
    Function.Surjective (SheafOfModules.sectionsMap S.g) := by
  intro t
  let x₃ : Ext (SheafOfModules.unit X.ringCatSheaf) S.X₃ 0 :=
    Ext.mk₀ (S.X₃.unitHomEquiv.symm t)
  have hx₃ : x₃.comp hS.extClass (show 0 + 1 = 1 by omega) =
      (0 : Ext (SheafOfModules.unit X.ringCatSheaf) S.X₁ 1) :=
    Subsingleton.elim _ _
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃
    (SheafOfModules.unit X.ringCatSheaf) hS x₃
    (show 0 + 1 = 1 by omega) hx₃
  let s : S.X₂.sections := S.X₂.unitHomEquiv (Ext.addEquiv₀ x₂)
  refine ⟨s, ?_⟩
  apply S.X₃.unitHomEquiv.symm.injective
  calc
    S.X₃.unitHomEquiv.symm (SheafOfModules.sectionsMap S.g s) =
        S.X₂.unitHomEquiv.symm s ≫ S.g :=
      (S.X₂.unitHomEquiv_symm_comp s S.g).symm
    _ = Ext.addEquiv₀ x₂ ≫ S.g := by simp [s]
    _ = Ext.addEquiv₀
        (x₂.comp (Ext.mk₀ S.g) (show 0 + 0 = 0 by omega)) := by
      have hmap :
          x₂.comp (Ext.mk₀ S.g) (show 0 + 0 = 0 by omega) =
            Ext.mk₀ (Ext.addEquiv₀ x₂ ≫ S.g) := by
        calc
          x₂.comp (Ext.mk₀ S.g) (show 0 + 0 = 0 by omega) =
              (Ext.mk₀ (Ext.addEquiv₀ x₂)).comp (Ext.mk₀ S.g)
                (show 0 + 0 = 0 by omega) := by
            rw [Ext.mk₀_addEquiv₀_apply]
          _ = Ext.mk₀ (Ext.addEquiv₀ x₂ ≫ S.g) :=
            Ext.mk₀_comp_mk₀ _ _
      apply (Ext.mk₀_bijective _ _).injective
      calc
        Ext.mk₀ (Ext.addEquiv₀ x₂ ≫ S.g) =
            x₂.comp (Ext.mk₀ S.g) (show 0 + 0 = 0 by omega) := hmap.symm
        _ = Ext.mk₀ (Ext.addEquiv₀
            (x₂.comp (Ext.mk₀ S.g) (show 0 + 0 = 0 by omega))) := by
          rw [Ext.mk₀_addEquiv₀_apply]
    _ = Ext.addEquiv₀ x₃ := by rw [hx₂]
    _ = S.X₃.unitHomEquiv.symm t := by
      rw [show x₃ = Ext.mk₀ (S.X₃.unitHomEquiv.symm t) by rfl,
        ← Ext.addEquiv₀_symm_apply]
      exact Ext.addEquiv₀.apply_symm_apply _

/-- If both `H⁰(A)` and `H¹(A)` vanish in a short exact sequence
`0 → A → B → C → 0`, then `H⁰(B) ≃ H⁰(C)` through the actual quotient map. -/
theorem sectionsMap_bijective_of_shortExact_of_left_h0_h1_vanish
    {X : Scheme.{u}} [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
    (hS : S.ShortExact)
    [Subsingleton S.X₁.sections]
    [Subsingleton (Ext.{u} (SheafOfModules.unit X.ringCatSheaf) S.X₁ 1)] :
    Function.Bijective (SheafOfModules.sectionsMap S.g) :=
  ⟨sectionsMap_injective_of_shortExact_of_subsingleton_left S hS,
   sectionsMap_surjective_of_shortExact_of_ext_one_subsingleton_left S hS⟩

/-- If restriction of global sections through the right map of a short exact
sequence is injective, then its left sheaf has no nonzero global sections.
For `0 → O(-D) → O → O_D → 0`, this is the abstract vanishing mechanism for
an effective nonempty divisor on a surface with constant global functions. -/
theorem subsingleton_left_sections_of_shortExact_of_right_sections_injective
    {X : Scheme.{u}}
    (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
    (hS : S.ShortExact)
    (hinj : Function.Injective (SheafOfModules.sectionsMap S.g)) :
    Subsingleton S.X₁.sections := by
  letI : Mono S.f := hS.mono_f
  refine ⟨fun a b => ?_⟩
  have hzero (x : S.X₁.sections) :
      S.X₃.unitHomEquiv.symm
        (SheafOfModules.sectionsMap S.g
          (SheafOfModules.sectionsMap S.f x)) = 0 := by
    calc
      S.X₃.unitHomEquiv.symm
          (SheafOfModules.sectionsMap S.g
            (SheafOfModules.sectionsMap S.f x)) =
        S.X₂.unitHomEquiv.symm
          (SheafOfModules.sectionsMap S.f x) ≫ S.g :=
        (S.X₂.unitHomEquiv_symm_comp _ S.g).symm
      _ = (S.X₁.unitHomEquiv.symm x ≫ S.f) ≫ S.g := by
        rw [← S.X₁.unitHomEquiv_symm_comp]
      _ = S.X₁.unitHomEquiv.symm x ≫ (S.f ≫ S.g) := Category.assoc _ _ _
      _ = 0 := by rw [S.zero]; simp
  have hga : SheafOfModules.sectionsMap S.g
      (SheafOfModules.sectionsMap S.f a) =
      SheafOfModules.sectionsMap S.g
        (SheafOfModules.sectionsMap S.f b) := by
    apply S.X₃.unitHomEquiv.symm.injective
    rw [hzero a, hzero b]
  exact SerreExtensionData.sectionsMap_injective_of_mono S.f (hinj hga)

/-- An ideal sheaf has no nonzero global sections when global functions
restrict injectively to its quotient. This is the form needed for an
effective conic divisor once restriction of constants has been established. -/
theorem idealModule_sections_subsingleton_of_quotient_restriction_injective
    {X : Scheme.{u}} (I : X.IdealSheafData)
    (hinj : Function.Injective (SheafOfModules.sectionsMap
      (IdealSheafDataModule.idealModuleCokernelSequence I).g)) :
    Subsingleton (IdealSheafDataModule.idealModule I).sections := by
  exact subsingleton_left_sections_of_shortExact_of_right_sections_injective
    (IdealSheafDataModule.idealModuleCokernelSequence I)
    (IdealSheafDataModule.idealModuleCokernelSequence_shortExact I) hinj

/-- The short complex obtained by tensoring a Serre extension with a module
sheaf. The zero-morphism preservation witness is supplied explicitly. -/
noncomputable def SerreExtensionSequenceData.twistedComplex
    {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
    (e : SerreExtensionSequenceData X M) (T : X.Modules) :
    ShortComplex X.Modules := by
  exact @ShortComplex.map _ _ _ _ _ _ e.complex (schemeModuleTensorRight T)
    (Functor.preservesZeroMorphisms_of_additive (schemeModuleTensorRight T))

/-- Twisting a Serre extension by a line bundle whose local trivializations
cover the surface preserves short exactness. If the twisted left term has no
nonzero global sections, the twisted bundle sections inject into the twisted
ideal-sheaf quotient sections. -/
theorem SerreExtensionSequenceData.twistedProjection_sections_injective
    {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
    (e : SerreExtensionSequenceData X M)
    {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    {T : X.Modules}
    (eU : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (U j))))
    [Subsingleton (e.twistedComplex T).X₁.sections] :
    Function.Injective (SheafOfModules.sectionsMap
      (e.twistedComplex T).g) := by
  have htwisted : (e.twistedComplex T).ShortExact := by
    unfold SerreExtensionSequenceData.twistedComplex
    exact shortComplex_tensor_shortExact_of_coversTop_iso_unit
      e.complex e.shortExact U hU eU
  exact sectionsMap_injective_of_shortExact_of_subsingleton_left
    (e.twistedComplex T) htwisted

/-- The left-term vanishing hypothesis can be stated on the twisting line
bundle itself, since `𝒪_X ⊗ T ≅ T`. In the conic branch, `T = 𝒪_X(-C)`. -/
theorem SerreExtensionSequenceData.twistedProjection_sections_injective_of_subsingleton_twist
    {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
    (e : SerreExtensionSequenceData X M)
    {I : Type u} (U : I → X.Opens)
    (hU : (Opens.grothendieckTopology X).CoversTop U)
    {T : X.Modules}
    (eU : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (U j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (U j))))
    [Subsingleton T.sections] :
    Function.Injective (SheafOfModules.sectionsMap
      (e.twistedComplex T).g) := by
  let i : (e.twistedComplex T).X₁ ≅ T := by
    change schemeModuleTensor (SheafOfModules.unit X.ringCatSheaf) T ≅ T
    exact schemeModuleTensorUnitLeftIso T
  letI : Subsingleton (e.twistedComplex T).X₁.sections := by
    refine ⟨fun a b => ?_⟩
    have hmap : (e.twistedComplex T).X₁.unitHomEquiv.symm a ≫ i.hom =
        (e.twistedComplex T).X₁.unitHomEquiv.symm b ≫ i.hom := by
      calc
        (e.twistedComplex T).X₁.unitHomEquiv.symm a ≫ i.hom =
            T.unitHomEquiv.symm (SheafOfModules.sectionsMap i.hom a) :=
          (e.twistedComplex T).X₁.unitHomEquiv_symm_comp a i.hom
        _ = T.unitHomEquiv.symm (SheafOfModules.sectionsMap i.hom b) := by
          congr 1
          exact Subsingleton.elim _ _
        _ = (e.twistedComplex T).X₁.unitHomEquiv.symm b ≫ i.hom :=
          ((e.twistedComplex T).X₁.unitHomEquiv_symm_comp b i.hom).symm
    have h := congrArg (fun f : SheafOfModules.unit X.ringCatSheaf ⟶ T =>
      f ≫ i.inv) hmap
    have hhom : (e.twistedComplex T).X₁.unitHomEquiv.symm a =
        (e.twistedComplex T).X₁.unitHomEquiv.symm b := by
      calc
        (e.twistedComplex T).X₁.unitHomEquiv.symm a =
            ((e.twistedComplex T).X₁.unitHomEquiv.symm a ≫ i.hom) ≫ i.inv := by
          calc
            _ = (e.twistedComplex T).X₁.unitHomEquiv.symm a ≫ (𝟙 _) :=
              (Category.comp_id _).symm
            _ = (e.twistedComplex T).X₁.unitHomEquiv.symm a ≫
                (i.hom ≫ i.inv) :=
              congrArg (fun f : (e.twistedComplex T).X₁ ⟶
                (e.twistedComplex T).X₁ =>
                  (e.twistedComplex T).X₁.unitHomEquiv.symm a ≫ f)
                i.hom_inv_id.symm
            _ = _ := (Category.assoc _ _ _).symm
        _ = ((e.twistedComplex T).X₁.unitHomEquiv.symm b ≫ i.hom) ≫ i.inv := h
        _ = (e.twistedComplex T).X₁.unitHomEquiv.symm b := by
          calc
            _ = (e.twistedComplex T).X₁.unitHomEquiv.symm b ≫
                (i.hom ≫ i.inv) := Category.assoc _ _ _
            _ = (e.twistedComplex T).X₁.unitHomEquiv.symm b ≫ (𝟙 _) := by
              exact congrArg (fun f : (e.twistedComplex T).X₁ ⟶
                (e.twistedComplex T).X₁ =>
                  (e.twistedComplex T).X₁.unitHomEquiv.symm b ≫ f)
                i.hom_inv_id
            _ = _ := Category.comp_id _
    exact (e.twistedComplex T).X₁.unitHomEquiv.symm.injective hhom
  exact e.twistedProjection_sections_injective U hU eU

end PfaffianDescent
