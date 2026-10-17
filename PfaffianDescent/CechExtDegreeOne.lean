import PfaffianDescent.CechExtDegreeTwo
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Degree-one Ext from the genuine first two exact spots of an augmented
chain. This is a categorical foundation; scheme-cover callers below must
derive exactness and local Ext from their actual constructions.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- Genuine degree-one Hom cocycles: actual maps killed by the next
differential. No chosen cohomology or comparison object is supplied. -/
def DegreeOneCocycle {C₁ C₂ Y : A} (d₂ : C₂ ⟶ C₁) :=
  (homPrecompAddMonoidHom (Y := Y) d₂).ker

/-- An actual degree-one cocycle descends to the actual image of d₁,
using exactness at C₁ and the canonical coimage/image isomorphism. -/
def degreeOneCocycleDesc
    {C₀ C₁ C₂ Y : A} (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (h₂₁ : d₂ ≫ d₁ = 0)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (z : DegreeOneCocycle d₂ (Y := Y)) :
    Abelian.image d₁ ⟶ Y :=
  (Abelian.coimageIsoImage d₁).inv ≫
    degreeTwoCocycleDesc d₁ d₂ h₂₁ hexact₁ z

theorem factorThruImage_comp_degreeOneCocycleDesc
    {C₀ C₁ C₂ Y : A} (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (h₂₁ : d₂ ≫ d₁ = 0)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (z : DegreeOneCocycle d₂ (Y := Y)) :
    Abelian.factorThruImage d₁ ≫
      degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ z = z.1 := by
  have hfac : Abelian.coimage.π d₁ ≫ (Abelian.coimageIsoImage d₁).hom =
      Abelian.factorThruImage d₁ := by
    apply (cancel_mono (Abelian.image.ι d₁)).1
    rw [Category.assoc]
    change Abelian.coimage.π d₁ ≫ Abelian.coimageImageComparison d₁ ≫
      Abelian.image.ι d₁ = Abelian.factorThruImage d₁ ≫ Abelian.image.ι d₁
    rw [Abelian.coimage_image_factorisation, Abelian.image.fac]
  dsimp only [degreeOneCocycleDesc]
  rw [← hfac]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact coimage_π_comp_degreeTwoCocycleDesc d₁ d₂ h₂₁ hexact₁ z

/-- The canonical additive descent map. Additivity is established by
cancelling the actual epimorphism onto the actual image. -/
def degreeOneCocycleDescAddHom
    {C₀ C₁ C₂ Y : A} (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (h₂₁ : d₂ ≫ d₁ = 0)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact) :
    DegreeOneCocycle d₂ (Y := Y) →+ (Abelian.image d₁ ⟶ Y) where
  toFun := degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁
  map_zero' := by
    apply (cancel_epi (Abelian.factorThruImage d₁)).1
    rw [factorThruImage_comp_degreeOneCocycleDesc, comp_zero]
    rfl
  map_add' z t := by
    apply (cancel_epi (Abelian.factorThruImage d₁)).1
    rw [factorThruImage_comp_degreeOneCocycleDesc, Preadditive.comp_add,
      factorThruImage_comp_degreeOneCocycleDesc,
      factorThruImage_comp_degreeOneCocycleDesc]
    rfl

/-- The actual short complex image(d₁) -> C₀ -> P. -/
abbrev augmentedChainDegreeOneShortComplex
    {P C₀ C₁ : A} (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀)
    (h₁₀ : d₁ ≫ epsilon = 0) : ShortComplex A :=
  ShortComplex.mk (Abelian.image.ι d₁) epsilon
    (Abelian.image_ι_comp_eq_zero h₁₀)

/-- Short exactness of the actual image sequence follows from the actual
augmentation exactness and epimorphism. -/
theorem augmentedChainDegreeOneShortComplex_shortExact
    {P C₀ C₁ : A} (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀)
    (h₁₀ : d₁ ≫ epsilon = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact) [Epi epsilon] :
    (augmentedChainDegreeOneShortComplex epsilon d₁ h₁₀).ShortExact := by
  exact ShortComplex.ShortExact.mk'
    (((ShortComplex.mk d₁ epsilon h₁₀).exact_iff_exact_image_ι).mp hexact₀)
    inferInstance inferInstance

/-- The genuine connecting map of the actual image short exact sequence,
evaluated on the descended degree-one Hom cocycle. -/
def augmentedChainDegreeOneToExtHom
    {P C₀ C₁ C₂ : A} (Y : A)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact) [Epi epsilon] :
    DegreeOneCocycle d₂ (Y := Y) →+ Ext P Y 1 where
  toFun z :=
    (augmentedChainDegreeOneShortComplex_shortExact epsilon d₁ h₁₀ hexact₀).extClass.comp
      (Ext.mk₀ (degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ z)) (by rfl)
  map_zero' := by
    have hz := (degreeOneCocycleDescAddHom (Y := Y) d₁ d₂ h₂₁ hexact₁).map_zero
    change degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ 0 = 0 at hz
    rw [hz, Ext.mk₀_zero, Ext.comp_zero]
  map_add' z t := by
    have hz := (degreeOneCocycleDescAddHom (Y := Y) d₁ d₂ h₂₁ hexact₁).map_add z t
    change degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ (z + t) =
      degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ z +
        degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ t at hz
    rw [hz, Ext.mk₀_add, Ext.comp_add]

/-- Every Ext¹ class comes from a genuine degree-one cocycle when the
actual degree-zero term is Ext¹-acyclic. This is the only acyclicity input
to the general categorical statement. -/
theorem augmentedChainDegreeOneToExt_surjective
    {P C₀ C₁ C₂ : A} (Y : A)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact) [Epi epsilon]
    [Subsingleton (Ext C₀ Y 1)] :
    Function.Surjective
      (augmentedChainDegreeOneToExtHom Y epsilon d₁ d₂ h₁₀ h₂₁ hexact₀ hexact₁) := by
  let S := augmentedChainDegreeOneShortComplex epsilon d₁ h₁₀
  let hS := augmentedChainDegreeOneShortComplex_shortExact epsilon d₁ h₁₀ hexact₀
  intro t
  have ht : (Ext.mk₀ S.g).comp t (zero_add 1) = 0 := Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₃ hS Y t ht (show 1 + 0 = 1 by rfl)
  let q : Abelian.image d₁ ⟶ Y := Ext.addEquiv₀ x
  have hz : d₂ ≫ Abelian.factorThruImage d₁ = 0 := by
    apply (cancel_mono (Abelian.image.ι d₁)).1
    simpa only [Category.assoc, Abelian.image.fac, zero_comp] using h₂₁
  let z : DegreeOneCocycle d₂ (Y := Y) :=
    ⟨Abelian.factorThruImage d₁ ≫ q, by
      change d₂ ≫ (Abelian.factorThruImage d₁ ≫ q) = 0
      rw [← Category.assoc, hz, zero_comp]⟩
  have hdesc : degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ z = q := by
    apply (cancel_epi (Abelian.factorThruImage d₁)).1
    rw [factorThruImage_comp_degreeOneCocycleDesc]
  refine ⟨z, ?_⟩
  change hS.extClass.comp
    (Ext.mk₀ (degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ z)) (show 1 + 0 = 1 by rfl) = t
  rw [hdesc]
  change hS.extClass.comp (Ext.mk₀ (Ext.addEquiv₀ x)) (show 1 + 0 = 1 by rfl) = t
  rw [Ext.mk₀_addEquiv₀_apply]
  exact hx

/-- The genuine connecting map kills precisely the actual degree-zero
Hom boundaries. This kernel statement does not require local acyclicity. -/
theorem augmentedChainDegreeOneToExt_eq_zero_iff
    {P C₀ C₁ C₂ : A} (Y : A)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact) [Epi epsilon]
    (z : DegreeOneCocycle d₂ (Y := Y)) :
    augmentedChainDegreeOneToExtHom Y epsilon d₁ d₂ h₁₀ h₂₁ hexact₀ hexact₁ z = 0 ↔
      ∃ q : C₀ ⟶ Y, d₁ ≫ q = z.1 := by
  let S := augmentedChainDegreeOneShortComplex epsilon d₁ h₁₀
  let hS := augmentedChainDegreeOneShortComplex_shortExact epsilon d₁ h₁₀ hexact₀
  let f := degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ z
  constructor
  · intro hz
    change hS.extClass.comp (Ext.mk₀ f) (show 1 + 0 = 1 by rfl) = 0 at hz
    obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₁
      hS Y (Ext.mk₀ f) (show 1 + 0 = 1 by rfl) hz
    let q : C₀ ⟶ Y := Ext.addEquiv₀ x
    have hq : Abelian.image.ι d₁ ≫ q = f := by
      apply (Ext.mk₀_bijective _ _).injective
      rw [← Ext.mk₀_addEquiv₀_apply x] at hx
      change (Ext.mk₀ (Abelian.image.ι d₁)).comp (Ext.mk₀ q) (zero_add 0) =
        Ext.mk₀ f at hx
      simpa only [Ext.mk₀_comp_mk₀] using hx
    refine ⟨q, ?_⟩
    rw [← Abelian.image.fac d₁, Category.assoc, hq]
    exact factorThruImage_comp_degreeOneCocycleDesc d₁ d₂ h₂₁ hexact₁ z
  · rintro ⟨q, hq⟩
    have hf : f = Abelian.image.ι d₁ ≫ q := by
      apply (cancel_epi (Abelian.factorThruImage d₁)).1
      dsimp only [f]
      rw [factorThruImage_comp_degreeOneCocycleDesc, ← Category.assoc,
        Abelian.image.fac, hq]
    change hS.extClass.comp (Ext.mk₀ f) (show 1 + 0 = 1 by rfl) = 0
    rw [hf, ← Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (Ext.mk₀ q)

/-- The genuine quotient of actual degree-one cocycles by the kernel of
the actual connecting map computes Ext¹ under local degree-zero acyclicity.
The preceding theorem identifies that kernel with actual Hom boundaries. -/
def augmentedChainDegreeOneQuotientEquivExt
    {P C₀ C₁ C₂ : A} (Y : A)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact) [Epi epsilon]
    [Subsingleton (Ext C₀ Y 1)] :
    DegreeOneCocycle d₂ (Y := Y) ⧸
        (augmentedChainDegreeOneToExtHom Y epsilon d₁ d₂ h₁₀ h₂₁ hexact₀ hexact₁).ker ≃+
      Ext P Y 1 :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (augmentedChainDegreeOneToExtHom Y epsilon d₁ d₂ h₁₀ h₂₁ hexact₀ hexact₁)
    (augmentedChainDegreeOneToExt_surjective Y epsilon d₁ d₂ h₁₀ h₂₁ hexact₀ hexact₁)

end PfaffianDescent
