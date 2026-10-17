import Mathlib.AlgebraicGeometry.Modules.Sheaf
import PfaffianDescent.SheafFreeCover
import PfaffianDescent.ExtOneRealization
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.GroupTheory.GroupAction.Transitive
import PfaffianDescent.SchemeModuleTensor
import PfaffianDescent.SheafModuleEnoughInjectives
import PfaffianDescent.BundleSectionZeroLocusNaturality
import PfaffianDescent.ExtMapFixedSource
import PfaffianDescent.SchemeModuleCohomology
import AllCharacteristics.IdealSheafOpenExt

/-!
# The categorical core of Voisin's Serre construction

Voisin's rank-two step starts from a short exact sequence
`0 → 𝒪_X → E → I_Z(L) → 0`.  Mathlib already provides the abelian category of
modules over a scheme's structure sheaf.  This file packages exactly the
part of that construction that is available there: a locally free middle
term together with a short exact sequence, and the left-exact consequences
on global sections.

The remaining task is genuinely geometric: constructing the nonzero local
`Ext²` class supplied by Serre duality, proving the required local vanishing,
and showing that the resulting sequence is locally free at the finite
subscheme.  This file now realizes the lifted `Ext¹` class by an actual short
exact sequence, while recording the locally free output as explicit data.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Abelian

universe u v w

/-- A subset of a transitive orbit which is stable under the group action is
either empty or the whole orbit.

In Voisin's Lemma 3.1 this is applied to the non-locally-free locus of an
extension after base change to an algebraic closure.  The geometric points of
the closed point form one Galois orbit, and the locus is Galois-stable; hence
the locus has exactly these two possibilities. -/
theorem invariant_subset_eq_empty_or_univ_of_pretransitive
    {G X : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
    (B : Set X) (hstable : ∀ (g : G) (x : X), x ∈ B → g • x ∈ B) :
    B = ∅ ∨ B = Set.univ := by
  by_cases hB : B = ∅
  · exact Or.inl hB
  · right
    obtain ⟨x, hx⟩ : ∃ x : X, x ∈ B := Set.nonempty_iff_ne_empty.mpr hB
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨g, hxy⟩ := MulAction.exists_smul_eq G x y
    rw [← hxy]
    exact hstable g x hx

/-- The non-locally-free locus in Voisin's Galois-orbit argument is empty
once a nonzero extension class injects into its local restriction space.

Here `B` is the bad locus, `e` the extension class, and `restriction` is the
map to the direct sum of the local extension spaces.  The geometric input
still needed for Lemma 3.1 is precisely that `B = univ` makes this restricted
class vanish and that the restriction map is injective. -/
theorem invariant_badLocus_eq_empty_of_pretransitive
    {G X V W : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
    [AddCommMonoid V] [AddCommMonoid W]
    (B : Set X) (hstable : ∀ (g : G) (x : X), x ∈ B → g • x ∈ B)
    (e : V) (restriction : V →+ W) (hinjective : Function.Injective restriction)
    (hne : e ≠ 0)
    (hvanishes : B = Set.univ → restriction e = 0) :
    B = ∅ := by
  obtain hB | hB := invariant_subset_eq_empty_or_univ_of_pretransitive B hstable
  · exact hB
  · exfalso
    apply hne
    apply hinjective
    rw [hvanishes hB, restriction.map_zero]

/-- A pointwise local-Ext calculation gives the global vanishing premise in
the Galois-orbit argument.  In Voisin's Lemma 3.1, `components x` is the
local component at the geometric point `x`; if every point of the orbit is
bad, each component of the connecting class vanishes. -/
theorem restriction_eq_zero_of_badLocus_eq_univ_of_pointwise_vanishing
    {X W : Type*} [AddCommMonoid W] {W' : X → Type*}
    [∀ x, AddCommMonoid (W' x)]
    (B : Set X) (w : W) (components : ∀ x, W →+ W' x)
    (hcomponents : ∀ w : W, (∀ x, components x w = 0) → w = 0)
    (hbad : ∀ x, x ∈ B → components x w = 0)
    (hB : B = Set.univ) :
    w = 0 := by
  apply hcomponents
  intro x
  exact hbad x (by rw [hB]; exact Set.mem_univ x)

/-- The pretransitive bad-locus argument in componentwise form.  This is the
precise logical shape of the local calculation in Voisin's Lemma 3.1: a bad
geometric point kills its local component, and the local components jointly
detect the global connecting class. -/
theorem invariant_badLocus_eq_empty_of_pretransitive_of_pointwise_vanishing
    {G X V W : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
    [AddCommMonoid V] [AddCommMonoid W] {W' : X → Type*}
    [∀ x, AddCommMonoid (W' x)]
    (B : Set X) (hstable : ∀ (g : G) (x : X), x ∈ B → g • x ∈ B)
    (e : V) (restriction : V →+ W) (hinjective : Function.Injective restriction)
    (hne : e ≠ 0) (components : ∀ x, W →+ W' x)
    (hcomponents : ∀ w : W, (∀ x, components x w = 0) → w = 0)
    (hbad : ∀ x, x ∈ B → components x (restriction e) = 0) :
    B = ∅ := by
  apply invariant_badLocus_eq_empty_of_pretransitive B hstable e restriction hinjective hne
  intro hB
  exact restriction_eq_zero_of_badLocus_eq_univ_of_pointwise_vanishing
    B (restriction e) components hcomponents hbad hB

/-- In a short exact sequence `0 → A → B → C → 0`, if `Ext¹(B,Y)`
vanishes, then the connecting map `Ext¹(A,Y) → Ext²(C,Y)` is injective.

This is the categorical form of the local-Ext injection in Voisin's Serre
argument: apply it to the twisted ideal sequence and `Y = O_S`. -/
theorem ext_one_connecting_injective_of_middle_ext_one_subsingleton
    {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    [Subsingleton (Ext S.X₂ Y 1)] :
    Function.Injective
      (fun x : Ext S.X₁ Y 1 ↦ hS.extClass.comp x (show 1 + 1 = 2 by omega)) := by
  let δ : Ext S.X₁ Y 1 →+ Ext S.X₃ Y 2 :=
    hS.extClass.precomp Y (show 1 + 1 = 2 by omega)
  change Function.Injective δ
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁ hS Y x
    (show 1 + 1 = 2 by omega) hx
  calc
    x = (Ext.mk₀ S.f).comp x₂ (show 0 + 1 = 1 by omega) := hx₂.symm
    _ = (Ext.mk₀ S.f).comp 0 (show 0 + 1 = 1 by omega) := by
      rw [Subsingleton.elim x₂ 0]
    _ = 0 := Ext.comp_zero _ _ _ _ _

/-- A nonzero degree-two class on the quotient of a short exact sequence
lifts to a nonzero degree-one class on its kernel when the middle degree-two
group vanishes. This is the Ext-theoretic existence step in Serre's
construction: after duality supplies a local class on the finite quotient,
cohomological vanishing on the twist yields a nonzero class on the twisted
ideal sheaf. -/
theorem exists_nonzero_ext_one_of_nonzero_ext_two_of_middle_ext_two_subsingleton
    {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    [Subsingleton (Ext S.X₂ Y 2)]
    (z : Ext S.X₃ Y 2) (hz : z ≠ 0) :
    ∃ x : Ext S.X₁ Y 1,
      x ≠ 0 ∧ hS.extClass.comp x (show 1 + 1 = 2 by omega) = z := by
  have hnext : (Ext.mk₀ S.g).comp z (zero_add 2) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₃ hS Y z hnext
    (show 1 + 1 = 2 by omega)
  refine ⟨x, ?_, hx⟩
  intro hx0
  apply hz
  rw [← hx, hx0]
  exact Ext.comp_zero _ _ _ _ _

/-- A nonzero degree-two class on the quotient lifts to a nonzero
degree-one class on the kernel as soon as its image on the middle term
vanishes.

This is the form needed for Voisin's cubic-surface application.  For
`0 ⟶ I_Z(3) ⟶ O_S(3) ⟶ O_Z(3) ⟶ 0`, the group
`Ext²(O_S(3), O_S)` need not vanish.  Serre duality instead produces a
nonzero class on `O_Z(3)` lying in the kernel of the following map. -/
theorem exists_nonzero_ext_one_of_nonzero_ext_two_of_comp_eq_zero
    {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    (z : Ext S.X₃ Y 2) (hz : z ≠ 0)
    (hnext : (Ext.mk₀ S.g).comp z (zero_add 2) = 0) :
    ∃ x : Ext S.X₁ Y 1,
      x ≠ 0 ∧ hS.extClass.comp x (show 1 + 1 = 2 by omega) = z := by
  obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₃ hS Y z hnext
    (show 1 + 1 = 2 by omega)
  refine ⟨x, ?_, hx⟩
  intro hx0
  apply hz
  rw [← hx, hx0]
  exact Ext.comp_zero _ _ _ _ _

/-- If the connecting image of an `Ext¹` class is nonzero, then the class
itself is nonzero.  This is the nonvanishing step that carries Serre duality's
local `Ext²` class into the Galois-orbit local-freeness argument. -/
theorem ext_one_ne_zero_of_extClass_comp_eq_nonzero
    {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    (z : Ext S.X₃ Y 2) (hz : z ≠ 0)
    (x : Ext S.X₁ Y 1)
    (hconnecting : hS.extClass.comp x (show 1 + 1 = 2 by omega) = z) :
    x ≠ 0 := by
  intro hx
  apply hz
  rw [← hconnecting, hx]
  exact Ext.comp_zero _ _ _ _ _

/-- The middle term of the twisted ideal sequence is canonically the twist
itself. -/
noncomputable def closedImmersionIdealTwistSequence_middleIso
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (L : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight L)] :
    (closedImmersionIdealTwistSequence i L).X₂ ≅ L :=
  schemeModuleTensorUnitLeftIso L

/-- Ext vanishing for the middle term of the twisted ideal sequence follows
from Ext vanishing for any isomorphic model of the twisting sheaf. -/
theorem closedImmersionIdealTwistSequence_middle_ext_subsingleton_of_iso
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (L L' Y : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight L)]
    [HasExt.{u} X.Modules] (e : L ≅ L') (n : ℕ)
    [Subsingleton (Ext L' Y n)] :
    Subsingleton (Ext (closedImmersionIdealTwistSequence i L).X₂ Y n) := by
  exact ext_subsingleton_of_iso_left (Y := Y)
    ((closedImmersionIdealTwistSequence_middleIso i L).trans e).symm n

/-- Remove an invertible twist from the first argument of Ext by an additive
equivalence.  In the intended application, `E` is tensoring by `T⁻¹`, `eT`
identifies `T ⊗ T⁻¹` with `𝒪_X`, and `eO` identifies
`𝒪_X ⊗ T⁻¹` with `T⁻¹`.  Thus the cohomological input can be stated as
`Extⁿ(𝒪_X, T⁻¹) = 0`, the form corresponding to `Hⁿ(X,T⁻¹)=0`. -/
theorem schemeModule_twist_ext_subsingleton_of_exact_equivalence
    {X : Scheme.{u}} (T Tinv : X.Modules)
    [HasExt.{u} X.Modules]
    (E : X.Modules ≌ X.Modules) [E.functor.Additive]
    (eT : E.functor.obj T ≅ SheafOfModules.unit X.ringCatSheaf)
    (eO : E.functor.obj (SheafOfModules.unit X.ringCatSheaf) ≅ Tinv)
    (n : ℕ)
    [Subsingleton (schemeModuleCohomology X Tinv n)] :
    Subsingleton
      (Ext.{u} (show X.Modules from T)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) n) := by
  letI : EnoughInjectives X.Modules :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  exact ext_subsingleton_of_exact_equivalence_of_isos E T
    (SheafOfModules.unit X.ringCatSheaf)
    (SheafOfModules.unit X.ringCatSheaf) Tinv eT eO n

/-- Concrete inverse-tensor form of the preceding theorem.  The two natural
isomorphisms exhibit right tensoring by `Tinv` and `T` as quasi-inverse
functors, while `eT` is the inverse-line-bundle identity
`T ⊗ Tinv ≅ 𝒪_X`.  The image of `𝒪_X` is identified with `Tinv` by the
already constructed left-unit tensor isomorphism. -/
theorem schemeModule_twist_ext_subsingleton_of_tensor_inverse
    {X : Scheme.{u}} (T Tinv : X.Modules)
    [HasExt.{u} X.Modules]
    (unitIso : 𝟭 X.Modules ≅
      schemeModuleTensorRight Tinv ⋙ schemeModuleTensorRight T)
    (counitIso : schemeModuleTensorRight T ⋙
      schemeModuleTensorRight Tinv ≅ 𝟭 X.Modules)
    (eT : schemeModuleTensor T Tinv ≅
      SheafOfModules.unit X.ringCatSheaf)
    (n : ℕ)
    [Subsingleton (schemeModuleCohomology X Tinv n)] :
    Subsingleton
      (Ext.{u} (show X.Modules from T)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) n) := by
  let E : X.Modules ≌ X.Modules :=
    schemeModuleTensorRightEquivalenceOfInverse T Tinv unitIso counitIso
  letI : E.functor.Additive := by
    change (schemeModuleTensorRight Tinv).Additive
    infer_instance
  exact schemeModule_twist_ext_subsingleton_of_exact_equivalence T Tinv E
    eT (schemeModuleTensorUnitLeftIso Tinv) n

/-- The middle Ext group in the twisted ideal sequence vanishes once the
twist is removed by its inverse-tensor equivalence and the corresponding
cohomology group `Extⁿ(𝒪_X,T⁻¹)` vanishes. -/
theorem closedImmersionIdealTwistSequence_middle_ext_subsingleton_of_inverse_twist
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T Tinv : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [HasExt.{u} X.Modules]
    (E : X.Modules ≌ X.Modules) [E.functor.Additive]
    (eT : E.functor.obj T ≅ SheafOfModules.unit X.ringCatSheaf)
    (eO : E.functor.obj (SheafOfModules.unit X.ringCatSheaf) ≅ Tinv)
    (n : ℕ)
    [Subsingleton (schemeModuleCohomology X Tinv n)] :
    Subsingleton
      (Ext.{u} (closedImmersionIdealTwistSequence i T).X₂
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) n) := by
  letI : Subsingleton
      (Ext.{u} (show X.Modules from T)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) n) :=
    schemeModule_twist_ext_subsingleton_of_exact_equivalence T Tinv E eT eO n
  exact closedImmersionIdealTwistSequence_middle_ext_subsingleton_of_iso
    i T T (SheafOfModules.unit X.ringCatSheaf) (Iso.refl T) n

/-- Concrete inverse-tensor form of the middle-term cohomology reduction.
After this theorem, the remaining input for Voisin's twist is the geometric
construction of `T⁻¹`, its tensor-inverse identities, and the single
cohomology vanishing `Extⁿ(𝒪_X,T⁻¹)=0`. -/
theorem closedImmersionIdealTwistSequence_middle_ext_subsingleton_of_tensor_inverse
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (T Tinv : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [HasExt.{u} X.Modules]
    (unitIso : 𝟭 X.Modules ≅
      schemeModuleTensorRight Tinv ⋙ schemeModuleTensorRight T)
    (counitIso : schemeModuleTensorRight T ⋙
      schemeModuleTensorRight Tinv ≅ 𝟭 X.Modules)
    (eT : schemeModuleTensor T Tinv ≅
      SheafOfModules.unit X.ringCatSheaf)
    (n : ℕ)
    [Subsingleton (schemeModuleCohomology X Tinv n)] :
    Subsingleton
      (Ext.{u} (closedImmersionIdealTwistSequence i T).X₂
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) n) := by
  letI : Subsingleton
      (Ext.{u} (show X.Modules from T)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) n) :=
    schemeModule_twist_ext_subsingleton_of_tensor_inverse T Tinv
      unitIso counitIso eT n
  exact closedImmersionIdealTwistSequence_middle_ext_subsingleton_of_iso
    i T T (SheafOfModules.unit X.ringCatSheaf) (Iso.refl T) n

/-- The nonzero Ext lift specialized to the twisted ideal sequence of a
closed finite subscheme. A nonzero local degree-two class therefore supplies
the nonzero degree-one class required before constructing Voisin's Serre
extension. -/
theorem closedImmersionIdealTwist_exists_nonzeroExtOne_of_nonzeroExtTwo
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (L : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight L)]
    [PreservesFiniteColimits (schemeModuleTensorRight L)]
    (Y : X.Modules)
    [HasExt.{u} (X.Modules)]
    [Subsingleton (Ext.{u} (closedImmersionIdealTwistSequence i L).X₂ Y 2)]
    (z : Ext.{u} (closedImmersionIdealTwistSequence i L).X₃ Y 2)
    (hz : z ≠ 0) :
    ∃ x : Ext.{u} (closedImmersionIdealTwist i L) Y 1,
      x ≠ 0 ∧
        (closedImmersionIdealTwistSequence_shortExact i L).extClass.comp x
          (show 1 + 1 = 2 by omega) = z := by
  exact exists_nonzero_ext_one_of_nonzero_ext_two_of_middle_ext_two_subsingleton
    (closedImmersionIdealTwistSequence_shortExact i L) Y z hz

/-- Kernel form of the Ext lift for the twisted ideal sequence.  Unlike the
vanishing-based convenience theorem above, this is applicable to the
degree-three twist on a cubic surface, where the middle `Ext²` group is
nonzero. -/
theorem closedImmersionIdealTwist_exists_nonzeroExtOne_of_nonzeroExtTwo_of_comp_eq_zero
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (L : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight L)]
    [PreservesFiniteColimits (schemeModuleTensorRight L)]
    (Y : X.Modules)
    [HasExt.{u} (X.Modules)]
    (z : Ext.{u} (closedImmersionIdealTwistSequence i L).X₃ Y 2)
    (hz : z ≠ 0)
    (hnext :
      (Ext.mk₀ (closedImmersionIdealTwistSequence i L).g).comp z
        (zero_add 2) = 0) :
    ∃ x : Ext.{u} (closedImmersionIdealTwist i L) Y 1,
      x ≠ 0 ∧
        (closedImmersionIdealTwistSequence_shortExact i L).extClass.comp x
          (show 1 + 1 = 2 by omega) = z := by
  exact exists_nonzero_ext_one_of_nonzero_ext_two_of_comp_eq_zero
    (closedImmersionIdealTwistSequence_shortExact i L) Y z hz hnext

/-- The same Serre-class existence result with the degree-two vanishing
stated for the ordinary twist, rather than its tensor-with-unit presentation
inside the ideal sequence. -/
theorem closedImmersionIdealTwist_exists_nonzeroExtOne_of_nonzeroExtTwo_of_ext_two_subsingleton
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (L : X.Modules)
    [PreservesFiniteLimits (schemeModuleTensorRight L)]
    [PreservesFiniteColimits (schemeModuleTensorRight L)]
    (Y : X.Modules)
    [HasExt.{u} (X.Modules)]
    [Subsingleton (Ext.{u} (show X.Modules from L) Y 2)]
    (z : Ext.{u} (closedImmersionIdealTwistSequence i L).X₃ Y 2)
    (hz : z ≠ 0) :
    ∃ x : Ext.{u} (closedImmersionIdealTwist i L) Y 1,
      x ≠ 0 ∧
        (closedImmersionIdealTwistSequence_shortExact i L).extClass.comp x
          (show 1 + 1 = 2 by omega) = z := by
  letI : Subsingleton (Ext.{u} (closedImmersionIdealTwistSequence i L).X₂ Y 2) :=
    ext_subsingleton_of_iso_left (Y := Y)
      (closedImmersionIdealTwistSequence_middleIso i L).symm 2
  exact closedImmersionIdealTwist_exists_nonzeroExtOne_of_nonzeroExtTwo i L Y z hz

/-- The local-Ext injection for the actual twisted ideal sequence of a
closed immersion.

The `Subsingleton` hypothesis is the cohomology-vanishing input on the
middle twisted structure sheaf.  Combined with a local nonvanishing
calculation, this is the injection used in Voisin's proof of local freeness. -/
theorem closedImmersionIdealTwist_connectingExtOne_injective
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (L : SheafOfModules.{u} X.ringCatSheaf)
    [PreservesFiniteLimits (schemeModuleTensorRight L)]
    [PreservesFiniteColimits (schemeModuleTensorRight L)]
    (Y : X.Modules)
    [HasExt.{u} (X.Modules)]
    [Subsingleton (Ext.{u} (closedImmersionIdealTwistSequence i L).X₂ Y 1)] :
    Function.Injective
      (fun x : Ext.{u} (closedImmersionIdealTwist i L) Y 1 ↦
        (closedImmersionIdealTwistSequence_shortExact i L).extClass.comp x
          (show 1 + 1 = 2 by omega)) := by
  exact ext_one_connecting_injective_of_middle_ext_one_subsingleton
    (closedImmersionIdealTwistSequence_shortExact i L) Y

/-- The local-Ext injection expressed using the direct middle cohomology
vanishing required in Voisin's Serre construction. -/
theorem closedImmersionIdealTwist_connectingExtOne_injective_of_ext_one_subsingleton
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (L : SheafOfModules.{u} X.ringCatSheaf)
    [PreservesFiniteLimits (schemeModuleTensorRight L)]
    [PreservesFiniteColimits (schemeModuleTensorRight L)]
    (Y : X.Modules)
    [HasExt.{u} (X.Modules)]
    [Subsingleton (Ext.{u} (show X.Modules from L) Y 1)] :
    Function.Injective
      (fun x : Ext.{u} (closedImmersionIdealTwist i L) Y 1 ↦
        (closedImmersionIdealTwistSequence_shortExact i L).extClass.comp x
          (show 1 + 1 = 2 by omega)) := by
  letI : Subsingleton (Ext.{u} (closedImmersionIdealTwistSequence i L).X₂ Y 1) :=
    ext_subsingleton_of_iso_left (Y := Y)
      (closedImmersionIdealTwistSequence_middleIso i L).symm 1
  exact closedImmersionIdealTwist_connectingExtOne_injective i L Y

/-- An extension sequence of a module sheaf `M` on a scheme.

This is the categorical extension before local freeness has been proved.  In
Voisin's Serre argument the middle term is first obtained from an `Ext¹`
class, and local freeness is then deduced from its local restrictions and the
Galois-orbit argument.  Keeping that conclusion out of this structure avoids
building it into the input to the local-freeness step. -/
structure SerreExtensionSequenceData (X : Scheme.{u})
    (M : SheafOfModules.{u} X.ringCatSheaf) where
  /-- The prospective rank-two sheaf. -/
  E : SheafOfModules.{u} X.ringCatSheaf
  /-- The canonical section. -/
  inclusion : SheafOfModules.unit X.ringCatSheaf ⟶ E
  /-- Its quotient. -/
  projection : E ⟶ M
  /-- The two maps form a complex. -/
  zero : inclusion ≫ projection = 0
  /-- The extension sequence is short exact. -/
  shortExact : (ShortComplex.mk inclusion projection zero).ShortExact

namespace SerreExtensionSequenceData

variable {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
  (e : SerreExtensionSequenceData X M)

/-- The short complex underlying an extension sequence. -/
noncomputable abbrev complex : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) :=
  ShortComplex.mk e.inclusion e.projection e.zero

/-- The `Ext¹` class of the extension sequence. -/
noncomputable def extensionClass [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)] :
    Ext M (SheafOfModules.unit X.ringCatSheaf) 1 :=
  e.shortExact.extClass

/-- An Ext¹ class becomes an actual Serre extension sequence once the
module-sheaf category is supplied with enough injectives.  For schemes this
categorical hypothesis is discharged below; the remaining work is the local
geometric proof that the resulting middle term is locally free. -/
theorem exists_of_extensionClass
    [EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf)] :
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
      hasExt_of_enoughInjectives _
    ∀ (z : Ext M (SheafOfModules.unit X.ringCatSheaf) 1),
      ∃ e : SerreExtensionSequenceData X M, e.extensionClass = z := by
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
    hasExt_of_enoughInjectives _
  intro z
  obtain ⟨E, i, p, hip, hS, hz⟩ := exists_shortExact_of_ext_one z
  refine ⟨⟨E, i, p, hip, hS⟩, ?_⟩
  exact hz

/-- Every degree-one class of module sheaves on a scheme is represented by a
short exact sequence.  This discharges the categorical existence hypothesis
in the Serre construction: enough injectives follow from exact
sheafification of module presheaves. -/
theorem exists_of_extensionClass_on_scheme :
    letI : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
      sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
      hasExt_of_enoughInjectives _
    ∀ (z : Ext M (SheafOfModules.unit X.ringCatSheaf) 1),
      ∃ e : SerreExtensionSequenceData X M, e.extensionClass = z := by
  let _ : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  exact exists_of_extensionClass

/-- A chosen short exact sequence realizing an `Ext¹` class of module sheaves
on a scheme.  This makes the categorical part of Serre's construction an
actual object that later local-freeness and section arguments can consume. -/
noncomputable def ofExtensionClass_on_scheme
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (z : Ext M (SheafOfModules.unit X.ringCatSheaf) 1) :
    SerreExtensionSequenceData X M := by
  let _ : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  exact Classical.choose (exists_of_extensionClass z)

/-- The selected sequence realizes the original `Ext¹` class exactly. -/
theorem extensionClass_ofExtensionClass_on_scheme
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (z : Ext M (SheafOfModules.unit X.ringCatSheaf) 1) :
    (ofExtensionClass_on_scheme z).extensionClass = z := by
  let _ : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  exact Classical.choose_spec (exists_of_extensionClass z)

/-- A nonzero class gives a non-split chosen Serre extension sequence. -/
theorem extensionClass_ofExtensionClass_on_scheme_ne_zero
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (z : Ext M (SheafOfModules.unit X.ringCatSheaf) 1) (hz : z ≠ 0) :
    (ofExtensionClass_on_scheme z).extensionClass ≠ 0 := by
  rw [extensionClass_ofExtensionClass_on_scheme]
  exact hz

/-- A nonzero local `Ext²` class produces an actual Serre extension sequence
whose extension class has the prescribed connecting image.  This combines
Serre's Ext lift with unconditional realization of `Ext¹` classes by short
exact sequences of module sheaves on a scheme. -/
theorem exists_of_nonzeroExtTwo_on_scheme_connecting :
    letI : EnoughInjectives (X.Modules) :=
      sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} (X.Modules) :=
      hasExt_of_enoughInjectives _
    letI : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
      sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
      hasExt_of_enoughInjectives _
    ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (L : X.Modules)
      [PreservesFiniteLimits (schemeModuleTensorRight L)]
      [PreservesFiniteColimits (schemeModuleTensorRight L)]
      [Subsingleton (Ext.{u} (show X.Modules from L)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)]
      (z : Ext.{u} (closedImmersionIdealTwistSequence i L).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)
      (_hz : z ≠ 0),
      ∃ e : SerreExtensionSequenceData X (closedImmersionIdealTwist i L),
        (closedImmersionIdealTwistSequence_shortExact i L).extClass.comp
          e.extensionClass (show 1 + 1 = 2 by omega) = z := by
  let _ : EnoughInjectives (X.Modules) :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  let _ : HasExt.{u} (X.Modules) :=
    hasExt_of_enoughInjectives _
  let _ : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  let _ : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
    hasExt_of_enoughInjectives _
  intro Z i hci L hlim hcol hsub z hz
  obtain ⟨x, hx, hconnecting⟩ :=
    closedImmersionIdealTwist_exists_nonzeroExtOne_of_nonzeroExtTwo_of_ext_two_subsingleton
      i L (show X.Modules from SheafOfModules.unit X.ringCatSheaf) z hz
  obtain ⟨e, he⟩ := exists_of_extensionClass x
  refine ⟨e, ?_⟩
  rwa [he]

/-- Realize the kernel-form Ext lift by an actual Serre extension sequence.
This is the correct categorical endpoint for the cubic-surface Serre
duality calculation: the selected nonzero local class is required to map to
zero on `O_S(3)`, rather than requiring all of
`Ext²(O_S(3), O_S)` to vanish. -/
theorem exists_of_nonzeroExtTwo_on_scheme_connecting_of_comp_eq_zero :
    letI : EnoughInjectives (X.Modules) :=
      sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} (X.Modules) :=
      hasExt_of_enoughInjectives _
    letI : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
      sheafOfModules_enoughInjectives X.ringCatSheaf
    letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
      hasExt_of_enoughInjectives _
    ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (L : X.Modules)
      [PreservesFiniteLimits (schemeModuleTensorRight L)]
      [PreservesFiniteColimits (schemeModuleTensorRight L)]
      (z : Ext.{u} (closedImmersionIdealTwistSequence i L).X₃
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) 2)
      (_hz : z ≠ 0)
      (_hnext :
        (Ext.mk₀ (closedImmersionIdealTwistSequence i L).g).comp z
          (zero_add 2) = 0),
      ∃ e : SerreExtensionSequenceData X (closedImmersionIdealTwist i L),
        (closedImmersionIdealTwistSequence_shortExact i L).extClass.comp
          e.extensionClass (show 1 + 1 = 2 by omega) = z := by
  let _ : EnoughInjectives (X.Modules) :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  let _ : HasExt.{u} (X.Modules) :=
    hasExt_of_enoughInjectives _
  let _ : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
    sheafOfModules_enoughInjectives X.ringCatSheaf
  let _ : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) :=
    hasExt_of_enoughInjectives _
  intro Z i hci L hlim hcol z hz hnext
  obtain ⟨x, hx, hconnecting⟩ :=
    closedImmersionIdealTwist_exists_nonzeroExtOne_of_nonzeroExtTwo_of_comp_eq_zero
      i L (show X.Modules from SheafOfModules.unit X.ringCatSheaf)
        z hz hnext
  obtain ⟨e, he⟩ := exists_of_extensionClass x
  refine ⟨e, ?_⟩
  rwa [he]

/-- The canonical section in an extension sequence is monic. -/
instance : Mono e.inclusion := e.shortExact.mono_f

/-- The quotient map in an extension sequence is epic. -/
instance : Epi e.projection := e.shortExact.epi_g

/-- Passing an extension class to its quotient gives zero. -/
@[simp]
theorem projection_comp_extensionClass
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)] :
    (Ext.mk₀ e.projection).comp e.extensionClass (zero_add 1) = 0 :=
  e.shortExact.comp_extClass

/-- Pulling an extension class back along its canonical section gives zero. -/
@[simp]
theorem extensionClass_comp_inclusion
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)] :
    e.extensionClass.comp (Ext.mk₀ e.inclusion) (add_zero 1) = 0 :=
  e.shortExact.extClass_comp

/-- A splitting of the quotient forces the class of an extension sequence to
vanish.  This conclusion is available before local freeness of the middle
term has been proved. -/
theorem extensionClass_eq_zero_of_projection_split
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (s : M ⟶ e.E) (hs : s ≫ e.projection = 𝟙 M) :
    e.extensionClass = 0 := by
  calc
    e.extensionClass = (Ext.mk₀ (𝟙 M)).comp e.extensionClass (zero_add 1) :=
      (Ext.mk₀_id_comp e.extensionClass).symm
    _ = (Ext.mk₀ (s ≫ e.projection)).comp e.extensionClass (zero_add 1) := by rw [hs]
    _ = (Ext.mk₀ s).comp
        ((Ext.mk₀ e.projection).comp e.extensionClass (zero_add 1))
        (zero_add 1) := by
      rw [Ext.mk₀_comp_mk₀_assoc]
    _ = 0 := by rw [e.projection_comp_extensionClass]; simp

/-- A nonzero class of an extension sequence prevents a global splitting of
its quotient. -/
theorem projection_not_split_of_extensionClass_ne_zero
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (he : e.extensionClass ≠ 0) (s : M ⟶ e.E) :
    s ≫ e.projection ≠ 𝟙 M := by
  intro hs
  exact he (e.extensionClass_eq_zero_of_projection_split s hs)

/-- Vanishing of `Ext¹(𝒪_X, 𝒪_X)` makes the quotient map of an extension
sequence surjective on global sections. Local freeness of the middle term
is not used here, so this lifting argument applies before Voisin's local
calculation proves that the extension is a vector bundle. -/
theorem projection_sections_surjective_of_ext_one_subsingleton
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    [Subsingleton (Ext (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) 1)] :
    Function.Surjective (SheafOfModules.sectionsMap e.projection) := by
  intro t
  let x₃ : Ext (SheafOfModules.unit X.ringCatSheaf) M 0 :=
    Ext.mk₀ (M.unitHomEquiv.symm t)
  have hx₃ : x₃.comp e.extensionClass (show 0 + 1 = 1 by omega) =
      (0 : Ext (SheafOfModules.unit X.ringCatSheaf)
        (SheafOfModules.unit X.ringCatSheaf) 1) :=
    Subsingleton.elim _ _
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃
    (SheafOfModules.unit X.ringCatSheaf) e.shortExact x₃
    (show 0 + 1 = 1 by omega) hx₃
  let s : e.E.sections := e.E.unitHomEquiv (Ext.addEquiv₀ x₂)
  refine ⟨s, ?_⟩
  apply M.unitHomEquiv.symm.injective
  calc
    M.unitHomEquiv.symm (SheafOfModules.sectionsMap e.projection s) =
        e.E.unitHomEquiv.symm s ≫ e.projection :=
      (e.E.unitHomEquiv_symm_comp s e.projection).symm
    _ = Ext.addEquiv₀ x₂ ≫ e.projection := by simp [s]
    _ = Ext.addEquiv₀ (x₂.comp (Ext.mk₀ e.projection) (show 0 + 0 = 0 by omega)) := by
      have hmap :
          x₂.comp (Ext.mk₀ e.projection) (show 0 + 0 = 0 by omega) =
            Ext.mk₀ (Ext.addEquiv₀ x₂ ≫ e.projection) := by
        calc
          x₂.comp (Ext.mk₀ e.projection) (show 0 + 0 = 0 by omega) =
              (Ext.mk₀ (Ext.addEquiv₀ x₂)).comp (Ext.mk₀ e.projection)
                (show 0 + 0 = 0 by omega) := by
            rw [Ext.mk₀_addEquiv₀_apply]
          _ = Ext.mk₀ (Ext.addEquiv₀ x₂ ≫ e.projection) :=
            Ext.mk₀_comp_mk₀ _ _
      apply (Ext.mk₀_bijective _ _).injective
      calc
        Ext.mk₀ (Ext.addEquiv₀ x₂ ≫ e.projection) =
            x₂.comp (Ext.mk₀ e.projection) (show 0 + 0 = 0 by omega) := hmap.symm
        _ = Ext.mk₀ (Ext.addEquiv₀
            (x₂.comp (Ext.mk₀ e.projection) (show 0 + 0 = 0 by omega))) := by
          rw [Ext.mk₀_addEquiv₀_apply]
    _ = Ext.addEquiv₀ x₃ := by rw [hx₂]
    _ = M.unitHomEquiv.symm t := by
      rw [show x₃ = Ext.mk₀ (M.unitHomEquiv.symm t) by rfl,
        ← Ext.addEquiv₀_symm_apply]
      exact Ext.addEquiv₀.apply_symm_apply _

/-- The zero global section, defined through the structure-sheaf representability
of sections.  Mathlib deliberately keeps `sections` as a type rather than
endowing it with a global additive instance. -/
noncomputable def zeroSection (A : SheafOfModules.{u} X.ringCatSheaf) : A.sections :=
  A.unitHomEquiv 0

@[simp]
theorem unitHomEquiv_symm_zeroSection (A : SheafOfModules.{u} X.ringCatSheaf) :
    A.unitHomEquiv.symm (zeroSection A) = 0 := by
  simp [zeroSection]

/-- The quotient map takes the zero section of an extension sequence to the
zero section of its quotient. -/
theorem projection_zeroSection :
    SheafOfModules.sectionsMap e.projection (zeroSection e.E) = zeroSection M := by
  calc
    SheafOfModules.sectionsMap e.projection (zeroSection e.E) =
        M.unitHomEquiv (0 ≫ e.projection) := by
          symm
          exact e.E.unitHomEquiv_comp_apply 0 e.projection
    _ = zeroSection M := by simp [zeroSection]

/-- The canonical section takes the zero section of the structure sheaf to
the zero section of the extension sequence.  This holds before any
local-freeness conclusion about the middle term. -/
theorem inclusion_zeroSection :
    SheafOfModules.sectionsMap e.inclusion
        (zeroSection (SheafOfModules.unit X.ringCatSheaf)) = zeroSection e.E := by
  calc
    SheafOfModules.sectionsMap e.inclusion
        (zeroSection (SheafOfModules.unit X.ringCatSheaf)) =
        e.E.unitHomEquiv (0 ≫ e.inclusion) := by
          symm
          exact (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv_comp_apply 0 e.inclusion
    _ = zeroSection e.E := by simp [zeroSection]

/-- A lift of a nonzero quotient section is distinct from the canonical zero
section already at the extension-sequence stage.  This is the two-section
input for Voisin's pencil before the Galois local-freeness argument is used. -/
theorem inclusion_zeroSection_ne_lift_of_projection_eq_nonzero
    (s : e.E.sections) (t : M.sections) (ht : t ≠ zeroSection M)
    (hs : SheafOfModules.sectionsMap e.projection s = t) :
    SheafOfModules.sectionsMap e.inclusion
      (zeroSection (SheafOfModules.unit X.ringCatSheaf)) ≠ s := by
  intro hzero
  apply ht
  rw [← hs, ← hzero, e.inclusion_zeroSection, e.projection_zeroSection]

/-- A lift of a nonzero quotient section is distinct from every section in
the canonical copy of `𝒪_X`, before local freeness of the middle term has
been established. -/
theorem inclusion_section_ne_lift_of_projection_eq_nonzero
    (s : e.E.sections) (t : M.sections) (ht : t ≠ zeroSection M)
    (hs : SheafOfModules.sectionsMap e.projection s = t)
    (u : (SheafOfModules.unit X.ringCatSheaf).sections) :
    SheafOfModules.sectionsMap e.inclusion u ≠ s := by
  intro hus
  have hzero : SheafOfModules.sectionsMap e.projection
      (SheafOfModules.sectionsMap e.inclusion u) = zeroSection M := by
    apply M.unitHomEquiv.symm.injective
    calc
      M.unitHomEquiv.symm
          (SheafOfModules.sectionsMap e.projection
            (SheafOfModules.sectionsMap e.inclusion u)) =
          e.E.unitHomEquiv.symm
            (SheafOfModules.sectionsMap e.inclusion u) ≫ e.projection :=
        (e.E.unitHomEquiv_symm_comp _ e.projection).symm
      _ = ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm u ≫
            e.inclusion) ≫ e.projection := by
        rw [← (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv_symm_comp]
      _ = (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm u ≫
          (e.inclusion ≫ e.projection) := Category.assoc _ _ _
      _ = 0 := by rw [e.zero]; simp
      _ = M.unitHomEquiv.symm (zeroSection M) :=
        (unitHomEquiv_symm_zeroSection M).symm
  apply ht
  rw [← hs, ← hus]
  exact hzero

/-- A globally surjective quotient map lifts every nonzero quotient section
nontrivially. This uses only the extension sequence, so it precedes the
local-freeness conclusion in Voisin's construction. -/
theorem exists_nonzero_section_lifting_of_projection_sections_surjective
    (hsurj : Function.Surjective (SheafOfModules.sectionsMap e.projection))
    (t : M.sections) (ht : t ≠ zeroSection M) :
    ∃ s : e.E.sections, s ≠ zeroSection e.E ∧
      SheafOfModules.sectionsMap e.projection s = t := by
  obtain ⟨s, hs⟩ := hsurj t
  refine ⟨s, ?_, hs⟩
  intro hzero
  apply ht
  rw [← hs, hzero, e.projection_zeroSection]

/-- Under the cohomological Ext-vanishing used by Voisin, every nonzero
quotient section has a nonzero lift before the middle term has been proved
locally free. -/
theorem exists_nonzero_section_lifting_of_ext_one_subsingleton
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    [Subsingleton (Ext (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) 1)]
    (t : M.sections) (ht : t ≠ zeroSection M) :
    ∃ s : e.E.sections, s ≠ zeroSection e.E ∧
      SheafOfModules.sectionsMap e.projection s = t := by
  exact e.exists_nonzero_section_lifting_of_projection_sections_surjective
    e.projection_sections_surjective_of_ext_one_subsingleton t ht

/-- The `Ext¹(𝒪_X, 𝒪_X)` vanishing used by Voisin therefore gives two
distinct extension-sequence sections directly from every nonzero quotient
section, without yet assuming that the middle term is locally free. -/
theorem exists_lift_distinct_from_canonical_zeroSection_of_ext_one_subsingleton
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    [Subsingleton (Ext (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) 1)]
    (t : M.sections) (ht : t ≠ zeroSection M) :
    ∃ s : e.E.sections,
      SheafOfModules.sectionsMap e.projection s = t ∧
      SheafOfModules.sectionsMap e.inclusion
        (zeroSection (SheafOfModules.unit X.ringCatSheaf)) ≠ s := by
  obtain ⟨s, hs⟩ := e.projection_sections_surjective_of_ext_one_subsingleton t
  exact ⟨s, hs,
    e.inclusion_zeroSection_ne_lift_of_projection_eq_nonzero s t ht hs⟩

/-- A surjective quotient map lifts a nonzero quotient section to a section
which differs from every section of the canonical copy of `𝒪_X`.  This
needs only exactness of the extension sequence, not local freeness. -/
theorem exists_lift_distinct_from_canonical_section_of_projection_sections_surjective
    (hsurj : Function.Surjective (SheafOfModules.sectionsMap e.projection))
    (t : M.sections) (ht : t ≠ zeroSection M) :
    ∃ s : e.E.sections,
      SheafOfModules.sectionsMap e.projection s = t ∧
      ∀ u : (SheafOfModules.unit X.ringCatSheaf).sections,
        SheafOfModules.sectionsMap e.inclusion u ≠ s := by
  obtain ⟨s, hs⟩ := hsurj t
  exact ⟨s, hs, fun u =>
    e.inclusion_section_ne_lift_of_projection_eq_nonzero s t ht hs u⟩

/-- The same Ext-vanishing makes the lift distinct from every section of the
canonical copy of `𝒪_X`, before the separate local-freeness argument. -/
theorem exists_lift_distinct_from_canonical_section_of_ext_one_subsingleton
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    [Subsingleton (Ext (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) 1)]
    (t : M.sections) (ht : t ≠ zeroSection M) :
    ∃ s : e.E.sections,
      SheafOfModules.sectionsMap e.projection s = t ∧
      ∀ u : (SheafOfModules.unit X.ringCatSheaf).sections,
        SheafOfModules.sectionsMap e.inclusion u ≠ s := by
  exact e.exists_lift_distinct_from_canonical_section_of_projection_sections_surjective
    e.projection_sections_surjective_of_ext_one_subsingleton t ht

/-- Translate a section of the middle term by a section of the canonical
copy of the structure sheaf. -/
noncomputable def translateByCanonicalSection (s : e.E.sections)
    (t : (SheafOfModules.unit X.ringCatSheaf).sections) : e.E.sections :=
  e.E.unitHomEquiv (e.E.unitHomEquiv.symm s +
    (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm t ≫ e.inclusion)

/-- Canonical translation preserves the image of a section in the quotient. -/
theorem projection_translateByCanonicalSection (s : e.E.sections)
    (t : (SheafOfModules.unit X.ringCatSheaf).sections) :
    SheafOfModules.sectionsMap e.projection (e.translateByCanonicalSection s t) =
      SheafOfModules.sectionsMap e.projection s := by
  apply M.unitHomEquiv.symm.injective
  calc
    M.unitHomEquiv.symm
        (SheafOfModules.sectionsMap e.projection
          (e.translateByCanonicalSection s t)) =
        e.E.unitHomEquiv.symm (e.translateByCanonicalSection s t) ≫ e.projection :=
      (e.E.unitHomEquiv_symm_comp _ e.projection).symm
    _ = (e.E.unitHomEquiv.symm s +
          (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm t ≫ e.inclusion) ≫
        e.projection := by simp only [translateByCanonicalSection, Equiv.symm_apply_apply]
    _ = e.E.unitHomEquiv.symm s ≫ e.projection +
          ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm t ≫
            e.inclusion) ≫ e.projection := by rw [Preadditive.add_comp]
    _ = e.E.unitHomEquiv.symm s ≫ e.projection +
          (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm t ≫
            (e.inclusion ≫ e.projection) := by rw [Category.assoc]
    _ = e.E.unitHomEquiv.symm s ≫ e.projection := by rw [e.zero]; simp
    _ = M.unitHomEquiv.symm (SheafOfModules.sectionsMap e.projection s) :=
      e.E.unitHomEquiv_symm_comp s e.projection

/-- A section of `E` whose image in the quotient vanishes comes from a unique
section of `𝒪_X`.  This is exactness at the middle term after taking global
sections. -/
theorem exists_unique_unit_section_of_projection_sections_eq_zero
    (s : e.E.sections)
    (hs : SheafOfModules.sectionsMap e.projection s = zeroSection M) :
    ∃! t : (SheafOfModules.unit X.ringCatSheaf).sections,
      SheafOfModules.sectionsMap e.inclusion t = s := by
  have hs' : e.E.unitHomEquiv.symm s ≫ e.projection = 0 := by
    calc
      e.E.unitHomEquiv.symm s ≫ e.projection =
          M.unitHomEquiv.symm (SheafOfModules.sectionsMap e.projection s) :=
        e.E.unitHomEquiv_symm_comp s e.projection
      _ = M.unitHomEquiv.symm (zeroSection M) := by rw [hs]
      _ = 0 := unitHomEquiv_symm_zeroSection M
  let l : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
    e.shortExact.fIsKernel.lift (KernelFork.ofι (e.E.unitHomEquiv.symm s) hs')
  have hl : l ≫ e.inclusion = e.E.unitHomEquiv.symm s :=
    e.shortExact.fIsKernel.fac (KernelFork.ofι (e.E.unitHomEquiv.symm s) hs')
      WalkingParallelPair.zero
  refine ⟨(SheafOfModules.unit X.ringCatSheaf).unitHomEquiv l, ?_, ?_⟩
  · apply e.E.unitHomEquiv.symm.injective
    calc
      e.E.unitHomEquiv.symm
          (SheafOfModules.sectionsMap e.inclusion
            ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv l)) =
          (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
            ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv l) ≫ e.inclusion :=
        (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv_symm_comp _ e.inclusion |>.symm
      _ = l ≫ e.inclusion := by simp
      _ = e.E.unitHomEquiv.symm s := hl
  · intro t ht
    apply (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm.injective
    apply (cancel_mono e.inclusion).mp
    calc
      (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm t ≫ e.inclusion =
          e.E.unitHomEquiv.symm (SheafOfModules.sectionsMap e.inclusion t) :=
        (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv_symm_comp t e.inclusion
      _ = e.E.unitHomEquiv.symm s := congrArg e.E.unitHomEquiv.symm ht
      _ = l ≫ e.inclusion := hl.symm
      _ = (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
          ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv l) ≫ e.inclusion := by simp

/-- The fibers of the quotient map on sections are torsors for canonical
sections of the structure sheaf. -/
theorem exists_unique_translateByCanonicalSection_of_projection_eq
    (s r : e.E.sections)
    (h : SheafOfModules.sectionsMap e.projection r =
      SheafOfModules.sectionsMap e.projection s) :
    ∃! t : (SheafOfModules.unit X.ringCatSheaf).sections,
      e.translateByCanonicalSection s t = r := by
  let d : e.E.sections :=
    e.E.unitHomEquiv (e.E.unitHomEquiv.symm r - e.E.unitHomEquiv.symm s)
  have hd : SheafOfModules.sectionsMap e.projection d = zeroSection M := by
    apply M.unitHomEquiv.symm.injective
    have h' : e.E.unitHomEquiv.symm r ≫ e.projection =
        e.E.unitHomEquiv.symm s ≫ e.projection := by
      calc
        e.E.unitHomEquiv.symm r ≫ e.projection =
            M.unitHomEquiv.symm (SheafOfModules.sectionsMap e.projection r) :=
          e.E.unitHomEquiv_symm_comp r e.projection
        _ = M.unitHomEquiv.symm (SheafOfModules.sectionsMap e.projection s) := by rw [h]
        _ = e.E.unitHomEquiv.symm s ≫ e.projection :=
          (e.E.unitHomEquiv_symm_comp s e.projection).symm
    calc
      M.unitHomEquiv.symm (SheafOfModules.sectionsMap e.projection d) =
          e.E.unitHomEquiv.symm d ≫ e.projection :=
        (e.E.unitHomEquiv_symm_comp d e.projection).symm
      _ = (e.E.unitHomEquiv.symm r - e.E.unitHomEquiv.symm s) ≫ e.projection := by
        simp only [d, Equiv.symm_apply_apply]
      _ = e.E.unitHomEquiv.symm r ≫ e.projection -
          e.E.unitHomEquiv.symm s ≫ e.projection := by rw [Preadditive.sub_comp]
      _ = 0 := sub_eq_zero.mpr h'
      _ = M.unitHomEquiv.symm (zeroSection M) :=
        (unitHomEquiv_symm_zeroSection M).symm
  obtain ⟨t, ht, htuniq⟩ :=
    e.exists_unique_unit_section_of_projection_sections_eq_zero d hd
  refine ⟨t, ?_, ?_⟩
  · apply e.E.unitHomEquiv.symm.injective
    have ht' : (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm t ≫
        e.inclusion = e.E.unitHomEquiv.symm r - e.E.unitHomEquiv.symm s := by
      calc
        (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm t ≫ e.inclusion =
            e.E.unitHomEquiv.symm (SheafOfModules.sectionsMap e.inclusion t) :=
          (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv_symm_comp t e.inclusion
        _ = e.E.unitHomEquiv.symm d := congrArg e.E.unitHomEquiv.symm ht
        _ = e.E.unitHomEquiv.symm r - e.E.unitHomEquiv.symm s := by
          simp only [d, Equiv.symm_apply_apply]
    simp only [translateByCanonicalSection, Equiv.symm_apply_apply]
    rw [ht']
    abel
  · intro t' ht'
    apply htuniq t'
    apply e.E.unitHomEquiv.symm.injective
    have ht'' := congrArg e.E.unitHomEquiv.symm ht'
    simp only [translateByCanonicalSection, Equiv.symm_apply_apply] at ht''
    calc
      e.E.unitHomEquiv.symm (SheafOfModules.sectionsMap e.inclusion t') =
          (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm t' ≫ e.inclusion :=
        (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv_symm_comp t' e.inclusion |>.symm
      _ = e.E.unitHomEquiv.symm r - e.E.unitHomEquiv.symm s := by
        rw [← ht'']
        abel
      _ = e.E.unitHomEquiv.symm d := by simp only [d, Equiv.symm_apply_apply]

/-- Global sections of an extension sequence are exact at the middle term.

The module-sheaf short exact sequence itself is categorical.  This theorem
records its concrete consequence for the types of global sections: a section
of `E` maps to zero in the twisted ideal quotient exactly when it is a section
of the canonical copy of `𝒪_X`.  The chosen `Zero` structure is deliberately
local to the statement, since Mathlib represents global sections as a type
rather than giving it a global additive structure. -/
theorem sections_exact :
    letI : Zero M.sections := ⟨zeroSection M⟩
    Function.Exact (SheafOfModules.sectionsMap e.inclusion)
      (SheafOfModules.sectionsMap e.projection) := by
  letI : Zero M.sections := ⟨zeroSection M⟩
  intro s
  constructor
  · intro hs
    obtain ⟨t, ht, -⟩ :=
      e.exists_unique_unit_section_of_projection_sections_eq_zero s hs
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    rw [← ht]
    apply M.unitHomEquiv.symm.injective
    calc
      M.unitHomEquiv.symm
          (SheafOfModules.sectionsMap e.projection
            (SheafOfModules.sectionsMap e.inclusion t)) =
          e.E.unitHomEquiv.symm
            (SheafOfModules.sectionsMap e.inclusion t) ≫ e.projection :=
        (e.E.unitHomEquiv_symm_comp _ e.projection).symm
      _ = ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm t ≫
            e.inclusion) ≫ e.projection := by
        rw [← (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv_symm_comp]
      _ = (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm t ≫
          (e.inclusion ≫ e.projection) := Category.assoc _ _ _
      _ = 0 := by rw [e.zero]; simp
      _ = M.unitHomEquiv.symm (zeroSection M) :=
        (unitHomEquiv_symm_zeroSection M).symm


end SerreExtensionSequenceData

/-- A locally free Serre extension of a module sheaf `M` on a scheme.

The intended instance has `M = I_Z ⊗ L`; `E` is the rank-two bundle used by
Voisin.  Keeping the quotient arbitrary makes the section-level lemmas
applicable to every later degree step. -/
structure SerreExtensionData (X : Scheme.{u})
    (M : SheafOfModules.{u} X.ringCatSheaf) where
  /-- The prospective rank-two bundle. -/
  E : SheafOfModules.{u} X.ringCatSheaf
  /-- The canonical section of the bundle. -/
  inclusion : SheafOfModules.unit X.ringCatSheaf ⟶ E
  /-- Its quotient by the canonical section. -/
  projection : E ⟶ M
  /-- The two maps form a complex. -/
  zero : inclusion ≫ projection = 0
  /-- The sequence is short exact. -/
  shortExact : (ShortComplex.mk inclusion projection zero).ShortExact
  /-- The middle term is locally free. -/
  locallyFree : E.IsLocallyFree

namespace SerreExtensionData

variable {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
  (e : SerreExtensionData X M)

/-- Forget the local-freeness conclusion and retain the underlying extension
sequence.  This is the form to which the local Ext and Galois arguments
apply. -/
noncomputable def toSequenceData : SerreExtensionSequenceData X M :=
  { E := e.E
    inclusion := e.inclusion
    projection := e.projection
    zero := e.zero
    shortExact := e.shortExact }

/-- Once local freeness of an extension sequence has been established, it is
the Serre extension datum used for the section and pencil arguments. -/
noncomputable def ofSequence
    (s : SerreExtensionSequenceData X M) (hlocalFree : s.E.IsLocallyFree) :
    SerreExtensionData X M :=
  { E := s.E
    inclusion := s.inclusion
    projection := s.projection
    zero := s.zero
    shortExact := s.shortExact
    locallyFree := hlocalFree }

/-- The short complex underlying a Serre extension. -/
noncomputable abbrev complex : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) :=
  ShortComplex.mk e.inclusion e.projection e.zero

/-- The canonical `Ext¹` class of the short exact sequence.

The missing Serre-duality step must construct an extension whose class has the
local nonvanishing needed for local freeness.  This declaration is the direct
bridge from the present sheaf-level datum to that future calculation. -/
noncomputable def extensionClass [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)] :
    Ext M (SheafOfModules.unit X.ringCatSheaf) 1 :=
  e.shortExact.extClass

/-- Forgetting local freeness does not change the Ext class of the extension.
This identifies the pre-local-freeness Serre argument with the usual
locally-free formulation once the local calculation is complete. -/
@[simp]
theorem toSequenceData_extensionClass
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)] :
    e.toSequenceData.extensionClass = e.extensionClass := rfl

/-- The extension class becomes zero after passage to the Serre quotient.
This is the first exactness relation that an Ext¹ class constructed by Serre
duality must satisfy. -/
@[simp]
theorem projection_comp_extensionClass
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)] :
    (Ext.mk₀ e.projection).comp e.extensionClass (zero_add 1) = 0 :=
  e.shortExact.comp_extClass

/-- Pulling the extension class back along the canonical inclusion gives
zero.  Together with `projection_comp_extensionClass`, this records the two
boundary relations of the Serre short exact sequence in Ext. -/
@[simp]
theorem extensionClass_comp_inclusion
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)] :
    e.extensionClass.comp (Ext.mk₀ e.inclusion) (add_zero 1) = 0 :=
  e.shortExact.extClass_comp

/-- A section of the quotient map splits the Serre extension, so its Ext
class vanishes.  Thus the nonzero class constructed by Serre duality is not
just decorative: it rules out a global splitting of the ideal-sheaf quotient. -/
theorem extensionClass_eq_zero_of_projection_split
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (s : M ⟶ e.E) (hs : s ≫ e.projection = 𝟙 M) :
    e.extensionClass = 0 := by
  calc
    e.extensionClass = (Ext.mk₀ (𝟙 M)).comp e.extensionClass (zero_add 1) :=
      (Ext.mk₀_id_comp e.extensionClass).symm
    _ = (Ext.mk₀ (s ≫ e.projection)).comp e.extensionClass (zero_add 1) := by rw [hs]
    _ = (Ext.mk₀ s).comp
        ((Ext.mk₀ e.projection).comp e.extensionClass (zero_add 1))
        (zero_add 1) := by
      rw [Ext.mk₀_comp_mk₀_assoc]
    _ = 0 := by rw [e.projection_comp_extensionClass]; simp

/-- A retraction of the canonical inclusion also splits the extension and
therefore forces its Ext class to vanish. -/
theorem extensionClass_eq_zero_of_inclusion_split
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (r : e.E ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hr : e.inclusion ≫ r = 𝟙 _) :
    e.extensionClass = 0 := by
  calc
    e.extensionClass = e.extensionClass.comp (Ext.mk₀ (𝟙 _)) (add_zero 1) :=
      (Ext.comp_mk₀_id e.extensionClass).symm
    _ = e.extensionClass.comp (Ext.mk₀ (e.inclusion ≫ r)) (add_zero 1) := by rw [hr]
    _ = (e.extensionClass.comp (Ext.mk₀ e.inclusion) (add_zero 1)).comp
        (Ext.mk₀ r) (add_zero 1) := by
      rw [← Ext.mk₀_comp_mk₀]
      simpa using (Ext.comp_assoc_of_second_deg_zero e.extensionClass
        (Ext.mk₀ e.inclusion) (Ext.mk₀ r) (add_zero 1)).symm
    _ = 0 := by rw [e.extensionClass_comp_inclusion]; simp

/-- A nonzero Serre extension class has no section splitting the quotient
map. -/
theorem projection_not_split_of_extensionClass_ne_zero
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (he : e.extensionClass ≠ 0) (s : M ⟶ e.E) :
    s ≫ e.projection ≠ 𝟙 M := by
  intro hs
  exact he (e.extensionClass_eq_zero_of_projection_split s hs)

/-- A nonzero Serre extension class has no retraction of its canonical
inclusion. -/
theorem inclusion_not_split_of_extensionClass_ne_zero
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (he : e.extensionClass ≠ 0)
    (r : e.E ⟶ SheafOfModules.unit X.ringCatSheaf) :
    e.inclusion ≫ r ≠ 𝟙 _ := by
  intro hr
  exact he (e.extensionClass_eq_zero_of_inclusion_split r hr)

/-- The canonical section is a monomorphism of sheaves. -/
instance : Mono e.inclusion := e.shortExact.mono_f

/-- The quotient map is an epimorphism of sheaves. -/
instance : Epi e.projection := e.shortExact.epi_g

/-- The zero global section, defined through the structure-sheaf representability
of sections.  Mathlib deliberately keeps `sections` as a type rather than
endowing it with a global additive instance. -/
noncomputable def zeroSection (A : SheafOfModules.{u} X.ringCatSheaf) : A.sections :=
  A.unitHomEquiv 0

@[simp]
theorem unitHomEquiv_symm_zeroSection (A : SheafOfModules.{u} X.ringCatSheaf) :
    A.unitHomEquiv.symm (zeroSection A) = 0 := by
  simp [zeroSection]

/-- A monomorphism of module sheaves is injective on global sections.

This uses the representation of global sections as maps from the structure
sheaf, so it needs no cohomology vanishing. -/
theorem sectionsMap_injective_of_mono
    {A B : SheafOfModules.{u} X.ringCatSheaf} (f : A ⟶ B) [Mono f] :
    Function.Injective (SheafOfModules.sectionsMap f) := by
  intro a b hab
  apply A.unitHomEquiv.symm.injective
  apply (cancel_mono f).mp
  rw [A.unitHomEquiv_symm_comp, A.unitHomEquiv_symm_comp, hab]

/-- The canonical section injects global sections of `𝒪_X` into those of `E`.
This is the first section-space conclusion in Voisin's Lemma 3.1. -/
theorem inclusion_sections_injective :
    Function.Injective (SheafOfModules.sectionsMap e.inclusion) :=
  sectionsMap_injective_of_mono e.inclusion

/-- Taking the canonical inclusion of a zero section gives a zero section. -/
theorem inclusion_zeroSection :
    SheafOfModules.sectionsMap e.inclusion
        (zeroSection (SheafOfModules.unit X.ringCatSheaf)) = zeroSection e.E := by
  calc
    SheafOfModules.sectionsMap e.inclusion
        (zeroSection (SheafOfModules.unit X.ringCatSheaf)) =
        e.E.unitHomEquiv (0 ≫ e.inclusion) := by
          symm
          exact (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv_comp_apply 0 e.inclusion
    _ = zeroSection e.E := by simp [zeroSection]

/-- The quotient map takes the zero section of the Serre bundle to the zero
section of its quotient. -/
theorem projection_zeroSection :
    SheafOfModules.sectionsMap e.projection (zeroSection e.E) = zeroSection M := by
  exact e.toSequenceData.projection_zeroSection


/-- Vanishing of `Ext¹(𝒪_X, 𝒪_X)` makes the quotient map in a Serre
extension surjective on global sections.

This is the homological-algebra step behind Voisin's use of
`H¹(S, O_S) = 0`: the long exact Ext sequence lifts every quotient section
through the locally free middle term. -/
theorem projection_sections_surjective_of_ext_one_subsingleton
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    [Subsingleton (Ext (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) 1)] :
    Function.Surjective (SheafOfModules.sectionsMap e.projection) := by
  exact e.toSequenceData.projection_sections_surjective_of_ext_one_subsingleton

/-- If the quotient map is surjective on global sections, a nonzero quotient
section has a nonzero lift to the Serre bundle.

For the cubic surface this is the section-lifting consequence of
`H¹(S, O_S) = 0` used in Lemma 3.1(c) and Proposition 3.2. -/
theorem exists_nonzero_section_lifting_of_projection_sections_surjective
    (hsurj : Function.Surjective (SheafOfModules.sectionsMap e.projection))
    (t : M.sections) (ht : t ≠ zeroSection M) :
    ∃ s : e.E.sections, s ≠ zeroSection e.E ∧
      SheafOfModules.sectionsMap e.projection s = t := by
  exact e.toSequenceData.exists_nonzero_section_lifting_of_projection_sections_surjective
    hsurj t ht

/-- Under the same Ext-vanishing hypothesis, every nonzero quotient section
has a nonzero lift to the Serre bundle.

This is the exact form used after choosing a section through Voisin's three
rank-two fibers. -/
theorem exists_nonzero_section_lifting_of_ext_one_subsingleton
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    [Subsingleton (Ext (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) 1)]
    (t : M.sections) (ht : t ≠ zeroSection M) :
    ∃ s : e.E.sections, s ≠ zeroSection e.E ∧
      SheafOfModules.sectionsMap e.projection s = t := by
  exact e.toSequenceData.exists_nonzero_section_lifting_of_ext_one_subsingleton t ht

/-- A lift of a nonzero quotient section is distinct from every section in
the canonical copy of `𝒪_X`.  This supplies the two different global bundle
sections used to start Voisin's rank-two pencil once a nonzero quotient
section has been found. -/
theorem inclusion_section_ne_lift_of_projection_eq_nonzero
    (s : e.E.sections) (t : M.sections) (ht : t ≠ zeroSection M)
    (hs : SheafOfModules.sectionsMap e.projection s = t)
    (u : (SheafOfModules.unit X.ringCatSheaf).sections) :
    SheafOfModules.sectionsMap e.inclusion u ≠ s := by
  exact e.toSequenceData.inclusion_section_ne_lift_of_projection_eq_nonzero
    s t ht hs u

/-- If the quotient map is surjective on global sections and the quotient
has a nonzero section, the Serre bundle has a lift which is distinct from its
canonical zero section.  This is the section-theoretic two-point input for
the pencil in Proposition 3.2. -/
theorem exists_lift_distinct_from_canonical_zeroSection_of_projection_sections_surjective
    (hsurj : Function.Surjective (SheafOfModules.sectionsMap e.projection))
    (t : M.sections) (ht : t ≠ zeroSection M) :
    ∃ s : e.E.sections,
      SheafOfModules.sectionsMap e.projection s = t ∧
      SheafOfModules.sectionsMap e.inclusion
        (zeroSection (SheafOfModules.unit X.ringCatSheaf)) ≠ s := by
  obtain ⟨s, hs⟩ := hsurj t
  refine ⟨s, hs, ?_⟩
  exact e.inclusion_section_ne_lift_of_projection_eq_nonzero s t ht hs
    (zeroSection (SheafOfModules.unit X.ringCatSheaf))

/-- The `Ext¹(𝒪_X,𝒪_X)` vanishing used on a cubic surface therefore supplies
the two distinct sections directly from any nonzero quotient section. -/
theorem exists_lift_distinct_from_canonical_zeroSection_of_ext_one_subsingleton
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    [Subsingleton (Ext (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) 1)]
    (t : M.sections) (ht : t ≠ zeroSection M) :
    ∃ s : e.E.sections,
      SheafOfModules.sectionsMap e.projection s = t ∧
      SheafOfModules.sectionsMap e.inclusion
        (zeroSection (SheafOfModules.unit X.ringCatSheaf)) ≠ s := by
  exact
    e.exists_lift_distinct_from_canonical_zeroSection_of_projection_sections_surjective
      e.projection_sections_surjective_of_ext_one_subsingleton t ht

/-- The locally free Serre datum inherits the all-canonical-section form of
the two-section lifting statement from its underlying extension sequence. -/
theorem exists_lift_distinct_from_canonical_section_of_projection_sections_surjective
    (hsurj : Function.Surjective (SheafOfModules.sectionsMap e.projection))
    (t : M.sections) (ht : t ≠ zeroSection M) :
    ∃ s : e.E.sections,
      SheafOfModules.sectionsMap e.projection s = t ∧
      ∀ u : (SheafOfModules.unit X.ringCatSheaf).sections,
        SheafOfModules.sectionsMap e.inclusion u ≠ s := by
  exact SerreExtensionSequenceData.exists_lift_distinct_from_canonical_section_of_projection_sections_surjective
    e.toSequenceData hsurj t ht

/-- The Ext-vanishing used in Lemma 3.1(c) provides a lift which differs
from every canonical section.  This is the two-section statement needed
before one forms the rank-two pencil in Proposition 3.2. -/
theorem exists_lift_distinct_from_canonical_section_of_ext_one_subsingleton
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    [Subsingleton (Ext (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) 1)]
    (t : M.sections) (ht : t ≠ zeroSection M) :
    ∃ s : e.E.sections,
      SheafOfModules.sectionsMap e.projection s = t ∧
      ∀ u : (SheafOfModules.unit X.ringCatSheaf).sections,
        SheafOfModules.sectionsMap e.inclusion u ≠ s := by
  exact e.exists_lift_distinct_from_canonical_section_of_projection_sections_surjective
    e.projection_sections_surjective_of_ext_one_subsingleton t ht

/-- The two global sections from which Voisin forms the rank-two pencil.
The lift is recorded together with the stronger fact that it lies outside the
entire canonical copy of `𝒪_X`, rather than merely being nonzero. -/
structure SerreExtensionPencilSeed
    (e : SerreExtensionData X M) where
  quotientSection : M.sections
  quotientSection_ne_zero : quotientSection ≠ zeroSection M
  lift : e.E.sections
  projection_lift : SheafOfModules.sectionsMap e.projection lift = quotientSection
  lift_not_canonical : ∀ u : (SheafOfModules.unit X.ringCatSheaf).sections,
    SheafOfModules.sectionsMap e.inclusion u ≠ lift

/-- The cohomological vanishing in Voisin's Lemma 3.1 produces a pencil seed
from every nonzero quotient section.  Constructing the corresponding family
of zero loci remains the geometric part of Proposition 3.2. -/
theorem nonempty_serreExtensionPencilSeed_of_ext_one_subsingleton
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    [Subsingleton (Ext (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) 1)]
    (t : M.sections) (ht : t ≠ zeroSection M) :
    Nonempty (SerreExtensionPencilSeed e) := by
  obtain ⟨s, hs, hnot⟩ :=
    e.exists_lift_distinct_from_canonical_section_of_ext_one_subsingleton t ht
  exact ⟨⟨t, ht, s, hs, hnot⟩⟩

/-- The morphism from the trivial rank-two module to the Serre bundle whose
two components are the canonical section and the chosen lift.  This is the
linear system underlying Voisin's pencil in Proposition 3.2.  Its local zero
loci and their projective-line family are constructed in the accompanying
Serre-pencil gluing files. -/
noncomputable def SerreExtensionPencilSeed.pencilMap
    (seed : SerreExtensionPencilSeed e) :
    (SheafOfModules.unit X.ringCatSheaf) ⊞
      (SheafOfModules.unit X.ringCatSheaf) ⟶ e.E :=
  biprod.desc e.inclusion (e.E.unitHomEquiv.symm seed.lift)

/-- The first generator of the pencil is the canonical section of the Serre
extension. -/
theorem SerreExtensionPencilSeed.inl_pencilMap
    (seed : SerreExtensionPencilSeed e) :
    biprod.inl ≫ seed.pencilMap = e.inclusion := by
  exact biprod.inl_desc _ _

/-- The second generator of the pencil is the homomorphism represented by
the chosen lifted global section. -/
theorem SerreExtensionPencilSeed.inr_pencilMap
    (seed : SerreExtensionPencilSeed e) :
    biprod.inr ≫ seed.pencilMap = e.E.unitHomEquiv.symm seed.lift := by
  exact biprod.inr_desc _ _

/-- The global section represented by the canonical inclusion.  Keeping this
as a named section makes the two points of the pencil available before any
construction of their zero schemes. -/
noncomputable def canonicalSection : e.E.sections :=
  SheafOfModules.sectionsMap e.inclusion
    ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv (𝟙 _))

/-- The two global sections selected for the pencil are distinct. -/
theorem SerreExtensionPencilSeed.lift_ne_canonicalSection
    (seed : SerreExtensionPencilSeed e) : seed.lift ≠ e.canonicalSection := by
  simpa only [canonicalSection] using
    (seed.lift_not_canonical
      ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv (𝟙 _))).symm

/-- The lifted generator is not a canonical generator multiplied by any
global endomorphism of the structure sheaf.  Thus the two entries of the
pencil map are genuinely distinct at the level of module morphisms. -/
theorem SerreExtensionPencilSeed.liftHom_ne_canonical
    (seed : SerreExtensionPencilSeed e)
    (a : (SheafOfModules.unit X.ringCatSheaf) ⟶
      (SheafOfModules.unit X.ringCatSheaf)) :
    e.E.unitHomEquiv.symm seed.lift ≠ a ≫ e.inclusion := by
  intro h
  apply seed.lift_not_canonical
    ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv a)
  apply e.E.unitHomEquiv.symm.injective
  calc
    e.E.unitHomEquiv.symm
        (SheafOfModules.sectionsMap e.inclusion
          ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv a)) =
        (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
          ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv a) ≫ e.inclusion :=
      (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv_symm_comp _ e.inclusion |>.symm
    _ = a ≫ e.inclusion := by simp
    _ = e.E.unitHomEquiv.symm seed.lift := h.symm

/-- A linear combination of the two generators of the Serre pencil, written
as a morphism from the structure sheaf.  On a local trivialization of `E`,
these are the sections whose common zero schemes form Voisin's family. -/
noncomputable def SerreExtensionPencilSeed.linearCombination
    (seed : SerreExtensionPencilSeed e)
    (a b : (SheafOfModules.unit X.ringCatSheaf) ⟶
      (SheafOfModules.unit X.ringCatSheaf)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ e.E :=
  a ≫ e.inclusion + b ≫ e.E.unitHomEquiv.symm seed.lift

/-- Simultaneously multiplying the two coefficients of a pencil member by a
scalar endomorphism multiplies the resulting section by that same scalar.
This is the homogeneous-coordinate identity used on the overlap of the two
standard charts of the parameter projective line. -/
theorem SerreExtensionPencilSeed.linearCombination_left_scale
    (seed : SerreExtensionPencilSeed e)
    (c a b : (SheafOfModules.unit X.ringCatSheaf) ⟶
      (SheafOfModules.unit X.ringCatSheaf)) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombination e seed
      (c ≫ a) (c ≫ b) = c ≫
        PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombination e seed
          a b := by
  simp only [SerreExtensionPencilSeed.linearCombination, Category.assoc,
    Preadditive.comp_add]

/-- Every member of the two-dimensional linear system factors through the
single pencil map.  This is the categorical form of taking a homogeneous
linear combination of the two chosen bundle sections. -/
theorem SerreExtensionPencilSeed.linearCombination_eq_lift_comp_pencilMap
    (seed : SerreExtensionPencilSeed e)
    (a b : (SheafOfModules.unit X.ringCatSheaf) ⟶
      (SheafOfModules.unit X.ringCatSheaf)) :
    biprod.lift a b ≫
      PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.pencilMap e seed =
      PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombination e seed a b := by
  rw [PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.pencilMap,
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombination]
  exact biprod.lift_desc

/-- The quotient of a pencil member only records its lifted component.  This
is the exact categorical identity behind the distinction between the
canonical section and a noncanonical member of Voisin's pencil. -/
theorem SerreExtensionPencilSeed.projection_linearCombination
    (seed : SerreExtensionPencilSeed e)
    (a b : (SheafOfModules.unit X.ringCatSheaf) ⟶
      (SheafOfModules.unit X.ringCatSheaf)) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombination e seed a b ≫
      e.projection =
      b ≫ M.unitHomEquiv.symm seed.quotientSection := by
  calc
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombination e seed a b ≫
      e.projection =
        (a ≫ e.inclusion) ≫ e.projection +
          (b ≫ e.E.unitHomEquiv.symm seed.lift) ≫ e.projection := by
      rw [PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombination,
        Preadditive.add_comp]
    _ = b ≫ (e.E.unitHomEquiv.symm seed.lift ≫ e.projection) := by
      rw [Category.assoc, e.zero, comp_zero, zero_add]
      rw [Category.assoc]
    _ = b ≫ M.unitHomEquiv.symm
        (SheafOfModules.sectionsMap e.projection seed.lift) := by
      rw [e.E.unitHomEquiv_symm_comp]
    _ = b ≫ M.unitHomEquiv.symm seed.quotientSection := by
      rw [seed.projection_lift]

/-- The two distinguished parameters of the Serre pencil recover its
canonical and lifted generators. -/
theorem SerreExtensionPencilSeed.linearCombination_one_zero
    (seed : SerreExtensionPencilSeed e) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombination e seed
      (𝟙 _) 0 = e.inclusion := by
  rw [PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombination]
  simp

/-- The lifted generator is nonzero: its image in the quotient is the chosen
nonzero quotient section. -/
theorem SerreExtensionPencilSeed.liftHom_ne_zero
    (seed : SerreExtensionPencilSeed e) :
    e.E.unitHomEquiv.symm seed.lift ≠ 0 := by
  intro h
  apply seed.quotientSection_ne_zero
  apply M.unitHomEquiv.symm.injective
  rw [unitHomEquiv_symm_zeroSection]
  have hq : M.unitHomEquiv.symm seed.quotientSection = 0 := by
    rw [← seed.projection_lift, ← e.E.unitHomEquiv_symm_comp, h, zero_comp]
  exact hq

/-- Any affine member of the pencil (coefficient one on the lifted section)
is outside the canonical copy of the structure sheaf.  This is the
section-level form of the fact that the pencil has no canonical member away
from its distinguished endpoint. -/
theorem SerreExtensionPencilSeed.linearCombination_right_one_ne_canonical
    (seed : SerreExtensionPencilSeed e)
    (a b : (SheafOfModules.unit X.ringCatSheaf) ⟶
      (SheafOfModules.unit X.ringCatSheaf)) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombination e seed
      a (𝟙 _) ≠ b ≫ e.inclusion := by
  intro h
  have h' : e.E.unitHomEquiv.symm seed.lift = (b - a) ≫ e.inclusion := by
    have hsub := congrArg (fun z => z - a ≫ e.inclusion) h
    simpa [PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombination,
      Preadditive.comp_add, Preadditive.add_comp] using hsub
  exact
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.liftHom_ne_canonical
      e seed (b - a) h'

/-- A section of `E` whose image in the quotient vanishes comes from a unique
section of `𝒪_X`.  This is exactness at the middle term after taking global
sections. -/
theorem exists_unique_unit_section_of_projection_sections_eq_zero
    (s : e.E.sections)
    (hs : SheafOfModules.sectionsMap e.projection s = zeroSection M) :
    ∃! t : (SheafOfModules.unit X.ringCatSheaf).sections,
      SheafOfModules.sectionsMap e.inclusion t = s := by
  exact e.toSequenceData.exists_unique_unit_section_of_projection_sections_eq_zero s hs

/-- Translate a section of a locally free Serre bundle by a canonical section. -/
noncomputable def translateByCanonicalSection (s : e.E.sections)
    (t : (SheafOfModules.unit X.ringCatSheaf).sections) : e.E.sections :=
  e.toSequenceData.translateByCanonicalSection s t

/-- Canonical translation preserves the quotient section. -/
theorem projection_translateByCanonicalSection (s : e.E.sections)
    (t : (SheafOfModules.unit X.ringCatSheaf).sections) :
    SheafOfModules.sectionsMap e.projection (e.translateByCanonicalSection s t) =
      SheafOfModules.sectionsMap e.projection s := by
  exact e.toSequenceData.projection_translateByCanonicalSection s t

/-- Each fiber of the quotient map on sections of the Serre bundle is a
canonical-section torsor. -/
theorem exists_unique_translateByCanonicalSection_of_projection_eq
    (s r : e.E.sections)
    (h : SheafOfModules.sectionsMap e.projection r =
      SheafOfModules.sectionsMap e.projection s) :
    ∃! t : (SheafOfModules.unit X.ringCatSheaf).sections,
      e.translateByCanonicalSection s t = r := by
  exact e.toSequenceData.exists_unique_translateByCanonicalSection_of_projection_eq s r h

/-- Global sections of a Serre extension are exact at the middle term.

The module-sheaf short exact sequence itself is categorical.  This theorem
records its concrete consequence for the types of global sections: a section
of `E` maps to zero in the twisted ideal quotient exactly when it is a section
of the canonical copy of `𝒪_X`.  The chosen `Zero` structure is deliberately
local to the statement, since Mathlib represents global sections as a type
rather than giving it a global additive structure. -/
theorem sections_exact :
    letI : Zero M.sections := ⟨zeroSection M⟩
    Function.Exact (SheafOfModules.sectionsMap e.inclusion)
      (SheafOfModules.sectionsMap e.projection) := by
  exact e.toSequenceData.sections_exact

/-- If the Serre quotient has no nonzero global sections, the canonical
inclusion identifies the global sections of the bundle with those of the
structure sheaf. -/
theorem inclusion_sections_bijective_of_subsingleton_quotient_sections
    [Subsingleton M.sections] :
    Function.Bijective (SheafOfModules.sectionsMap e.inclusion) := by
  refine ⟨e.inclusion_sections_injective, ?_⟩
  intro s
  have hs : SheafOfModules.sectionsMap e.projection s = zeroSection M :=
    Subsingleton.elim _ _
  obtain ⟨t, ht, -⟩ :=
    e.exists_unique_unit_section_of_projection_sections_eq_zero s hs
  exact ⟨t, ht⟩

/-- Under the same vanishing hypothesis, every global section of the Serre
bundle is uniquely a multiple of the canonical section. -/
theorem exists_unique_unit_section_of_subsingleton_quotient_sections
    [Subsingleton M.sections] (s : e.E.sections) :
    ∃! t : (SheafOfModules.unit X.ringCatSheaf).sections,
      SheafOfModules.sectionsMap e.inclusion t = s := by
  apply e.exists_unique_unit_section_of_projection_sections_eq_zero s
  exact Subsingleton.elim _ _

/-- A nonzero global section of `𝒪_X` remains nonzero in the Serre bundle.
For the projective cubic surface, the constant section supplies the required
nonzero section of `E`. -/
theorem inclusion_sections_ne_zero_of_ne_zero
    {t : (SheafOfModules.unit X.ringCatSheaf).sections}
    (ht : t ≠ zeroSection (SheafOfModules.unit X.ringCatSheaf)) :
    SheafOfModules.sectionsMap e.inclusion t ≠ zeroSection e.E := by
  intro hzero
  apply ht
  apply e.inclusion_sections_injective
  calc
    SheafOfModules.sectionsMap e.inclusion t = zeroSection e.E := hzero
    _ = SheafOfModules.sectionsMap e.inclusion
        (zeroSection (SheafOfModules.unit X.ringCatSheaf)) := e.inclusion_zeroSection.symm

/-- Transport a Serre extension across an isomorphism of its quotient sheaf.

The geometric Serre construction is naturally first obtained with a chosen
presentation of the twisted ideal sheaf.  This lemma replaces that
presentation by any isomorphic quotient without changing the rank-two
bundle or its canonical section.  In particular, it permits the later
construction to use the concrete ideal module of an actual closed finite
subscheme. -/
noncomputable def retarget {N : SheafOfModules.{u} X.ringCatSheaf}
    (qIso : M ≅ N) : SerreExtensionData X N := by
  let S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) := e.complex
  let T : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) :=
    ShortComplex.mk e.inclusion (e.projection ≫ qIso.hom) (by
      calc
        e.inclusion ≫ e.projection ≫ qIso.hom =
            (e.inclusion ≫ e.projection) ≫ qIso.hom := rfl
        _ = 0 ≫ qIso.hom := by rw [e.zero]
        _ = 0 := by simp)
  let a : S ≅ T := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) qIso
    (by simp [S, T]) (by simp [S, T])
  exact
    { E := e.E
      inclusion := e.inclusion
      projection := e.projection ≫ qIso.hom
      zero := by
        calc
          e.inclusion ≫ e.projection ≫ qIso.hom =
              (e.inclusion ≫ e.projection) ≫ qIso.hom := rfl
          _ = 0 ≫ qIso.hom := by rw [e.zero]
          _ = 0 := by simp
      shortExact := by
        change T.ShortExact
        exact ShortComplex.shortExact_of_iso a e.shortExact
      locallyFree := e.locallyFree }

/-- Retargeting transports the canonical `Ext¹` class by the quotient
isomorphism.  Thus a Serre-duality calculation may be performed in any
isomorphic presentation of the twisted ideal sheaf. -/
@[simp]
theorem extensionClass_retarget {N : SheafOfModules.{u} X.ringCatSheaf}
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (qIso : M ≅ N) :
    e.extensionClass =
      (Ext.mk₀ qIso.hom).comp (e.retarget qIso).extensionClass (zero_add 1) := by
  let f : e.complex ⟶ (e.retarget qIso).complex :=
    ShortComplex.homMk (𝟙 _) (𝟙 _) qIso.hom
      (by simp [complex, retarget])
      (by simp [complex, retarget])
  have h := ShortComplex.ShortExact.extClass_naturality e.shortExact
    (e.retarget qIso).shortExact f
  change e.shortExact.extClass.comp
      (Ext.mk₀ (𝟙 (SheafOfModules.unit X.ringCatSheaf))) (add_zero 1) =
    (Ext.mk₀ qIso.hom).comp (e.retarget qIso).shortExact.extClass (zero_add 1) at h
  simpa only [Ext.comp_mk₀_id, extensionClass] using h

/-- A nonzero Serre extension class remains nonzero after replacing its
quotient by an isomorphic ideal-sheaf presentation. -/
theorem extensionClass_retarget_ne_zero {N : SheafOfModules.{u} X.ringCatSheaf}
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (qIso : M ≅ N) (he : e.extensionClass ≠ 0) :
    (e.retarget qIso).extensionClass ≠ 0 := by
  intro hzero
  apply he
  rw [e.extensionClass_retarget qIso, hzero]
  simp

/-- Retargeting preserves exactly whether the Serre extension class vanishes.
The two presentations therefore carry equivalent local nonvanishing
information for the later Serre-duality calculation. -/
theorem extensionClass_retarget_ne_zero_iff {N : SheafOfModules.{u} X.ringCatSheaf}
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (qIso : M ≅ N) :
    (e.retarget qIso).extensionClass ≠ 0 ↔ e.extensionClass ≠ 0 := by
  constructor
  · intro h he
    apply h
    have htransport :
        (Ext.mk₀ qIso.inv).comp e.extensionClass (zero_add 1) =
          (e.retarget qIso).extensionClass := by
      rw [e.extensionClass_retarget qIso, Ext.mk₀_comp_mk₀_assoc]
      simpa using
        (Ext.mk₀_id_comp (e.retarget qIso).extensionClass)
    rw [← htransport, he]
    simp
  · exact e.extensionClass_retarget_ne_zero qIso

/-- Retargeting preserves the locally free middle term literally. -/
theorem retarget_E {N : SheafOfModules.{u} X.ringCatSheaf}
    (qIso : M ≅ N) : (e.retarget qIso).E = e.E := rfl

/-- An extension whose quotient is merely presented by a sheaf isomorphism
can be retargeted to the concrete ideal module of a closed immersion.  This
is the verified interface from an eventual Serre-duality construction to the
actual finite subscheme used in Voisin's residual argument. -/
noncomputable def retargetToClosedImmersion
    {Z : Scheme.{u}} (i : Z ⟶ X)
    (qIso : M ≅ IdealSheafDataModule.closedImmersionModule i) :
    SerreExtensionData X (IdealSheafDataModule.closedImmersionModule i) :=
  e.retarget qIso

/-- The same retargeting bridge applies to the actual quotient in Voisin's
rank-two construction: the ideal sheaf of the finite subscheme, twisted by
the chosen line bundle.  Thus an eventual extension-class construction may
use any equivalent presentation and still produce data whose quotient is
literally `I_Z ⊗ L`. -/
noncomputable def retargetToClosedImmersionIdealTwist
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (L : SheafOfModules.{u} X.ringCatSheaf)
    (qIso : M ≅ closedImmersionIdealTwist i L) :
    SerreExtensionData X (closedImmersionIdealTwist i L) :=
  e.retarget qIso

end SerreExtensionData


namespace SerreExtensionData

variable {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
  (e : SerreExtensionData X M)

/-- The section of the Serre bundle represented by one homogeneous linear
combination in the pencil.  This is the input for the scheme-theoretic zero
locus on each free trivialization of the locally free bundle. -/
noncomputable def SerreExtensionPencilSeed.linearCombinationSection
    (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : e.E.sections :=
  e.E.unitHomEquiv
    (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombination e seed a b)

/-- The Serre-pencil combination after pullback to an auxiliary scheme.  The
unit-comparison witness is the precise sheaf-theoretic datum needed to pull
the two original sections to a parameter chart.  In particular, this gives
the section from which the moving zero scheme on an affine chart of
`X × ℙ¹` is formed. -/
noncomputable def SerreExtensionPencilSeed.pullbackLinearCombinationSection
    {Y : Scheme.{u}} (f : Y ⟶ X)
    (hunit : IsIso (BundleSectionZeroLocus.pullbackUnitComparison f))
    (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit Y.ringCatSheaf ⟶
      SheafOfModules.unit Y.ringCatSheaf) :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj e.E).sections :=
  BundleSectionZeroLocus.addSections (X := Y)
    (BundleSectionZeroLocus.scaleSection a
      (BundleSectionZeroLocus.pullbackSection f e.E hunit e.canonicalSection))
    (BundleSectionZeroLocus.scaleSection b
      (BundleSectionZeroLocus.pullbackSection f e.E hunit seed.lift))

/-- The homogeneous-coordinate scaling identity also holds for the actual
sections of the Serre bundle. -/
theorem SerreExtensionPencilSeed.linearCombinationSection_left_scale
    (seed : SerreExtensionPencilSeed e)
    (c a b : (SheafOfModules.unit X.ringCatSheaf) ⟶
      (SheafOfModules.unit X.ringCatSheaf)) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
      e seed (c ≫ a) (c ≫ b) =
      BundleSectionZeroLocus.scaleSection c
        (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
          e seed a b) := by
  apply e.E.unitHomEquiv.symm.injective
  simp only [SerreExtensionPencilSeed.linearCombinationSection,
    BundleSectionZeroLocus.scaleSection, Equiv.symm_apply_apply]
  exact SerreExtensionPencilSeed.linearCombination_left_scale e seed c a b

/-- The canonical endpoint of the section-valued pencil is precisely the
canonical section of the Serre extension. -/
theorem SerreExtensionPencilSeed.linearCombinationSection_one_zero
    (seed : SerreExtensionPencilSeed e) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
      e seed (𝟙 _) 0 = e.canonicalSection := by
  apply e.E.unitHomEquiv.symm.injective
  rw [SerreExtensionPencilSeed.linearCombinationSection, Equiv.symm_apply_apply]
  rw [SerreExtensionPencilSeed.linearCombination_one_zero]
  change e.inclusion =
    e.E.unitHomEquiv.symm
      (SheafOfModules.sectionsMap e.inclusion
        ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv (𝟙 _)))
  calc
    e.inclusion =
        (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
          ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv (𝟙 _)) ≫
          e.inclusion := by simp
    _ = e.E.unitHomEquiv.symm
      (SheafOfModules.sectionsMap e.inclusion
        ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv (𝟙 _))) :=
      (SheafOfModules.unitHomEquiv_symm_comp _ e.inclusion)

/-- The other distinguished endpoint of the section-valued pencil is the
chosen noncanonical lift. -/
theorem SerreExtensionPencilSeed.linearCombinationSection_zero_one
    (seed : SerreExtensionPencilSeed e) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
      e seed 0 (𝟙 _) = seed.lift := by
  apply e.E.unitHomEquiv.symm.injective
  rw [SerreExtensionPencilSeed.linearCombinationSection, Equiv.symm_apply_apply]
  rw [PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombination]
  simp

/-- Every affine member of the section-valued pencil remains outside the
canonical copy of the structure sheaf.  This carries the earlier morphism
level noncanonicity to the actual sections whose zero schemes are used in
the pencil. -/
theorem SerreExtensionPencilSeed.linearCombinationSection_right_one_ne_canonical
    (seed : SerreExtensionPencilSeed e)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
      e seed a (𝟙 _) ≠
      SheafOfModules.sectionsMap e.inclusion
        ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv b) := by
  intro h
  apply
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombination_right_one_ne_canonical
      e seed a b
  calc
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombination e seed a (𝟙 _) =
        e.E.unitHomEquiv.symm
          (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
            e seed a (𝟙 _)) := (e.E.unitHomEquiv.symm_apply_apply _).symm
    _ = e.E.unitHomEquiv.symm
      (SheafOfModules.sectionsMap e.inclusion
        ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv b)) := by rw [h]
    _ = (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
        ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv b) ≫ e.inclusion :=
      (SheafOfModules.unitHomEquiv_symm_comp _ e.inclusion).symm
    _ = b ≫ e.inclusion := by simp

/-- On a chosen globally free chart for the Serre bundle, the zero locus of a
pencil member is the ideal-defined closed subscheme generated by its scalar
coordinates.  The definition is deliberately chart-level: the next
geometric step is to prove compatibility on overlaps of the local free
charts supplied by `e.locallyFree`. -/
noncomputable def SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso
    (seed : SerreExtensionPencilSeed e) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf) I ≅ e.E)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    AlgebraicGeometry.Scheme.IdealSheafData X :=
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I t
    (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
      e seed a b)

/-- The zero ideal at the canonical endpoint is the zero ideal of the
canonical Serre section in the chosen free chart. -/
theorem SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso_one_zero
    (seed : SerreExtensionPencilSeed e) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf) I ≅ e.E) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso
      e seed I t (𝟙 _) 0 =
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I t e.canonicalSection := by
  rw [SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso,
    SerreExtensionPencilSeed.linearCombinationSection_one_zero]

/-- The other distinguished endpoint has the zero ideal of the chosen lifted
section. -/
theorem SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso_zero_one
    (seed : SerreExtensionPencilSeed e) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf) I ≅ e.E) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso
      e seed I t 0 (𝟙 _) =
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I t seed.lift := by
  rw [SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso,
    SerreExtensionPencilSeed.linearCombinationSection_zero_one]

/-- The chart-level scheme-theoretic zero locus of a member of the Serre
pencil. -/
noncomputable def SerreExtensionPencilSeed.linearCombinationZeroSubschemeOfFreeIso
    (seed : SerreExtensionPencilSeed e) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf) I ≅ e.E)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : Scheme.{u} :=
  (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso
    e seed I t a b).subscheme

/-- The inclusion of the chart-level pencil zero locus into the cubic
surface. -/
noncomputable def SerreExtensionPencilSeed.linearCombinationZeroSubschemeOfFreeIsoι
    (seed : SerreExtensionPencilSeed e) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf) I ≅ e.E)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationZeroSubschemeOfFreeIso
      e seed I t a b ⟶ X :=
  (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso
    e seed I t a b).subschemeι

/-- On an affine free chart, multiplying both homogeneous coefficients by an
invertible scalar leaves the Serre-pencil zero ideal unchanged. -/
theorem SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso_left_scale_eq
    [AlgebraicGeometry.IsAffine X] (seed : SerreExtensionPencilSeed e)
    (I : Type u) (t : SheafOfModules.free (R := X.ringCatSheaf) I ≅ e.E)
    (c a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) [IsIso c] :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso
      e seed I t (c ≫ a) (c ≫ b) =
      PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso
        e seed I t a b := by
  rw [SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso,
    SerreExtensionPencilSeed.linearCombinationSection_left_scale]
  exact BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_scaleSection_eq_of_isIso I t c _

/-- The preceding homogeneous-coordinate scaling identity also identifies
the chart-level Serre-pencil zero subschemes. -/
theorem SerreExtensionPencilSeed.linearCombinationZeroSubschemeOfFreeIso_left_scale_eq
    [AlgebraicGeometry.IsAffine X] (seed : SerreExtensionPencilSeed e)
    (I : Type u) (t : SheafOfModules.free (R := X.ringCatSheaf) I ≅ e.E)
    (c a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) [IsIso c] :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationZeroSubschemeOfFreeIso
      e seed I t (c ≫ a) (c ≫ b) =
      PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationZeroSubschemeOfFreeIso
        e seed I t a b := by
  rw [SerreExtensionPencilSeed.linearCombinationZeroSubschemeOfFreeIso,
    SerreExtensionPencilSeed.linearCombinationZeroSubschemeOfFreeIso,
    SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso_left_scale_eq
      e seed I t c a b]

/-- Each chart-level zero locus of a pencil member is a genuine closed
subscheme, not just a set of points. -/
theorem SerreExtensionPencilSeed.isClosedImmersion_linearCombinationZeroSubschemeOfFreeIsoι
    (seed : SerreExtensionPencilSeed e) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf) I ≅ e.E)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsClosedImmersion
      (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationZeroSubschemeOfFreeIsoι
        e seed I t a b) := by
  change IsClosedImmersion
    (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso
      e seed I t a b).subschemeι
  infer_instance


/-- On an affine chart, a finite free change of basis leaves the Serre
pencil's scheme-theoretic zero ideal unchanged.  This discharges the
coordinate-overlap condition for rank-two trivializations. -/
theorem SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso_eq_of_finiteFreeIso
    [AlgebraicGeometry.IsAffine X] (seed : SerreExtensionPencilSeed e)
    (I J : Type u) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (t : SheafOfModules.free (R := X.ringCatSheaf) I ≅ e.E)
    (v : SheafOfModules.free (R := X.ringCatSheaf) J ≅ e.E)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso
      e seed I t a b =
      PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso
        e seed J v a b := by
  unfold SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso
  exact BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_eq_of_finiteFreeIso I J t v _

/-- The resulting finite-free chart zero schemes agree under a change of
trivialization. -/
theorem SerreExtensionPencilSeed.linearCombinationZeroSubschemeOfFreeIso_eq_of_finiteFreeIso
    [AlgebraicGeometry.IsAffine X] (seed : SerreExtensionPencilSeed e)
    (I J : Type u) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (t : SheafOfModules.free (R := X.ringCatSheaf) I ≅ e.E)
    (v : SheafOfModules.free (R := X.ringCatSheaf) J ≅ e.E)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationZeroSubschemeOfFreeIso
      e seed I t a b =
      PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationZeroSubschemeOfFreeIso
        e seed J v a b := by
  rw [SerreExtensionPencilSeed.linearCombinationZeroSubschemeOfFreeIso,
    SerreExtensionPencilSeed.linearCombinationZeroSubschemeOfFreeIso,
    SerreExtensionPencilSeed.linearCombinationZeroIdealOfFreeIso_eq_of_finiteFreeIso
      e seed I J t v a b]


/-- On an open trivialization of the Serre bundle, a pencil member has the
literal ideal-defined zero locus of its restricted section. -/
noncomputable def SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
    (seed : SerreExtensionPencilSeed e) (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    AlgebraicGeometry.Scheme.IdealSheafData (U : Scheme.{u}) :=
  BundleSectionZeroLocus.localSectionZeroIdealOfOver U I t
    (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
      e seed a b)

/-- The canonical parameter on every free open chart has the restricted
canonical Serre section as its zero-locus section. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_one_zero
    (seed : SerreExtensionPencilSeed e) (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
      e seed U I t (𝟙 _) 0 =
      BundleSectionZeroLocus.localSectionZeroIdealOfOver U I t e.canonicalSection := by
  rw [SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver,
    SerreExtensionPencilSeed.linearCombinationSection_one_zero]

/-- The second distinguished parameter on a free open chart gives the zero
ideal of the chosen lifted Serre section. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_zero_one
    (seed : SerreExtensionPencilSeed e) (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
      e seed U I t 0 (𝟙 _) =
      BundleSectionZeroLocus.localSectionZeroIdealOfOver U I t seed.lift := by
  rw [SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver,
    SerreExtensionPencilSeed.linearCombinationSection_zero_one]

/-- Finite free rank-two charts define the same local zero ideal for a fixed
pencil member. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_eq_of_finiteFreeIso
    (seed : SerreExtensionPencilSeed e) (U : X.Opens)
    [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (I J : Type u) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (v : SheafOfModules.free (R := X.ringCatSheaf.over U) J ≅ e.E.over U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
      e seed U I t a b =
      PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
        e seed U J v a b := by
  unfold SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
  exact BundleSectionZeroLocus.localSectionZeroIdealOfOver_eq_of_finiteFreeIso U I J t v _

/-- The local zero scheme of a Serre-pencil member on a free chart. -/
noncomputable def SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
    (seed : SerreExtensionPencilSeed e) (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : Scheme.{u} :=
  BundleSectionZeroLocus.localSectionZeroSubschemeOfOver U I t
    (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
      e seed a b)

/-- On an affine Serre trivialization, the local zero ideal is unchanged
when the two homogeneous coefficients are multiplied by a scalar whose
restriction is invertible.  The compatibility hypothesis records exactly the
identification between the restricted global scalar and the local unit. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_left_scale_eq
    (seed : SerreExtensionPencilSeed e) (U : X.Opens)
    [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (c a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (d : SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf ⟶
      SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) [IsIso d]
    (hcompat : BundleSectionZeroLocus.restrictSectionToOpen (X := X) U
      (BundleSectionZeroLocus.scaleSection (X := X) c
        (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
          e seed a b)) =
        BundleSectionZeroLocus.scaleSection (X := (U : Scheme.{u})) d
          (BundleSectionZeroLocus.restrictSectionToOpen (X := X) U
            (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
              e seed a b))) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
      e seed U I t (c ≫ a) (c ≫ b) =
      PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
        e seed U I t a b := by
  rw [SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver,
    SerreExtensionPencilSeed.linearCombinationSection_left_scale]
  exact BundleSectionZeroLocus.localSectionZeroIdealOfOver_scaleSection_eq_of_localCompatibility
    U I t c d _ hcompat

/-- The preceding local homogeneous-coordinate identity also identifies the
ideal-defined zero schemes on that affine trivialization. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver_left_scale_eq
    (seed : SerreExtensionPencilSeed e) (U : X.Opens)
    [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (c a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (d : SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf ⟶
      SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) [IsIso d]
    (hcompat : BundleSectionZeroLocus.restrictSectionToOpen (X := X) U
      (BundleSectionZeroLocus.scaleSection (X := X) c
        (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
          e seed a b)) =
        BundleSectionZeroLocus.scaleSection (X := (U : Scheme.{u})) d
          (BundleSectionZeroLocus.restrictSectionToOpen (X := X) U
            (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
              e seed a b))) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
      e seed U I t (c ≫ a) (c ≫ b) =
      PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
        e seed U I t a b := by
  unfold SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
    BundleSectionZeroLocus.localSectionZeroSubschemeOfOver
  exact congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme
    (SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_left_scale_eq
      e seed U I t c a b d hcompat)

/-- The precise coherence needed to compare a pencil section on two nested
open charts through their canonical module identification. -/
def SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible
    (seed : SerreExtensionPencilSeed e) {U V : X.Opens} (f : V ⟶ U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : Prop :=
  SheafOfModules.sectionsMap
    (BundleSectionZeroLocus.localRestrictionTargetIso (E := e.E) f).inv
    (BundleSectionZeroLocus.restrictModuleSection (X.homOfLE (leOfHom f))
      ((AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.obj (e.E.over U))
      (BundleSectionZeroLocus.restrictSectionToOpen (X := X) U
        (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
          e seed a b))) =
    BundleSectionZeroLocus.restrictSectionToOpen (X := X) V
      (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
        e seed a b)

/-- The chart-unit coherence supplies restriction compatibility simultaneously
for every member of the Serre pencil. -/
theorem SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible_of_unit
    (seed : SerreExtensionPencilSeed e) {U V : X.Opens} (f : V ⟶ U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hunit : BundleSectionZeroLocus.localRestrictionUnitCompatible f) :
    SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible
      e seed f a b := by
  unfold SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible
  exact BundleSectionZeroLocus.localRestrictionTargetIso_sectionCompatibility_of_unit
    f hunit _

/-- The pencil section compatibility is already implied by the reduced
structure-sheaf comparison; the strictly identity over-site factor need not
be retained in later Serre calculations. -/
theorem SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible_of_core
    (seed : SerreExtensionPencilSeed e) {U V : X.Opens} (f : V ⟶ U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hcore :
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso
        (X.homOfLE (leOfHom f))).symm.hom ≫
        (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).inv.app
          ((SheafOfModules.unit X.ringCatSheaf).over U) = 𝟙 _) :
    SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible
      e seed f a b := by
  unfold SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible
  exact BundleSectionZeroLocus.localRestrictionTargetIso_sectionCompatibility_of_core
    f hcore _

/-- Every Serre-pencil member has canonically compatible restrictions on
nested charts. -/
theorem SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible_proof
    (seed : SerreExtensionPencilSeed e) {U V : X.Opens} (f : V ⟶ U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible
      e seed f a b := by
  unfold SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible
  exact BundleSectionZeroLocus.localRestrictionTargetIso_sectionCompatibility f _

/-- Once restriction of the pencil section is identified through the
canonical chart-module isomorphism, its local zero ideal commutes with
pullback to a nested affine chart. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_comap_eq_restrictFreeIsoOver
    (seed : SerreExtensionPencilSeed e) {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hsection : SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible
      e seed f a b) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
        e seed U I t a b)
      (X.homOfLE (leOfHom f)) =
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
      e seed V I (BundleSectionZeroLocus.restrictFreeIsoOver (X := X) f I t) a b := by
  unfold SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
  exact BundleSectionZeroLocus.localSectionZeroIdealOfOver_comap_eq_restrictFreeIsoOver_of_sectionCompatibility
      f I t _ (by simpa only [SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible]
        using hsection)

/-- Once the unit-object chart coherence holds, every member of the Serre
pencil has a local zero ideal compatible with nested affine restriction. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_comap_eq_restrictFreeIsoOver_of_unit
    (seed : SerreExtensionPencilSeed e) {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hunit : BundleSectionZeroLocus.localRestrictionUnitCompatible f) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
        e seed U I t a b)
      (X.homOfLE (leOfHom f)) =
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
      e seed V I (BundleSectionZeroLocus.restrictFreeIsoOver (X := X) f I t) a b := by
  exact SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_comap_eq_restrictFreeIsoOver
    e seed f I t a b
    (SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible_of_unit
      e seed f a b hunit)

/-- The local zero-ideal pullback formula for a pencil member with the
remaining chart condition reduced to the one core unit comparison. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_comap_eq_restrictFreeIsoOver_of_core
    (seed : SerreExtensionPencilSeed e) {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hcore :
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso
        (X.homOfLE (leOfHom f))).symm.hom ≫
        (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).inv.app
          ((SheafOfModules.unit X.ringCatSheaf).over U) = 𝟙 _) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
        e seed U I t a b)
      (X.homOfLE (leOfHom f)) =
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
      e seed V I (BundleSectionZeroLocus.restrictFreeIsoOver (X := X) f I t) a b := by
  exact SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_comap_eq_restrictFreeIsoOver
    e seed f I t a b
    (SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible_of_core
      e seed f a b hcore)

/-- The local zero ideal of every Serre-pencil member pulls back canonically
to each nested affine chart. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_comap_eq_restrictFreeIsoOver_canonical
    (seed : SerreExtensionPencilSeed e) {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
        e seed U I t a b)
      (X.homOfLE (leOfHom f)) =
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
      e seed V I (BundleSectionZeroLocus.restrictFreeIsoOver (X := X) f I t) a b := by
  exact SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_comap_eq_restrictFreeIsoOver
    e seed f I t a b
    (SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible_proof
      e seed f a b)

/-- The associated local closed zero subschemes have the same nested-chart
pullback compatibility. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver_comap_eq_restrictFreeIsoOver
    (seed : SerreExtensionPencilSeed e) {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hsection : SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible
      e seed f a b) :
    (AlgebraicGeometry.Scheme.IdealSheafData.comap
      (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
        e seed U I t a b)
      (X.homOfLE (leOfHom f))).subscheme =
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
      e seed V I (BundleSectionZeroLocus.restrictFreeIsoOver (X := X) f I t) a b := by
  unfold SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
    BundleSectionZeroLocus.localSectionZeroSubschemeOfOver
  exact congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme
    (SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_comap_eq_restrictFreeIsoOver
      e seed f I t a b hsection)

/-- The nested-chart pullback formula for local Serre-pencil zero schemes
follows uniformly for every pencil member from the unit-object coherence. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver_comap_eq_restrictFreeIsoOver_of_unit
    (seed : SerreExtensionPencilSeed e) {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hunit : BundleSectionZeroLocus.localRestrictionUnitCompatible f) :
    (AlgebraicGeometry.Scheme.IdealSheafData.comap
      (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
        e seed U I t a b)
      (X.homOfLE (leOfHom f))).subscheme =
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
      e seed V I (BundleSectionZeroLocus.restrictFreeIsoOver (X := X) f I t) a b := by
  exact SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver_comap_eq_restrictFreeIsoOver
    e seed f I t a b
    (SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible_of_unit
      e seed f a b hunit)

/-- The corresponding local closed zero subschemes commute with pullback
under the reduced core unit comparison. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver_comap_eq_restrictFreeIsoOver_of_core
    (seed : SerreExtensionPencilSeed e) {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hcore :
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso
        (X.homOfLE (leOfHom f))).symm.hom ≫
        (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv f).inv.app
          ((SheafOfModules.unit X.ringCatSheaf).over U) = 𝟙 _) :
    (AlgebraicGeometry.Scheme.IdealSheafData.comap
      (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
        e seed U I t a b)
      (X.homOfLE (leOfHom f))).subscheme =
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
      e seed V I (BundleSectionZeroLocus.restrictFreeIsoOver (X := X) f I t) a b := by
  exact SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver_comap_eq_restrictFreeIsoOver
    e seed f I t a b
    (SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible_of_core
      e seed f a b hcore)

/-- The local zero subscheme of every Serre-pencil member pulls back
canonically to each nested affine chart. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver_comap_eq_restrictFreeIsoOver_canonical
    (seed : SerreExtensionPencilSeed e) {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (U : Scheme.{u})]
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    (I : Type u) [Fintype I] [DecidableEq I]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (AlgebraicGeometry.Scheme.IdealSheafData.comap
      (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
        e seed U I t a b)
      (X.homOfLE (leOfHom f))).subscheme =
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
      e seed V I (BundleSectionZeroLocus.restrictFreeIsoOver (X := X) f I t) a b := by
  exact SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver_comap_eq_restrictFreeIsoOver
    e seed f I t a b
    (SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible_proof
      e seed f a b)

/-- Its canonical closed immersion into the corresponding open subscheme. -/
noncomputable def SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOverι
    (seed : SerreExtensionPencilSeed e) (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
      e seed U I t a b ⟶ (U : Scheme.{u}) :=
  BundleSectionZeroLocus.localSectionZeroSubschemeOfOverι U I t
    (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationSection
      e seed a b)

/-- Each local Serre-pencil zero locus is a genuine closed subscheme. -/
theorem SerreExtensionPencilSeed.isClosedImmersion_linearCombinationLocalZeroSubschemeOfOverι
    (seed : SerreExtensionPencilSeed e) (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsClosedImmersion
      (PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOverι
        e seed U I t a b) := by
  exact BundleSectionZeroLocus.isClosedImmersion_localSectionZeroSubschemeOfOverι U I t _

/-- The local closed scheme at the canonical endpoint is the zero scheme of
its canonical section. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver_one_zero
    (seed : SerreExtensionPencilSeed e) (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
      e seed U I t (𝟙 _) 0 =
      BundleSectionZeroLocus.localSectionZeroSubschemeOfOver U I t e.canonicalSection := by
  unfold SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
  rw [SerreExtensionPencilSeed.linearCombinationSection_one_zero]

/-- The other endpoint local closed scheme is the zero scheme of the chosen
noncanonical lift. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver_zero_one
    (seed : SerreExtensionPencilSeed e) (U : X.Opens) (I : Type u)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
      e seed U I t 0 (𝟙 _) =
      BundleSectionZeroLocus.localSectionZeroSubschemeOfOver U I t seed.lift := by
  unfold SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
  rw [SerreExtensionPencilSeed.linearCombinationSection_zero_one]


/-- Restricting a finite free trivialization along an affine open inclusion
produces the same local zero ideal as any finite free trivialization on the
smaller chart.  Thus the local Serre-pencil zero ideals satisfy the overlap
identity required for gluing. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_restrictFreeIsoOver_eq
    (seed : SerreExtensionPencilSeed e) {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    (I J : Type u) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (v : SheafOfModules.free (R := X.ringCatSheaf.over V) J ≅ e.E.over V)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
      e seed V I (BundleSectionZeroLocus.restrictFreeIsoOver (X := X) f I t) a b =
      PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
        e seed V J v a b := by
  unfold SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver
  exact BundleSectionZeroLocus.localSectionZeroIdealOfOver_restrictFreeIsoOver_eq
    f I J t v _

/-- The corresponding local closed subschemes agree on affine overlaps. -/
theorem SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver_restrictFreeIsoOver_eq
    (seed : SerreExtensionPencilSeed e) {U V : X.Opens} (f : V ⟶ U)
    [AlgebraicGeometry.IsAffine (V : Scheme.{u})]
    (I J : Type u) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ e.E.over U)
    (v : SheafOfModules.free (R := X.ringCatSheaf.over V) J ≅ e.E.over V)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
      e seed V I (BundleSectionZeroLocus.restrictFreeIsoOver (X := X) f I t) a b =
      PfaffianDescent.SerreExtensionData.SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
        e seed V J v a b := by
  unfold SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver
  exact BundleSectionZeroLocus.localSectionZeroSubschemeOfOver_restrictFreeIsoOver_eq
    f I J t v _


structure SerreExtensionRankTwoAffineCover where
  ι : Type u
  U : ι → X.Opens
  covers : ⨆ i, U i = ⊤
  affine : ∀ i, AlgebraicGeometry.IsAffine (U i : Scheme.{u})
  overlapAffine : ∀ i j, AlgebraicGeometry.IsAffine ((U i ⊓ U j : X.Opens) : Scheme.{u})
  trivialization : ∀ i,
    SheafOfModules.free (R := X.ringCatSheaf.over (U i)) (ULift.{u} (Fin 2)) ≅ e.E.over (U i)


/-- The affine trivializations of a Serre extension form an actual
scheme-theoretic open cover.  This exposes the cover underlying the local
zero-locus calculations, so it can be pulled back to the projective-line
parameter space of the pencil. -/
noncomputable def SerreExtensionRankTwoAffineCover.openCover
    (C : SerreExtensionRankTwoAffineCover e) : X.OpenCover where
  I₀ := C.ι
  X i := C.U i
  f i := (C.U i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun _ ↦ inferInstance⟩
    intro x
    have hx : x ∈ ⨆ i, C.U i := by rw [C.covers]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨i, hxi⟩ := hx
    exact ⟨i, ⟨x, hxi⟩, rfl⟩


/-- Pointwise affine rank-two trivializations assemble into an affine cover.
The affine-diagonal hypothesis makes pairwise intersections affine, so this
cover is immediately usable for the overlap calculations of the pencil. -/
noncomputable def SerreExtensionRankTwoAffineCover.ofPointwise
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (U : X → X.Opens) (hU : ∀ x, x ∈ U x)
    (haffine : ∀ x, AlgebraicGeometry.IsAffine (U x : Scheme.{u}))
    (t : ∀ x, SheafOfModules.free (R := X.ringCatSheaf.over (U x))
      (ULift.{u} (Fin 2)) ≅ e.E.over (U x)) :
    SerreExtensionRankTwoAffineCover e where
  ι := X
  U := U
  covers := by
    apply le_antisymm le_top
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨x, hU x⟩
  affine := haffine
  overlapAffine := by
    intro x y
    exact IsAffineOpen.inf (haffine x) (haffine y)
  trivialization := t


/-- The displayed affine rank-two trivializations are a genuine local-free
cover of the Serre bundle. -/
theorem SerreExtensionRankTwoAffineCover.isLocallyFree
    (C : SerreExtensionRankTwoAffineCover e) : e.E.IsLocallyFree := by
  apply sheaf_isLocallyFree_of_coverIso X.ringCatSheaf e.E C.U ?_
    (fun _ => ULift.{u} (Fin 2)) C.trivialization
  exact (Opens.coversTop_iff _ _).mpr (by
    apply TopologicalSpace.IsOpenCover.mk
    simp [C.covers])

noncomputable def SerreExtensionRankTwoAffineCover.overlapToLeft
    (C : SerreExtensionRankTwoAffineCover e) (i j : C.ι) : C.U i ⊓ C.U j ⟶ C.U i :=
  homOfLE inf_le_left

noncomputable def SerreExtensionRankTwoAffineCover.overlapToRight
    (C : SerreExtensionRankTwoAffineCover e) (i j : C.ι) : C.U i ⊓ C.U j ⟶ C.U j :=
  homOfLE inf_le_right

noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroIdeal
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    AlgebraicGeometry.Scheme.IdealSheafData (C.U i : Scheme.{u}) :=
  SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver e seed (C.U i) (ULift.{u} (Fin 2))
    (C.trivialization i) a b

/-- On every affine trivialization, the canonical endpoint of the Serre
pencil is literally the zero ideal of the canonical Serre section.  This is
the endpoint identification needed when the locally glued pencil is compared
with the original finite subscheme. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_one_zero
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι) :
    SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i (𝟙 _) 0 =
      BundleSectionZeroLocus.localSectionZeroIdealOfOver (C.U i) (ULift.{u} (Fin 2))
        (C.trivialization i) e.canonicalSection := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroIdeal
  exact SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_one_zero
    e seed (C.U i) (ULift.{u} (Fin 2)) (C.trivialization i)

/-- On every affine trivialization, the second marked endpoint is literally
the zero ideal of the selected lifted section. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_zero_one
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι) :
    SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i 0 (𝟙 _) =
      BundleSectionZeroLocus.localSectionZeroIdealOfOver (C.U i) (ULift.{u} (Fin 2))
        (C.trivialization i) seed.lift := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroIdeal
  exact SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_zero_one
    e seed (C.U i) (ULift.{u} (Fin 2)) (C.trivialization i)

/-- The local zero ideal on an affine chart, viewed as an ideal sheaf of the
ambient scheme through the chart's open immersion.  Its restriction back to
the chart is proved below, so this gives a concrete ambient extension of each
member of the Serre pencil before the chart extensions are glued. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension
    [QuasiSeparatedSpace X]
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : X.IdealSheafData :=
  AllCharacteristics.openKernelExtension
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b)
    (C.U i).ι

/-- Restricting the ambient extension of a chart zero ideal recovers exactly
the original ideal.  Affineness of the chart and quasi-separatedness of the
ambient scheme supply the required quasi-compactness automatically. -/
theorem SerreExtensionRankTwoAffineCover.comap_localPencilZeroIdealExtension
    [QuasiSeparatedSpace X]
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed i a b).comap
      (C.U i).ι =
      SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b := by
  let _ : AlgebraicGeometry.IsAffine (C.U i : Scheme.{u}) := C.affine i
  exact AllCharacteristics.idealSheafData_comap_ker_subscheme_comp_open_of_isAffine
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b) (C.U i).ι

/-- Restricting an ambient kernel extension to any smaller open inside its
chart is the same as first recovering the chart ideal and then restricting
that ideal.  This records the full functorial form of the chart calculation
used in overlap and gluing arguments. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension_comap_of_le
    [QuasiSeparatedSpace X]
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι) (V : X.Opens) (hV : V ≤ C.U i)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed i a b).comap V.ι =
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE hV) := by
  calc
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed i a b).comap V.ι =
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed i a b).comap
        (X.homOfLE hV ≫ (C.U i).ι) := by rw [X.homOfLE_ι]
    _ = ((SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed i a b).comap
        (C.U i).ι).comap (X.homOfLE hV) := by
      rw [Scheme.IdealSheafData.comap_comp]
    _ = (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE hV) := by
      rw [SerreExtensionRankTwoAffineCover.comap_localPencilZeroIdealExtension]

/-- The closed subscheme of the `i`-th affine chart cut out by a member of
Voisin's Serre pencil. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroSubscheme
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : Scheme.{u} :=
  SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver e seed (C.U i)
    (ULift.{u} (Fin 2)) (C.trivialization i) a b

/-- The local zero scheme at the canonical marked point of the pencil is the
ordinary zero scheme of the canonical Serre section. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroSubscheme_one_zero
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι) :
    SerreExtensionRankTwoAffineCover.localPencilZeroSubscheme e C seed i (𝟙 _) 0 =
      BundleSectionZeroLocus.localSectionZeroSubschemeOfOver (C.U i) (ULift.{u} (Fin 2))
        (C.trivialization i) e.canonicalSection := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroSubscheme
  exact SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver_one_zero
    e seed (C.U i) (ULift.{u} (Fin 2)) (C.trivialization i)

/-- The local zero scheme at the other marked point is the ordinary zero
scheme of the selected lift. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroSubscheme_zero_one
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι) :
    SerreExtensionRankTwoAffineCover.localPencilZeroSubscheme e C seed i 0 (𝟙 _) =
      BundleSectionZeroLocus.localSectionZeroSubschemeOfOver (C.U i) (ULift.{u} (Fin 2))
        (C.trivialization i) seed.lift := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroSubscheme
  exact SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver_zero_one
    e seed (C.U i) (ULift.{u} (Fin 2)) (C.trivialization i)

/-- The local zero locus, regarded as a closed subscheme of the whole
ambient surface by taking the kernel extension through its affine chart.
This gives an actual ambient closed immersion for every member of the Serre
pencil; the next gluing step only has to identify these ambient models. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroSubschemeExtension
    [QuasiSeparatedSpace X]
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : Scheme.{u} :=
  (SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed i a b).subscheme

/-- The ambient model of a local Serre-pencil zero locus is a closed
subscheme of the ambient surface. -/
theorem SerreExtensionRankTwoAffineCover.isClosedImmersion_localPencilZeroSubschemeExtensionι
    [QuasiSeparatedSpace X]
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsClosedImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed i a b).subschemeι := by
  infer_instance

/-- Pulling the ambient local model back to its defining chart recovers the
original chart zero locus.  The assertion is stated at the level of schemes,
so it can be used directly when the local closed immersions are glued. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroSubschemeExtension_comap_eq
    [QuasiSeparatedSpace X]
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    ((SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed i a b).comap
      (C.U i).ι).subscheme =
      SerreExtensionRankTwoAffineCover.localPencilZeroSubscheme e C seed i a b := by
  change
    ((SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed i a b).comap
      (C.U i).ι).subscheme =
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subscheme
  rw [SerreExtensionRankTwoAffineCover.comap_localPencilZeroIdealExtension]

theorem SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_overlap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver e seed (C.U i ⊓ C.U j)
      (ULift.{u} (Fin 2)) (BundleSectionZeroLocus.restrictFreeIsoOver
        (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j) (ULift.{u} (Fin 2)) (C.trivialization i)) a b =
    SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver e seed (C.U i ⊓ C.U j)
      (ULift.{u} (Fin 2)) (BundleSectionZeroLocus.restrictFreeIsoOver
        (SerreExtensionRankTwoAffineCover.overlapToRight e C i j) (ULift.{u} (Fin 2)) (C.trivialization j)) a b := by
  haveI : AlgebraicGeometry.IsAffine ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) :=
    C.overlapAffine i j
  exact SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_restrictFreeIsoOver_eq
    e seed (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j) (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) (C.trivialization i)
    (BundleSectionZeroLocus.restrictFreeIsoOver
      (SerreExtensionRankTwoAffineCover.overlapToRight e C i j) (ULift.{u} (Fin 2)) (C.trivialization j)) a b

/-- If the section restriction coherences hold on the two inclusions into an
overlap, the two chart zero ideals have literally equal pullbacks there. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hleft : SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible
      e seed (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j) a b)
    (hright : SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible
      e seed (SerreExtensionRankTwoAffineCover.overlapToRight e C i j) a b) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U i : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j))) =
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U j : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToRight e C i j))) := by
  haveI : AlgebraicGeometry.IsAffine ((C.U i : X.Opens) : Scheme.{u}) := C.affine i
  haveI : AlgebraicGeometry.IsAffine ((C.U j : X.Opens) : Scheme.{u}) := C.affine j
  haveI : AlgebraicGeometry.IsAffine ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) :=
    C.overlapAffine i j
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroIdeal
  rw [SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_comap_eq_restrictFreeIsoOver
      e seed (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j)
      (ULift.{u} (Fin 2)) (C.trivialization i) a b hleft,
    SerreExtensionPencilSeed.linearCombinationLocalZeroIdealOfOver_comap_eq_restrictFreeIsoOver
      e seed (SerreExtensionRankTwoAffineCover.overlapToRight e C i j)
      (ULift.{u} (Fin 2)) (C.trivialization j) a b hright]
  exact SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_overlap e C seed i j a b

/-- One canonical unit-object coherence for each inclusion into an affine
overlap gives literal equality of the two pulled-back Serre-pencil ideals. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap_of_unit
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hleft : BundleSectionZeroLocus.localRestrictionUnitCompatible
      (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j))
    (hright : BundleSectionZeroLocus.localRestrictionUnitCompatible
      (SerreExtensionRankTwoAffineCover.overlapToRight e C i j)) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U i : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j))) =
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U j : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToRight e C i j))) := by
  apply SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap
    e C seed i j a b
  · exact SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible_of_unit
      e seed (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j) a b hleft
  · exact SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible_of_unit
      e seed (SerreExtensionRankTwoAffineCover.overlapToRight e C i j) a b hright

/-- The affine-overlap identity for the local Serre-pencil ideals with both
section coherences reduced to the one remaining core unit comparison. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap_of_core
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hleft :
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso
        (X.homOfLE (leOfHom
          (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j)))).symm.hom ≫
        (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv
          (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j)).inv.app
          ((SheafOfModules.unit X.ringCatSheaf).over (C.U i)) = 𝟙 _)
    (hright :
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso
        (X.homOfLE (leOfHom
          (SerreExtensionRankTwoAffineCover.overlapToRight e C i j)))).symm.hom ≫
        (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv
          (SerreExtensionRankTwoAffineCover.overlapToRight e C i j)).inv.app
          ((SheafOfModules.unit X.ringCatSheaf).over (C.U j)) = 𝟙 _) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U i : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j))) =
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U j : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToRight e C i j))) := by
  apply SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap
    e C seed i j a b
  · exact SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible_of_core
      e seed (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j) a b hleft
  · exact SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible_of_core
      e seed (SerreExtensionRankTwoAffineCover.overlapToRight e C i j) a b hright

/-- The zero ideals of every Serre-pencil member have literally equal
pullbacks to each affine overlap of a rank-two trivializing cover. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap_canonical
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U i : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j))) =
    AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U j : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToRight e C i j))) := by
  apply SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap
    e C seed i j a b
  · exact SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible_proof
      e seed (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j) a b
  · exact SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible_proof
      e seed (SerreExtensionRankTwoAffineCover.overlapToRight e C i j) a b

/-- Transporting equal ideal data through their associated subschemes
commutes with the closed immersion into the ambient scheme. -/
theorem idealSheafData_eqToIso_subschemeι
    {Y : Scheme.{u}} (I J : Y.IdealSheafData) (h : I = J) :
    (eqToIso (congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme h)).hom ≫
      J.subschemeι = I.subschemeι := by
  subst J
  simp

/-- Equality of ideal sheaves is compatible with the canonical maps from
their pullback subschemes.  This is the naturality square used to transport
pairwise overlap equalities through a further chart restriction. -/
theorem idealSheafData_eqToIso_comapSubschemeι
    {W Y : Scheme.{u}} (I J : Y.IdealSheafData) (f : W ⟶ Y) (h : I = J) :
    (eqToIso (congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme
      (congrArg (fun L : Y.IdealSheafData => L.comap f) h))).hom ≫
      ((J.comapIso f).hom ≫ pullback.snd f J.subschemeι) =
    ((I.comapIso f).hom ≫ pullback.snd f I.subschemeι) ≫
      (eqToIso (congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme h)).hom := by
  subst J
  simp

/-- Transporting a successive closed-subsheme restriction across an equality
of pairwise ideals agrees with transporting the resulting triple ideal. -/
theorem successiveComapTransition
    {A B : Scheme.{u}} (P Q : B.IdealSheafData) (g : A ⟶ B)
    (J : A.IdealSheafData) (hJ : J = P.comap g) (hPQ : P = Q) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme hJ)).hom ≫
      (P.comapIso g).hom ≫ pullback.snd g P.subschemeι ≫
        (eqToIso (congrArg Scheme.IdealSheafData.subscheme hPQ)).hom ≫ Q.subschemeι =
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme
      (hJ.trans (congrArg (fun L => L.comap g) hPQ)))).hom ≫
      (Q.comapIso g).hom ≫ pullback.snd g Q.subschemeι ≫ Q.subschemeι := by
  subst Q
  simp

/-- The canonical map from a pulled-back closed subscheme to its ambient
scheme is the pullback projection followed by the original closed immersion. -/
@[reassoc]
theorem comapSubschemeMap_to_ambient
    {A B : Scheme.{u}} (K : B.IdealSheafData) (h : A ⟶ B) :
    (K.comapIso h).hom ≫ pullback.snd h K.subschemeι ≫ K.subschemeι =
      (K.comap h).subschemeι ≫ h := by
  rw [← pullback.condition]
  rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc]

/-- The part of the `i`-th local zero locus lying over the overlap with the
`j`-th chart.  It is expressed as the subscheme of the pulled-back ideal so
that it has a canonical map to the `i`-th local zero locus. -/
noncomputable abbrev SerreExtensionRankTwoAffineCover.localPencilZeroOverlap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : Scheme.{u} :=
  ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
    (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).subscheme

/-- The same chart overlap, expressed from the right local zero locus while
keeping the ambient open `Uᵢ ∩ Uⱼ` fixed. -/
noncomputable abbrev SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRight
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : Scheme.{u} :=
  ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).comap
    (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right))).subscheme

/-- The overlap is an open subscheme of the zero locus on its left chart. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlap e C seed i j a b ⟶
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subscheme :=
  ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comapIso
    (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).hom ≫
    pullback.snd _ _

/-- The overlap written from the right chart is likewise open in that local
zero locus. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRight e C seed i j a b ⟶
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).subscheme :=
  ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).comapIso
    (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right))).hom ≫
    pullback.snd _ _

/-- Restriction of the left local zero locus to a chart overlap is an open
immersion. -/
theorem SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroOverlapι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b) := by
  let f : ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left)
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  change IsOpenImmersion ((I.comapIso f).hom ≫ pullback.snd f I.subschemeι)
  letI : IsOpenImmersion f := inferInstance
  letI : IsOpenImmersion (pullback.snd f I.subschemeι) := inferInstance
  infer_instance

/-- Every restriction of a local Serre-pencil zero locus to a chart overlap is
a monomorphism.  Registering this consequence lets the categorical gluing
construction use the overlap maps directly. -/
instance SerreExtensionRankTwoAffineCover.mono_localPencilZeroOverlapι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    Mono (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b) :=
  (SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroOverlapι
    e C seed i j a b).mono

/-- The right-hand presentation of the chart overlap is open in its local
zero locus as well. -/
theorem SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroOverlapRightι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightι e C seed i j a b) := by
  let f : ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) ⟶
      ((C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right)
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b
  change IsOpenImmersion ((I.comapIso f).hom ≫ pullback.snd f I.subschemeι)
  letI : IsOpenImmersion f := inferInstance
  letI : IsOpenImmersion (pullback.snd f I.subschemeι) := inferInstance
  infer_instance

/-- The open overlap map is compatible with the two closed immersions into
the left chart. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι_comp_subschemeι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι =
    ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
      (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).subschemeι ≫
        X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlap
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_fst]

/-- The local zero locus restricted to an overlap is the pullback of its
closed immersion along the ambient overlap open immersion. -/
theorem SerreExtensionRankTwoAffineCover.isPullback_localPencilZeroOverlap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsPullback
      ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).subschemeι
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
      (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι := by
  apply AlgebraicGeometry.isPullback_of_isClosedImmersion
  · exact (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι_comp_subschemeι
      e C seed i j a b).symm
  · rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
      AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]

/-- The right overlap map has the analogous compatibility with its local
closed immersion. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightι_comp_subschemeι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightι e C seed i j a b ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).subschemeι =
    ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).comap
      (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right))).subschemeι ≫
        X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right) := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightι
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRight
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_fst]

/-- The canonical equality of pulled-back zero ideals gives the transition
isomorphism between the two presentations of a chart overlap. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroOverlapIso
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlap e C seed i j a b ≅
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRight e C seed i j a b :=
  eqToIso (congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme
    (by simpa only [homOfLE_leOfHom] using
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap_canonical
        e C seed i j a b)))

/-- Reindexing a pulled-back ideal subscheme along an equality of ambient
opens.  The construction is explicit because intersections of opens commute
only propositionally, while scheme gluing needs a genuine isomorphism. -/
noncomputable def reindexComapSubschemeIso
    {W U V : X.Opens} (hUV : U = V)
    (I : (W : Scheme.{u}).IdealSheafData)
    (f : (U : Scheme.{u}) ⟶ W) (g : (V : Scheme.{u}) ⟶ W)
    (hfg : (X.isoOfEq hUV).hom ≫ g = f) :
    (I.comap f).subscheme ≅ (I.comap g).subscheme := by
  let r : (U : Scheme.{u}) ⟶ V := (X.isoOfEq hUV).hom
  have hr : IsIso r := by
    dsimp [r]
    infer_instance
  have hcomap : I.comap f = (I.comap g).comap r := by
    rw [← Scheme.IdealSheafData.comap_comp, hfg]
  exact eqToIso (congrArg Scheme.IdealSheafData.subscheme hcomap) ≪≫
    (I.comap g).comapIso r ≪≫ asIso (pullback.snd r (I.comap g).subschemeι)

/-- Reindexing a pulled-back ideal subscheme commutes with its canonical map
to the original closed subscheme. -/
theorem reindexComapSubschemeIso_hom_comp_comapSubschemeι
    {W U V : X.Opens} (hUV : U = V)
    (I : (W : Scheme.{u}).IdealSheafData)
    (f : (U : Scheme.{u}) ⟶ W) (g : (V : Scheme.{u}) ⟶ W)
    (hfg : (X.isoOfEq hUV).hom ≫ g = f) :
    (reindexComapSubschemeIso hUV I f g hfg).hom ≫
      (I.comapIso g).hom ≫ pullback.snd g I.subschemeι =
      (I.comapIso f).hom ≫ pullback.snd f I.subschemeι := by
  apply (cancel_mono I.subschemeι).mp
  unfold reindexComapSubschemeIso
  simp only [Iso.trans_hom, asIso_hom]
  simp only [Category.assoc]
  rw [← pullback.condition (f := g) (g := I.subschemeι)]
  rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  rw [← pullback.condition_assoc (f := (X.isoOfEq hUV).hom)
    (g := (I.comap g).subschemeι) (h := g)]
  rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  rw [← Category.assoc]
  rw [idealSheafData_eqToIso_subschemeι]
  · rw [hfg]
    rw [← pullback.condition (f := f) (g := I.subschemeι)]
    rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  · rw [← Scheme.IdealSheafData.comap_comp, hfg]

/-- Successive pullback of an ideal subscheme commutes with the canonical
map to the original closed subscheme, including an explicitly chosen
one-step composite. -/
theorem comapSubschemeIso_hom_comp_comapSubschemeι
    {A B C : Scheme.{u}} (I : C.IdealSheafData)
    (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C)
    (hcomp : f ≫ g = h) (hcomap : I.comap h = (I.comap g).comap f) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme hcomap)).hom ≫
        ((I.comap g).comapIso f).hom ≫ pullback.snd f (I.comap g).subschemeι ≫
          (I.comapIso g).hom ≫ pullback.snd g I.subschemeι =
      (I.comapIso h).hom ≫ pullback.snd h I.subschemeι := by
  apply (cancel_mono I.subschemeι).mp
  simp only [Category.assoc]
  rw [← pullback.condition (f := g) (g := I.subschemeι)]
  rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  rw [← pullback.condition_assoc (f := f) (g := (I.comap g).subschemeι) (h := g)]
  rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  rw [← Category.assoc]
  rw [idealSheafData_eqToIso_subschemeι]
  · rw [hcomp]
    rw [← pullback.condition (f := h) (g := I.subschemeι)]
    rw [Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  · exact hcomap

/-- The right presentation of an overlap is canonically reindexed to the
left presentation with the chart order reversed. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroOverlapReindexIso
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRight e C seed i j a b ≅
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlap e C seed j i a b := by
  apply reindexComapSubschemeIso
    (X := X) (hUV := inf_comm (C.U i) (C.U j))
    (I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b)
  apply (cancel_mono (C.U j).ι).mp
  simp

/-- Reindexing the right overlap presentation preserves its canonical map to
the local zero locus on the right chart. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroOverlapReindexIso_hom_comp_ι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapReindexIso
      e C seed i j a b).hom ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b =
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightι e C seed i j a b := by
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b
  let f : ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) ⟶
      ((C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right)
  let g : ((C.U j ⊓ C.U i : X.Opens) : Scheme.{u}) ⟶
      ((C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U j ⊓ C.U i ≤ C.U j from inf_le_left)
  let hUV : C.U i ⊓ C.U j = C.U j ⊓ C.U i := inf_comm _ _
  have hfg : (X.isoOfEq hUV).hom ≫ g = f := by
    apply (cancel_mono (C.U j).ι).mp
    simp [f, g]
  change (reindexComapSubschemeIso hUV I f g hfg).hom ≫
      (I.comapIso g).hom ≫ pullback.snd g I.subschemeι =
    (I.comapIso f).hom ≫ pullback.snd f I.subschemeι
  exact reindexComapSubschemeIso_hom_comp_comapSubschemeι hUV I f g hfg

/-- The canonical transition from the overlap on the `i`-th chart to the
same overlap on the `j`-th chart. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlap e C seed i j a b ≅
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlap e C seed j i a b :=
  SerreExtensionRankTwoAffineCover.localPencilZeroOverlapIso e C seed i j a b ≪≫
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapReindexIso e C seed i j a b

/-- The map from the overlap to the local zero locus on its right chart,
transported through the canonical transition isomorphism. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlap e C seed i j a b ⟶
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).subscheme :=
  (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom ≫
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b

/-- The pairwise transition followed by the left overlap map is, by
definition, the right overlap map.  This is the first transition identity
required when the local zero loci are assembled by scheme gluing. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap_hom_comp_left_eq_rightMap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b =
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i j a b := rfl

/-- The change from the left to the right overlap presentation factors
through the right overlap map. -/
@[reassoc]
theorem SerreExtensionRankTwoAffineCover.localPencilZeroOverlapIso_hom_comp_rightι_eq_rightMap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapIso e C seed i j a b).hom ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightι e C seed i j a b =
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i j a b := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap
  simp only [Iso.trans_hom, Category.assoc]
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapReindexIso_hom_comp_ι]

/-- The transported right overlap map has its explicit ambient factorization
through the right pulled-back zero ideal. -/
@[reassoc]
theorem SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap_comp_subschemeι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i j a b ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).subschemeι =
    (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapIso e C seed i j a b).hom ≫
      ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).comap
        (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right))).subschemeι ≫
          X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right) := by
  rw [← SerreExtensionRankTwoAffineCover.localPencilZeroOverlapIso_hom_comp_rightι_eq_rightMap,
    Category.assoc,
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightι_comp_subschemeι]

/-- The two presentations of a pairwise local zero locus induce the same map
to the ambient scheme.  This form is stable under later triple restrictions
and avoids retaining a choice of the left or right chart presentation. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap_comp_subschemeι_comp_ι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i j a b ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).subschemeι ≫
      (C.U j).ι =
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι ≫
      (C.U i).ι := by
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap_comp_subschemeι_assoc]
  rw [← Category.assoc
    (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)]
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι_comp_subschemeι]
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroOverlapIso
  rw [← Category.assoc (eqToIso _).hom]
  rw [idealSheafData_eqToIso_subschemeι]
  · simp
  · simpa only [SerreExtensionRankTwoAffineCover.overlapToLeft,
      SerreExtensionRankTwoAffineCover.overlapToRight, homOfLE_leOfHom] using
      SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap_canonical
        e C seed i j a b

/-- Swapping an overlap and then taking the right local map in the reversed
order recovers the original left restriction. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap_hom_comp_rightMap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed j i a b =
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b := by
  apply (cancel_mono
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι).mp
  apply (cancel_mono (C.U i).ι).mp
  simp only [Category.assoc]
  calc
    (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed j i a b ≫
        (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι ≫
        (C.U i).ι =
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b ≫
        (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).subschemeι ≫
        (C.U j).ι := by
          rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap_comp_subschemeι_comp_ι]
    _ =
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i j a b ≫
        (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).subschemeι ≫
        (C.U j).ι := by
          rw [← Category.assoc
            (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom]
          rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap_hom_comp_left_eq_rightMap]
    _ =
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b ≫
        (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι ≫
        (C.U i).ι := by
          rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap_comp_subschemeι_comp_ι]

/-- The pairwise chart-transition maps are mutually inverse. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap_hom_comp_swap_hom
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed j i a b).hom =
      𝟙 _ := by
  apply (cancel_mono
    (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)).mp
  simp only [Category.assoc]
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap_hom_comp_left_eq_rightMap]
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap_hom_comp_rightMap]
  simp

/-- Both maps out of a chart overlap are open immersions. -/
theorem SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroOverlapRightMap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i j a b) := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap
  letI : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i j a b).hom := by
    apply IsOpenImmersion.of_isIso
  letI : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j i a b) :=
    SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroOverlapι
      e C seed j i a b
  exact IsOpenImmersion.comp _ _

/-- Restriction to the self-overlap of a chart is an isomorphism. -/
theorem SerreExtensionRankTwoAffineCover.isIso_localPencilZeroOverlapι_self
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsIso (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i i a b) := by
  let f : ((C.U i ⊓ C.U i : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U i ≤ C.U i from inf_le_left)
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  change IsIso ((I.comapIso f).hom ≫ pullback.snd f I.subschemeι)
  have hf : IsIso f := by
    refine ⟨X.homOfLE (by simp), ?_, ?_⟩ <;> simp [f]
  infer_instance

/-- The self-overlap restriction is available as an instance for gluing. -/
instance SerreExtensionRankTwoAffineCover.isIso_localPencilZeroOverlapι_self_instance
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsIso (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i i a b) :=
  SerreExtensionRankTwoAffineCover.isIso_localPencilZeroOverlapι_self e C seed i a b

/-- On the self-overlap, the transported right map is the ordinary
restriction map. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap_self
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i i a b =
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i i a b := by
  apply (cancel_mono
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι).mp
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap_comp_subschemeι,
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι_comp_subschemeι]
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroOverlapIso
  simp

/-- The overlap transition is the identity on a self-overlap. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap_self
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap e C seed i i a b).hom =
      𝟙 _ := by
  apply (cancel_mono
    (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i i a b)).mp
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapSwap_hom_comp_left_eq_rightMap,
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap_self]
  simp

/-- The common restriction of the `i`-th local zero locus to three affine
charts, first through the `i,j` overlap and then through the `k`-th chart. -/
noncomputable abbrev SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : Scheme.{u} :=
  (((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
    (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).comap
    (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))).subscheme

/-- The same triple overlap obtained by restricting the original local ideal
in one step.  It is used to compare different parenthesizations of a triple
intersection. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirect
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : Scheme.{u} :=
  ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
    (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i from
      inf_le_left.trans inf_le_left))).subscheme

/-- Successive restriction through a pairwise overlap agrees with direct
restriction to the triple open. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap_eq_direct
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap e C seed i j k a b =
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirect e C seed i j k a b := by
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  let f : ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left)
  let g : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left)
  let h : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i from
      inf_le_left.trans inf_le_left)
  change ((I.comap f).comap g).subscheme = (I.comap h).subscheme
  have hfg : g ≫ f = h := by
    apply (cancel_mono (C.U i).ι).mp
    simp [f, g, h]
  rw [← Scheme.IdealSheafData.comap_comp, hfg]

/-- The one-step and successive presentations of a triple zero restriction,
oriented from the one-step presentation to the successive one.  This
orientation is convenient for comparing their maps to the original local
closed subscheme. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectToSequentialIso
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirect e C seed i j k a b ≅
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap e C seed i j k a b := by
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  let f : ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left)
  let g : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left)
  let h : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i from
      inf_le_left.trans inf_le_left)
  have hcomp : g ≫ f = h := by
    apply (cancel_mono (C.U i).ι).mp
    simp [f, g, h]
  have hcomap : I.comap h = (I.comap f).comap g := by
    rw [← Scheme.IdealSheafData.comap_comp, hcomp]
  exact eqToIso (congrArg Scheme.IdealSheafData.subscheme hcomap)

/-- Restricting the `i`-th local zero ideal through `Uᵢ ∩ Uⱼ` and then
`Uₖ` agrees with restricting it through `Uᵢ ∩ Uₖ`.  This is the second
pairwise view of the triple overlap. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleIdeal_eq_toOverlapIk
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
      (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).comap
        (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left)) =
    ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
      (X.homOfLE (show C.U i ⊓ C.U k ≤ C.U i from inf_le_left))).comap
        (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U k by
          exact inf_le_inf (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) le_rfl)) := by
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  let f : ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left)
  let g : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left)
  let f' : ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U k ≤ C.U i from inf_le_left)
  let g' : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U k by
      exact inf_le_inf (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) le_rfl)
  change (I.comap f).comap g = (I.comap f').comap g'
  have hcomp : g ≫ f = g' ≫ f' := by
    apply (cancel_mono (C.U i).ι).mp
    simp [f, g, f', g']
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hcomp]

/-- The second projection of the triple overlap into the `i,k` pairwise
zero locus.  The source is transported along the canonical equality of its
two iterated pullback ideals. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap e C seed i j k a b ⟶
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlap e C seed i k a b := by
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  let f : ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U k ≤ C.U i from inf_le_left)
  let g : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U k by
      exact inf_le_inf (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) le_rfl)
  let J := ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
    (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).comap
      (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))
  have h : J = (I.comap f).comap g := by
    dsimp [J, I, f, g]
    exact SerreExtensionRankTwoAffineCover.localPencilZeroTripleIdeal_eq_toOverlapIk
      e C seed i j k a b
  exact (eqToIso (congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme h)).hom ≫
    ((I.comap f).comapIso g).hom ≫ pullback.snd _ _

/-- The common triple restriction mapped directly into the local zero locus
on the `k`-th chart.  The construction transports the `i,k` pairwise ideal
comparison through the remaining `j`-chart restriction. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToK
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap e C seed i j k a b ⟶
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed k a b).subscheme := by
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  let K := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed k a b
  let f : ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U k ≤ C.U i from inf_le_left)
  let g : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U k by
      exact inf_le_inf (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) le_rfl)
  let h : ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U k : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U k ≤ C.U k from inf_le_right)
  let J := (I.comap
    (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).comap
      (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))
  have hIk : J = (I.comap f).comap g := by
    dsimp [J, I, f, g]
    exact SerreExtensionRankTwoAffineCover.localPencilZeroTripleIdeal_eq_toOverlapIk
      e C seed i j k a b
  have hpair : I.comap f = K.comap h := by
    dsimp [I, K, f, h]
    simpa only [homOfLE_leOfHom] using
      SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap_canonical
        e C seed i k a b
  have hK : J = (K.comap h).comap g :=
    hIk.trans (congrArg (fun L => L.comap g) hpair)
  exact (eqToIso (congrArg Scheme.IdealSheafData.subscheme hK)).hom ≫
    ((K.comap h).comapIso g).hom ≫ pullback.snd g (K.comap h).subschemeι ≫
      (K.comapIso h).hom ≫ pullback.snd h K.subschemeι

/-- Restricting first through the `i,k` overlap and then transporting to the
right chart is the canonical triple restriction to the `k`-th local zero
locus. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk_comp_rightMap_eq_toK
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk e C seed i j k a b ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i k a b =
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToK e C seed i j k a b := by
  apply (cancel_mono
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed k a b).subschemeι).mp
  simp only [Category.assoc]
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap_comp_subschemeι]
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  let K := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed k a b
  let f : ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U k ≤ C.U i from inf_le_left)
  let g : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U k by
      exact inf_le_inf (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) le_rfl)
  let h : ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U k : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U k ≤ C.U k from inf_le_right)
  let J := (I.comap
    (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).comap
      (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))
  have hIk : J = (I.comap f).comap g := by
    dsimp [J, I, f, g]
    exact SerreExtensionRankTwoAffineCover.localPencilZeroTripleIdeal_eq_toOverlapIk
      e C seed i j k a b
  have hpair : I.comap f = K.comap h := by
    dsimp [I, K, f, h]
    simpa only [homOfLE_leOfHom] using
      SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap_canonical
        e C seed i k a b
  have htrans := congrArg (fun z => z ≫ h)
    (successiveComapTransition (P := I.comap f) (Q := K.comap h) g J hIk hpair)
  simpa only [SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk,
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToK,
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapIso,
    comapSubschemeMap_to_ambient, comapSubschemeMap_to_ambient_assoc, Category.assoc] using htrans

/-- The second projection of a triple overlap is an open immersion. -/
theorem SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroTripleOverlapToIk
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk
        e C seed i j k a b) := by
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  let f : ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U k ≤ C.U i from inf_le_left)
  let g : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U k by
      exact inf_le_inf (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) le_rfl)
  let h := SerreExtensionRankTwoAffineCover.localPencilZeroTripleIdeal_eq_toOverlapIk
    e C seed i j k a b
  change IsOpenImmersion ((eqToIso
    (congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme h)).hom ≫
      ((I.comap f).comapIso g).hom ≫ pullback.snd g (I.comap f).subschemeι)
  letI : IsOpenImmersion (eqToIso
      (congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme h)).hom := inferInstance
  letI : IsOpenImmersion ((I.comap f).comapIso g).hom := inferInstance
  letI : IsOpenImmersion g := inferInstance
  letI : IsOpenImmersion (pullback.snd g (I.comap f).subschemeι) := inferInstance
  infer_instance

/-- The second triple-overlap projection commutes with the closed immersions
into the ambient `i,k` overlap. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk_comp_subschemeι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk e C seed i j k a b ≫
      ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE (show C.U i ⊓ C.U k ≤ C.U i from inf_le_left))).subschemeι =
    (((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
      (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).comap
        (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))).subschemeι ≫
      X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U k by
        exact inf_le_inf (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) le_rfl) := by
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  let f : ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U k ≤ C.U i from inf_le_left)
  let g : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U k by
      exact inf_le_inf (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) le_rfl)
  let J := ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
    (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).comap
      (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))
  have h : J = (I.comap f).comap g := by
    dsimp [J, I, f, g]
    exact SerreExtensionRankTwoAffineCover.localPencilZeroTripleIdeal_eq_toOverlapIk
      e C seed i j k a b
  change ((eqToIso (congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme h)).hom ≫
      ((I.comap f).comapIso g).hom ≫ pullback.snd g (I.comap f).subschemeι) ≫
      (I.comap f).subschemeι = _
  rw [Category.assoc]
  rw [Category.assoc ((I.comap f).comapIso g).hom
    (pullback.snd g (I.comap f).subschemeι) (I.comap f).subschemeι]
  rw [← pullback.condition]
  rw [← Category.assoc ((I.comap f).comapIso g).hom
    (pullback.fst g (I.comap f).subschemeι) g]
  rw [AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_fst]
  rw [← Category.assoc (eqToIso
    (congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme h)).hom
    ((I.comap f).comap g).subschemeι g]
  rw [idealSheafData_eqToIso_subschemeι J ((I.comap f).comap g) h]

/-- The second triple-overlap projection exhibits the triple zero locus as
the pullback of the `i,k` pairwise zero locus. -/
theorem SerreExtensionRankTwoAffineCover.isPullback_localPencilZeroTripleOverlapToIk
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsPullback
      (((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).comap
          (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))).subschemeι
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk e C seed i j k a b)
      (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U k by
        exact inf_le_inf (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) le_rfl))
      ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE (show C.U i ⊓ C.U k ≤ C.U i from inf_le_left))).subschemeι := by
  letI : IsClosedImmersion
      (((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).comap
          (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))).subschemeι :=
    inferInstance
  letI : IsClosedImmersion
      ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE (show C.U i ⊓ C.U k ≤ C.U i from inf_le_left))).subschemeι :=
    inferInstance
  refine AlgebraicGeometry.isPullback_of_isClosedImmersion
    (((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
      (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).comap
        (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))).subschemeι
    ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
      (X.homOfLE (show C.U i ⊓ C.U k ≤ C.U i from inf_le_left))).subschemeι
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk e C seed i j k a b)
    (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U k by
      exact inf_le_inf (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) le_rfl)) ?_ ?_
  · exact (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk_comp_subschemeι
      e C seed i j k a b).symm
  · rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
      AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]
    exact (SerreExtensionRankTwoAffineCover.localPencilZeroTripleIdeal_eq_toOverlapIk
      e C seed i j k a b).symm

/-- The one-step restriction of a local zero locus to the triple chart.  This
uses the direct triple-overlap presentation, so its target has no choice of
parenthesization in the intermediate restriction. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirect
      e C seed i j k a b ⟶
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subscheme :=
  ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comapIso
    (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i from
      inf_le_left.trans inf_le_left))).hom ≫
    pullback.snd _ _

/-- The direct triple restriction is open in the local zero locus. -/
theorem SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroTripleOverlapDirectι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectι
        e C seed i j k a b) := by
  let f : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i from
      inf_le_left.trans inf_le_left)
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  change IsOpenImmersion ((I.comapIso f).hom ≫ pullback.snd f I.subschemeι)
  letI : IsOpenImmersion f := inferInstance
  letI : IsOpenImmersion (pullback.snd f I.subschemeι) := inferInstance
  infer_instance

/-- The direct triple-restriction map commutes with its ambient closed
immersion. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectι_comp_subschemeι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectι
        e C seed i j k a b ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι =
    ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
      (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i from
        inf_le_left.trans inf_le_left))).subschemeι ≫
      X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i from
        inf_le_left.trans inf_le_left) := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectι
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirect
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_fst]

/-- The direct triple restriction is the base change of the local closed
zero locus to the three-chart ambient open. -/
theorem SerreExtensionRankTwoAffineCover.isPullback_localPencilZeroTripleOverlapDirect
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsPullback
      ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i from
          inf_le_left.trans inf_le_left))).subschemeι
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectι e C seed i j k a b)
      (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i from
        inf_le_left.trans inf_le_left))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι := by
  refine AlgebraicGeometry.isPullback_of_isClosedImmersion
    ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
      (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i from
        inf_le_left.trans inf_le_left))).subschemeι
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectι e C seed i j k a b)
    (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i from
      inf_le_left.trans inf_le_left)) ?_ ?_
  · exact (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectι_comp_subschemeι
      e C seed i j k a b).symm
  · rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
      AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]

/-- The triple overlap written from the `j`-th local zero locus, while using
the same parenthesized ambient triple open as the left presentation. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRight
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : Scheme.{u} :=
  (((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).comap
    (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right))).comap
    (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))).subscheme

/-- The canonical equality of pairwise restricted ideals remains valid after
restriction to any third chart.  This is the ideal-level triple-overlap
compatibility needed by the cocycle comparison. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap_eq_right
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap e C seed i j k a b =
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRight
        e C seed i j k a b := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRight
  apply congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme
  exact congrArg (fun I : AlgebraicGeometry.Scheme.IdealSheafData
      ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) => I.comap
        (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left)))
    (by simpa only [SerreExtensionRankTwoAffineCover.overlapToLeft,
      SerreExtensionRankTwoAffineCover.overlapToRight, homOfLE_leOfHom] using
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap_canonical
        e C seed i j a b))

/-- The right triple restriction in its one-step presentation from the
`j`-th local zero ideal. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightDirect
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) : Scheme.{u} :=
  ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).comap
    (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U j from
      inf_le_left.trans inf_le_right))).subscheme

/-- The one-step right triple restriction mapped into the local zero locus
on the `j`-th chart. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightDirectι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightDirect
      e C seed i j k a b ⟶
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).subscheme :=
  ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).comapIso
    (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U j from
      inf_le_left.trans inf_le_right))).hom ≫ pullback.snd _ _

/-- The one-step right triple presentation maps canonically to its
successive right presentation. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightDirectToSequentialIso
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightDirect
      e C seed i j k a b ≅
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRight
        e C seed i j k a b := by
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b
  let f : ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) ⟶
      ((C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right)
  let g : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left)
  let h : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U j from
      inf_le_left.trans inf_le_right)
  have hcomp : g ≫ f = h := by
    apply (cancel_mono (C.U j).ι).mp
    simp [f, g, h]
  have hcomap : I.comap h = (I.comap f).comap g := by
    rw [← Scheme.IdealSheafData.comap_comp, hcomp]
  exact eqToIso (congrArg Scheme.IdealSheafData.subscheme hcomap)

/-- Successive restriction of the right local zero ideal agrees with its
one-step restriction to the common triple chart. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRight_eq_direct
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRight e C seed i j k a b =
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightDirect
        e C seed i j k a b := by
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b
  let f : ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) ⟶
      ((C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right)
  let g : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left)
  let h : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U j from
      inf_le_left.trans inf_le_right)
  change ((I.comap f).comap g).subscheme = (I.comap h).subscheme
  have hfg : g ≫ f = h := by
    apply (cancel_mono (C.U j).ι).mp
    simp [f, g, h]
  rw [← Scheme.IdealSheafData.comap_comp, hfg]

/-- Reindexing the right triple restriction identifies its ambient triple
open with the `(j,k,i)` parenthesization. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightReindexIso
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightDirect
      e C seed i j k a b ≅
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirect
        e C seed j k i a b := by
  apply reindexComapSubschemeIso
    (X := X) (hUV := by simp only [inf_assoc, inf_comm])
    (I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b)
  apply (cancel_mono (C.U j).ι).mp
  simp

/-- Reindexing the one-step right triple restriction preserves its map into
the `j`-th local zero locus. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightReindexIso_hom_comp_directι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightReindexIso
      e C seed i j k a b).hom ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectι e C seed j k i a b =
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightDirectι
      e C seed i j k a b := by
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b
  let f : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U j from
      inf_le_left.trans inf_le_right)
  let g : (((C.U j ⊓ C.U k) ⊓ C.U i : X.Opens) : Scheme.{u}) ⟶
      ((C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U j ⊓ C.U k) ⊓ C.U i ≤ C.U j from
      inf_le_left.trans inf_le_left)
  let hUV : (C.U i ⊓ C.U j) ⊓ C.U k = (C.U j ⊓ C.U k) ⊓ C.U i := by
    simp only [inf_assoc, inf_comm]
  have hfg : (X.isoOfEq hUV).hom ≫ g = f := by
    apply (cancel_mono (C.U j).ι).mp
    simp [f, g]
  change (reindexComapSubschemeIso hUV I f g hfg).hom ≫
      (I.comapIso g).hom ≫ pullback.snd g I.subschemeι =
    (I.comapIso f).hom ≫ pullback.snd f I.subschemeι
  exact reindexComapSubschemeIso_hom_comp_comapSubschemeι hUV I f g hfg

/-- Restriction from the right triple-overlap presentation to the pairwise
right overlap. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRight
      e C seed i j k a b ⟶
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRight e C seed i j a b :=
  (((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).comap
    (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right))).comapIso
    (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))).hom ≫
      pullback.snd _ _

/-- The right triple-overlap presentation is open in the pairwise right
overlap. -/
theorem SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroTripleOverlapRightι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightι
        e C seed i j k a b) := by
  let f : ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) ⟶
      ((C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right)
  let g : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left)
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b
  change IsOpenImmersion (((I.comap f).comapIso g).hom ≫
    pullback.snd g (I.comap f).subschemeι)
  letI : IsOpenImmersion g := inferInstance
  letI : IsOpenImmersion (pullback.snd g (I.comap f).subschemeι) := inferInstance
  infer_instance

/-- The right triple-overlap restriction commutes with the closed immersion
into the ambient pairwise-overlap open. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightι_comp_subschemeι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightι
        e C seed i j k a b ≫
      ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).comap
        (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right))).subschemeι =
    (((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).comap
      (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right))).comap
      (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))).subschemeι ≫
        X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left) := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightι
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRight
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRight
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_fst]

/-- The right triple overlap as an open subscheme of the local zero locus on
the `j`-th chart. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToRight
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRight
      e C seed i j k a b ⟶
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).subscheme :=
  SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightι e C seed i j k a b ≫
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightι e C seed i j a b

/-- Passing from the one-step right triple restriction to the successive
right restriction preserves the map to the `j`-th local zero locus. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightDirectToSequentialIso_hom_comp_toRight
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightDirectToSequentialIso
      e C seed i j k a b).hom ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToRight e C seed i j k a b =
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightDirectι
      e C seed i j k a b := by
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b
  let f : ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) ⟶
      ((C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right)
  let g : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left)
  let h : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U j from
      inf_le_left.trans inf_le_right)
  have hcomp : g ≫ f = h := by
    apply (cancel_mono (C.U j).ι).mp
    simp [f, g, h]
  have hcomap : I.comap h = (I.comap f).comap g := by
    rw [← Scheme.IdealSheafData.comap_comp, hcomp]
  change (eqToIso (congrArg Scheme.IdealSheafData.subscheme hcomap)).hom ≫
      ((I.comap f).comapIso g).hom ≫ pullback.snd g (I.comap f).subschemeι ≫
        (I.comapIso f).hom ≫ pullback.snd f I.subschemeι =
      (I.comapIso h).hom ≫ pullback.snd h I.subschemeι
  exact comapSubschemeIso_hom_comp_comapSubschemeι I g f h hcomp hcomap

/-- Successive restriction through the right overlap is open in the local
zero locus on the second chart. -/
theorem SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroTripleOverlapToRight
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToRight
        e C seed i j k a b) := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToRight
  letI : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightι
        e C seed i j k a b) :=
    SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroTripleOverlapRightι
      e C seed i j k a b
  letI : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightι e C seed i j a b) :=
    SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroOverlapRightι
      e C seed i j a b
  infer_instance

/-- The canonical identification of the left and right presentations of a
triple overlap. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap e C seed i j k a b ≅
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRight
        e C seed i j k a b :=
  eqToIso (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap_eq_right
    e C seed i j k a b)

/-- The triple overlap is an open subscheme of the `i,j` overlap. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap e C seed i j k a b ⟶
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlap e C seed i j a b :=
  (((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
    (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).comapIso
    (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))).hom ≫
      pullback.snd _ _

/-- The pairwise transition commutes with restriction to a third chart.
This is the transition-factorization identity for the triple-overlap data. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso_hom_comp_rightι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso
      e C seed i j k a b).hom ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightι
        e C seed i j k a b =
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapIso e C seed i j a b).hom := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightι
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapIso
  exact idealSheafData_eqToIso_comapSubschemeι
    ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
      (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left)))
    ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).comap
      (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U j from inf_le_right)))
    (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))
    (by simpa only [SerreExtensionRankTwoAffineCover.overlapToLeft,
      SerreExtensionRankTwoAffineCover.overlapToRight, homOfLE_leOfHom] using
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap_canonical
        e C seed i j a b))

/-- Restriction from a pairwise overlap to a triple overlap is open. -/
theorem SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroTripleOverlapι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b) := by
  let f : ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left)
  let g : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left)
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  change IsOpenImmersion (((I.comap f).comapIso g).hom ≫
    pullback.snd g (I.comap f).subschemeι)
  letI : IsOpenImmersion g := inferInstance
  letI : IsOpenImmersion (pullback.snd g (I.comap f).subschemeι) := inferInstance
  infer_instance

/-- The map from the common triple restriction to the pairwise restriction
on the `j,k` charts.  It passes through the right local presentation and
then reindexes the ambient triple open. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap e C seed i j k a b ⟶
  SerreExtensionRankTwoAffineCover.localPencilZeroOverlap e C seed j k a b :=
  (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso e C seed i j k a b).hom ≫
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightDirectToSequentialIso
      e C seed i j k a b).inv ≫
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightReindexIso
      e C seed i j k a b).hom ≫
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectToSequentialIso
      e C seed j k i a b).hom ≫
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed j k i a b

/-- The reindexed map from a triple restriction to the `j,k` overlap is an
open immersion. -/
theorem SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroTripleOverlapToJk
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk
        e C seed i j k a b) := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk
  let _ : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso e C seed i j k a b).hom := by
    apply IsOpenImmersion.of_isIso
  let _ : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightDirectToSequentialIso
        e C seed i j k a b).inv := by
    apply IsOpenImmersion.of_isIso
  let _ : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightReindexIso
        e C seed i j k a b).hom := by
    apply IsOpenImmersion.of_isIso
  let _ : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectToSequentialIso
        e C seed j k i a b).hom := by
    apply IsOpenImmersion.of_isIso
  let _ : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed j k i a b) :=
    SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroTripleOverlapι
      e C seed j k i a b
  infer_instance

/-- The triple-overlap restriction commutes with the two closed immersions
into the ambient pairwise-overlap open. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι_comp_subschemeι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b ≫
      ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).subschemeι =
    (((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
      (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).comap
      (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))).subschemeι ≫
        X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left) := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlap
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    AlgebraicGeometry.Scheme.IdealSheafData.comapIso_hom_fst]

/-- The triple overlap is the pullback of the pairwise closed zero locus
along the third ambient-chart restriction. -/
theorem SerreExtensionRankTwoAffineCover.isPullback_localPencilZeroTripleOverlap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsPullback
      (((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).comap
          (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))).subschemeι
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b)
      (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))
      ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).subschemeι := by
  letI : IsClosedImmersion
      (((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).comap
          (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))).subschemeι :=
    inferInstance
  letI : IsClosedImmersion
      ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).subschemeι :=
    inferInstance
  refine AlgebraicGeometry.isPullback_of_isClosedImmersion
    (((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
      (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).comap
        (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left))).subschemeι
    ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
      (X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left))).subschemeι
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b)
    (X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left)) ?_ ?_
  · exact (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι_comp_subschemeι
      e C seed i j k a b).symm
  · rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
      AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]

/-- The restriction of a triple overlap directly into the local zero locus
on its first chart.  This is the map used to compare two successive chart
restrictions with their one-step restriction. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToLeft
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap e C seed i j k a b ⟶
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subscheme :=
  SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b ≫
    SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b

/-- Passing from the one-step triple restriction to the successive one
preserves the canonical map into the first local zero locus. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectToSequentialIso_hom_comp_toLeft
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectToSequentialIso
      e C seed i j k a b).hom ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToLeft e C seed i j k a b =
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectι e C seed i j k a b := by
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  let f : ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left)
  let g : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left)
  let h : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i from
      inf_le_left.trans inf_le_left)
  have hcomp : g ≫ f = h := by
    apply (cancel_mono (C.U i).ι).mp
    simp [f, g, h]
  have hcomap : I.comap h = (I.comap f).comap g := by
    rw [← Scheme.IdealSheafData.comap_comp, hcomp]
  change (eqToIso (congrArg Scheme.IdealSheafData.subscheme hcomap)).hom ≫
      ((I.comap f).comapIso g).hom ≫ pullback.snd g (I.comap f).subschemeι ≫
        (I.comapIso f).hom ≫ pullback.snd f I.subschemeι =
      (I.comapIso h).hom ≫ pullback.snd h I.subschemeι
  exact comapSubschemeIso_hom_comp_comapSubschemeι I g f h hcomp hcomap

/-- Expanded form of the compatibility with the two successive restriction
maps. -/
@[reassoc]
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectToSequentialIso_hom_comp_ι_comp_ι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectToSequentialIso
      e C seed i j k a b).hom ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b =
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectι e C seed i j k a b := by
  simpa only [SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToLeft] using
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectToSequentialIso_hom_comp_toLeft
      e C seed i j k a b

/-- The reindexed triple map to the `j,k` overlap agrees with the canonical
right-hand triple restriction after both are mapped into the `j`-th local
zero locus. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk_comp_ι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk e C seed i j k a b ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j k a b =
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso
      e C seed i j k a b).hom ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToRight e C seed i j k a b := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk
  simp only [Category.assoc]
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapDirectToSequentialIso_hom_comp_ι_comp_ι]
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightReindexIso_hom_comp_directι]
  rw [← SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapRightDirectToSequentialIso_hom_comp_toRight]
  simp only [Iso.inv_hom_id_assoc]

/-- The two successive restrictions of the local zero locus, through the
`i,j` and `i,k` overlaps, coincide on the triple chart. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToLeft_eq_toIk
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToLeft e C seed i j k a b =
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk e C seed i j k a b ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToLeft
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  let f_ij : ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left)
  let g_ij : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left)
  let f_ik : ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U k ≤ C.U i from inf_le_left)
  let g_ik : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶
      ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U k by
      exact inf_le_inf (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) le_rfl)
  let Iij := I.comap f_ij
  let Iijk := Iij.comap g_ij
  let Iik := I.comap f_ik
  have hpairij :
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b ≫ I.subschemeι =
        Iij.subschemeι ≫ f_ij := by
    dsimp [I, Iij, f_ij]
    exact SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι_comp_subschemeι
      e C seed i j a b
  have htripleij :
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b ≫
        Iij.subschemeι = Iijk.subschemeι ≫ g_ij := by
    dsimp [I, f_ij, g_ij, Iij, Iijk]
    exact SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι_comp_subschemeι
      e C seed i j k a b
  have htripleik :
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk e C seed i j k a b ≫
        Iik.subschemeι = Iijk.subschemeι ≫ g_ik := by
    dsimp [I, f_ij, g_ij, f_ik, g_ik, Iij, Iijk, Iik]
    exact SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk_comp_subschemeι
      e C seed i j k a b
  have hpairik :
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b ≫ I.subschemeι =
        Iik.subschemeι ≫ f_ik := by
    dsimp [I, Iik, f_ik]
    exact SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι_comp_subschemeι
      e C seed i k a b
  have hambient : g_ij ≫ f_ij = g_ik ≫ f_ik := by
    dsimp [g_ij, f_ij, g_ik, f_ik]
    simp only [Scheme.homOfLE_homOfLE]
  have hmiddle : (Iijk.subschemeι ≫ g_ij) ≫ f_ij =
      (Iijk.subschemeι ≫ g_ik) ≫ f_ik := by
    rw [Category.assoc, hambient, ← Category.assoc]
  apply (cancel_mono I.subschemeι).mp
  have hleft :
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b) ≫
          I.subschemeι = (Iijk.subschemeι ≫ g_ij) ≫ f_ij := by
    rw [Category.assoc, hpairij, ← Category.assoc, htripleij]
  have hright :
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk e C seed i j k a b ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) ≫
          I.subschemeι = (Iijk.subschemeι ≫ g_ik) ≫ f_ik := by
    rw [Category.assoc, hpairik, ← Category.assoc, htripleik]
  exact hleft.trans (hmiddle.trans hright.symm)

/-- The canonical triple restriction to the `k`-th local zero locus has the
same ambient map as the ordinary successive restriction through the `i,j`
overlap. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToK_comp_subschemeι_comp_ι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToK e C seed i j k a b ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed k a b).subschemeι ≫
      (C.U k).ι =
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι ≫
      (C.U i).ι := by
  rw [← SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk_comp_rightMap_eq_toK]
  simp only [Category.assoc]
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap_comp_subschemeι_comp_ι]
  rw [← Category.assoc
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk e C seed i j k a b)]
  rw [← SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToLeft_eq_toIk]
  rfl

/-- The common triple restriction is the categorical pullback of the two
pairwise restrictions of a local Serre-pencil zero locus.  This supplies the
universal property required for the triple-overlap part of scheme gluing. -/
theorem SerreExtensionRankTwoAffineCover.isPullback_localPencilZeroTripleOverlap_pairwise
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsPullback
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk e C seed i j k a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) := by
  let I := SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b
  let f_ij : ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) ⟶ ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left)
  let f_ik : ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶ ((C.U i : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U k ≤ C.U i from inf_le_left)
  let g_ij : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶ ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U j from inf_le_left)
  let g_ik : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶ ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U i ⊓ C.U k by
      exact inf_le_inf (show C.U i ⊓ C.U j ≤ C.U i from inf_le_left) le_rfl)
  let r_ik : ((C.U i ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶ ((C.U k : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show C.U i ⊓ C.U k ≤ C.U k from inf_le_right)
  let h_ijk : (((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) : Scheme.{u}) ⟶ ((C.U k : X.Opens) : Scheme.{u}) :=
    X.homOfLE (show (C.U i ⊓ C.U j) ⊓ C.U k ≤ C.U k from inf_le_right)
  let Iij := I.comap f_ij
  let Iik := I.comap f_ik
  let Iijk := Iij.comap g_ij
  let Hambient := AlgebraicGeometry.isPullback_opens_inf (C.U i ⊓ C.U j) (C.U k)
  let Hij := SerreExtensionRankTwoAffineCover.isPullback_localPencilZeroOverlap
    e C seed i j a b
  let Hik := SerreExtensionRankTwoAffineCover.isPullback_localPencilZeroOverlap
    e C seed i k a b
  let Htriple := SerreExtensionRankTwoAffineCover.isPullback_localPencilZeroTripleOverlap
    e C seed i j k a b
  let HtoIk := SerreExtensionRankTwoAffineCover.isPullback_localPencilZeroTripleOverlapToIk
    e C seed i j k a b
  have hcone :
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b =
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk e C seed i j k a b ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b := by
    exact SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToLeft_eq_toIk
      e C seed i j k a b
  let q : ∀ s : PullbackCone
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b),
      s.pt ⟶ ((C.U i ⊓ C.U j) ⊓ C.U k : X.Opens) := fun s =>
    Hambient.lift (s.fst ≫ Iij.subschemeι)
      (s.snd ≫ Iik.subschemeι ≫ r_ik) (by
        calc
          (s.fst ≫ Iij.subschemeι) ≫ (C.U i ⊓ C.U j).ι =
              s.fst ≫ (Iij.subschemeι ≫ f_ij) ≫ (C.U i).ι := by
            have hfij : f_ij ≫ (C.U i).ι = (C.U i ⊓ C.U j).ι := by
              dsimp [f_ij]
              exact X.homOfLE_ι _
            calc
              (s.fst ≫ Iij.subschemeι) ≫ (C.U i ⊓ C.U j).ι =
                  (s.fst ≫ Iij.subschemeι) ≫ (f_ij ≫ (C.U i).ι) :=
                congrArg ((s.fst ≫ Iij.subschemeι) ≫ ·) hfij.symm
              _ = s.fst ≫ (Iij.subschemeι ≫ f_ij) ≫ (C.U i).ι := by
                simp only [Category.assoc]
          _ = s.fst ≫
              (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b ≫
                I.subschemeι) ≫ (C.U i).ι := by
            rw [Hij.w]
          _ = s.snd ≫
              (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b ≫
                I.subschemeι) ≫ (C.U i).ι := by
            simp only [← Category.assoc, s.condition]
          _ = s.snd ≫ (Iik.subschemeι ≫ f_ik) ≫ (C.U i).ι := by
            rw [Hik.w]
          _ = (s.snd ≫ Iik.subschemeι ≫ r_ik) ≫ (C.U k).ι := by
            have hfik : f_ik ≫ (C.U i).ι = (C.U i ⊓ C.U k).ι := by
              dsimp [f_ik]
              exact X.homOfLE_ι _
            have hrik : r_ik ≫ (C.U k).ι = (C.U i ⊓ C.U k).ι := by
              dsimp [r_ik]
              exact X.homOfLE_ι _
            calc
              s.snd ≫ (Iik.subschemeι ≫ f_ik) ≫ (C.U i).ι =
                  (s.snd ≫ Iik.subschemeι) ≫ (f_ik ≫ (C.U i).ι) := by
                    simp only [Category.assoc]
              _ = (s.snd ≫ Iik.subschemeι) ≫ (C.U i ⊓ C.U k).ι :=
                congrArg ((s.snd ≫ Iik.subschemeι) ≫ ·) hfik
              _ = (s.snd ≫ Iik.subschemeι) ≫ (r_ik ≫ (C.U k).ι) :=
                congrArg ((s.snd ≫ Iik.subschemeι) ≫ ·) hrik.symm
              _ = (s.snd ≫ Iik.subschemeι ≫ r_ik) ≫ (C.U k).ι := by
                simp only [Category.assoc])
  let lift : ∀ s : PullbackCone
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b),
      s.pt ⟶ SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap
        e C seed i j k a b := fun s =>
    Htriple.lift (q s) s.fst (by
      dsimp [q]
      exact Hambient.lift_fst _ _ _)
  have lift_fst (s : PullbackCone
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b)) :
      lift s ≫ SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι
        e C seed i j k a b = s.fst := by
    dsimp [lift]
    exact Htriple.lift_snd _ _ _
  let _ : Mono (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) :=
    (SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroOverlapι
      e C seed i k a b).mono
  have lift_snd (s : PullbackCone
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b)) :
      lift s ≫ SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk
        e C seed i j k a b = s.snd := by
    apply (cancel_mono
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b)).mp
    rw [Category.assoc, ← hcone, ← Category.assoc, lift_fst, s.condition]
  refine ⟨⟨hcone⟩, ⟨PullbackCone.isLimitAux
    (PullbackCone.mk
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b)
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk e C seed i j k a b)
      hcone) lift (fun s => lift_fst s) (fun s => lift_snd s) ?_⟩⟩
  intro s m hm
  change s.pt ⟶ SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap
    e C seed i j k a b at m
  have hm_fst : m ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b =
        s.fst := by
    have h := hm WalkingCospan.left
    change m ≫ SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι
      e C seed i j k a b = s.fst at h
    exact h
  have hm_snd : m ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk e C seed i j k a b =
        s.snd := by
    have h := hm WalkingCospan.right
    change m ≫ SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk
      e C seed i j k a b = s.snd at h
    exact h
  apply Htriple.hom_ext
  · have hlift_ambient : lift s ≫ Iijk.subschemeι = q s := by
      dsimp [lift]
      exact Htriple.lift_fst _ _ _
    apply Hambient.hom_ext
    · rw [hlift_ambient]
      change m ≫ Iijk.subschemeι ≫ g_ij = q s ≫ g_ij
      calc
        m ≫ Iijk.subschemeι ≫ g_ij =
            m ≫ (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι
              e C seed i j k a b ≫ Iij.subschemeι) := by
              rw [Htriple.w]
        _ = s.fst ≫ Iij.subschemeι := by rw [← Category.assoc, hm_fst]
        _ = q s ≫ g_ij := by
          dsimp [q]
          exact (Hambient.lift_fst _ _ _).symm
    · rw [hlift_ambient]
      change m ≫ Iijk.subschemeι ≫ h_ijk = q s ≫ h_ijk
      have hgik : g_ik ≫ r_ik = h_ijk := by
        dsimp [g_ik, r_ik, h_ijk]
        simp only [Scheme.homOfLE_homOfLE]
      calc
        m ≫ Iijk.subschemeι ≫ h_ijk = m ≫ Iijk.subschemeι ≫ g_ik ≫ r_ik := by
          rw [hgik]
        _ = m ≫ (Iijk.subschemeι ≫ g_ik) ≫ r_ik := by
          simp only [Category.assoc]
        _ = m ≫
            (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk
              e C seed i j k a b ≫ Iik.subschemeι) ≫ r_ik := by
          rw [HtoIk.w]
        _ = (m ≫
            SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk
              e C seed i j k a b) ≫ Iik.subschemeι ≫ r_ik := by
          simp only [Category.assoc]
        _ = s.snd ≫ Iik.subschemeι ≫ r_ik := by
          rw [hm_snd]
        _ = q s ≫ h_ijk := by
          dsimp [q]
          exact (Hambient.lift_snd _ _ _).symm
  · rw [hm_fst, lift_fst]

/-- The canonical isomorphism from the explicit triple restriction to the
pullback of the two pairwise restrictions. -/
noncomputable def SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlap e C seed i j k a b ≅
      pullback
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
        (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) :=
  (SerreExtensionRankTwoAffineCover.isPullback_localPencilZeroTripleOverlap_pairwise
    e C seed i j k a b).isoPullback

/-- The first projection of the pairwise-pullback model is the usual map
from the triple restriction to the `i,j` restriction. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso_hom_fst
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso
      e C seed i j k a b).hom ≫
        pullback.fst
          (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
          (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) =
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b :=
  (SerreExtensionRankTwoAffineCover.isPullback_localPencilZeroTripleOverlap_pairwise
    e C seed i j k a b).isoPullback_hom_fst

/-- The second projection of the pairwise-pullback model is the `i,k`
restriction map constructed from the alternate triple presentation. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso_hom_snd
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapPairwiseIso
      e C seed i j k a b).hom ≫
        pullback.snd
          (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b)
          (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i k a b) =
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToIk e C seed i j k a b :=
  (SerreExtensionRankTwoAffineCover.isPullback_localPencilZeroTripleOverlap_pairwise
    e C seed i j k a b).isoPullback_hom_snd

/-- The triple-overlap transition remains compatible after mapping all the way
to the zero locus on the right chart. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso_hom_comp_toRight
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso
      e C seed i j k a b).hom ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToRight
        e C seed i j k a b =
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapIso e C seed i j a b).hom ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightι e C seed i j a b := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToRight
  rw [← Category.assoc,
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso_hom_comp_rightι]
  simp only [Category.assoc]

/-- The triple transition followed by the right restriction factors through
the right overlap map from the original pairwise overlap. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso_hom_comp_toRight_eq_rightMap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso
      e C seed i j k a b).hom ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToRight e C seed i j k a b =
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i j a b := by
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso_hom_comp_toRight]
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapIso_hom_comp_rightι_eq_rightMap]

/-- The path to the `j,k` overlap, followed by its right local map, has the
same ambient triple-restriction map as the original `i,j` path. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk_comp_rightMap_comp_subschemeι_comp_ι
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk e C seed i j k a b ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed j k a b ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed k a b).subschemeι ≫
      (C.U k).ι =
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b ≫
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι ≫
      (C.U i).ι := by
  calc
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk e C seed i j k a b ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed j k a b ≫
        (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed k a b).subschemeι ≫
        (C.U k).ι =
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk e C seed i j k a b ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed j k a b ≫
        (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).subschemeι ≫
        (C.U j).ι := by
          rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap_comp_subschemeι_comp_ι]
    _ =
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso e C seed i j k a b).hom ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToRight e C seed i j k a b ≫
        (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).subschemeι ≫
        (C.U j).ι := by
          rw [← Category.assoc
            (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk e C seed i j k a b)]
          rw [SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk_comp_ι]
          simp only [Category.assoc]
    _ =
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed i j a b ≫
        (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).subschemeι ≫
        (C.U j).ι := by
          rw [← Category.assoc
            (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso e C seed i j k a b).hom]
          rw [SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapIso_hom_comp_toRight_eq_rightMap]
          simp only [Category.assoc]
    _ =
      SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b ≫
        SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b ≫
        (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).subschemeι ≫
        (C.U i).ι := by
          rw [SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap_comp_subschemeι_comp_ι]

/-- Restricting through the `j,k` overlap and then taking its right local map
is the same canonical triple restriction to the `k`-th local zero locus. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk_comp_rightMap_eq_toK
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk e C seed i j k a b ≫
      SerreExtensionRankTwoAffineCover.localPencilZeroOverlapRightMap e C seed j k a b =
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToK e C seed i j k a b := by
  have hleft :=
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToJk_comp_rightMap_comp_subschemeι_comp_ι
      e C seed i j k a b
  have hright :=
    SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToK_comp_subschemeι_comp_ι
      e C seed i j k a b
  apply (cancel_mono
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed k a b).subschemeι).mp
  apply (cancel_mono (C.U k).ι).mp
  simp only [Category.assoc]
  exact hleft.trans hright.symm

/-- Successive restriction to a triple overlap is open in the local zero
locus on the first chart. -/
theorem SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroTripleOverlapToLeft
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j k : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToLeft
        e C seed i j k a b) := by
  unfold SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapToLeft
  letI : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroTripleOverlapι e C seed i j k a b) :=
    SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroTripleOverlapι
      e C seed i j k a b
  letI : IsOpenImmersion
      (SerreExtensionRankTwoAffineCover.localPencilZeroOverlapι e C seed i j a b) :=
    SerreExtensionRankTwoAffineCover.isOpenImmersion_localPencilZeroOverlapι
      e C seed i j a b
  infer_instance

/-- The ambient kernel extensions of local Serre-pencil zero ideals have equal
pullbacks to every affine overlap.  Thus extending the local closed schemes
through their open chart inclusions preserves precisely the descent datum
already supplied by the local trivializations. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension_comap_overlap
    [QuasiSeparatedSpace X]
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed i a b).comap
      ((C.U i ⊓ C.U j).ι) =
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed j a b).comap
      ((C.U i ⊓ C.U j).ι) := by
  calc
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed i a b).comap
        ((C.U i ⊓ C.U j).ι) =
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE inf_le_left) :=
      SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension_comap_of_le
        e C seed i (C.U i ⊓ C.U j) inf_le_left a b
    _ = (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b).comap
        (X.homOfLE inf_le_right) := by
      simpa only [homOfLE_leOfHom] using
        (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap_canonical
          e C seed i j a b)
    _ = (SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed j a b).comap
        ((C.U i ⊓ C.U j).ι) :=
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension_comap_of_le
        e C seed j (C.U i ⊓ C.U j) inf_le_right a b).symm

/-- The ambient chart models restrict to literally the same closed scheme on
an overlap.  This is the scheme-level descent datum for the local Serre
pencil and is the form required to build the global member by gluing closed
immersions. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroSubschemeExtension_comap_overlap
    [QuasiSeparatedSpace X]
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    ((SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed i a b).comap
      ((C.U i ⊓ C.U j).ι)).subscheme =
    ((SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed j a b).comap
      ((C.U i ⊓ C.U j).ι)).subscheme := by
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension_comap_overlap]

/-- On every smaller open of an affine trivializing chart, the ambient
closed model is the pullback of that chart's coordinate zero locus. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroSubschemeExtension_comap_of_le
    [QuasiSeparatedSpace X]
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i : C.ι) (V : X.Opens) (hV : V ≤ C.U i)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    ((SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension e C seed i a b).comap
      V.ι).subscheme =
      ((SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b).comap
        (X.homOfLE hV)).subscheme := by
  rw [SerreExtensionRankTwoAffineCover.localPencilZeroIdealExtension_comap_of_le]

/-- The pulled-back local closed zero schemes agree on the affine overlap
under the same section restriction coherences. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroSubscheme_comap_overlap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hleft : SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible
      e seed (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j) a b)
    (hright : SerreExtensionPencilSeed.linearCombinationSectionRestrictionCompatible
      e seed (SerreExtensionRankTwoAffineCover.overlapToRight e C i j) a b) :
    (AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U i : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j)))).subscheme =
    (AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U j : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToRight e C i j)))).subscheme := by
  exact congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap e C seed i j a b hleft hright)

/-- The same overlap equality for local Serre-pencil zero schemes, with the
two section coherences reduced to the canonical structure-sheaf coherence. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroSubscheme_comap_overlap_of_unit
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hleft : BundleSectionZeroLocus.localRestrictionUnitCompatible
      (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j))
    (hright : BundleSectionZeroLocus.localRestrictionUnitCompatible
      (SerreExtensionRankTwoAffineCover.overlapToRight e C i j)) :
    (AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U i : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j)))).subscheme =
    (AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U j : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToRight e C i j)))).subscheme := by
  exact congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap_of_unit
      e C seed i j a b hleft hright)

/-- The corresponding affine-overlap identity for the closed Serre-pencil
zero schemes under the reduced core unit comparisons. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroSubscheme_comap_overlap_of_core
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf)
    (hleft :
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso
        (X.homOfLE (leOfHom
          (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j)))).symm.hom ≫
        (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv
          (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j)).inv.app
          ((SheafOfModules.unit X.ringCatSheaf).over (C.U i)) = 𝟙 _)
    (hright :
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso
        (X.homOfLE (leOfHom
          (SerreExtensionRankTwoAffineCover.overlapToRight e C i j)))).symm.hom ≫
        (AlgebraicGeometry.Scheme.Modules.overMapCompOverEquiv
          (SerreExtensionRankTwoAffineCover.overlapToRight e C i j)).inv.app
          ((SheafOfModules.unit X.ringCatSheaf).over (C.U j)) = 𝟙 _) :
    (AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U i : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j)))).subscheme =
    (AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U j : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToRight e C i j)))).subscheme := by
  exact congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap_of_core
      e C seed i j a b hleft hright)

/-- The zero subschemes of every Serre-pencil member agree after pullback to
each affine overlap of a rank-two trivializing cover. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroSubscheme_comap_overlap_canonical
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    (AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U i : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed i a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j)))).subscheme =
    (AlgebraicGeometry.Scheme.IdealSheafData.comap
      (X := ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}))
      (Y := ((C.U j : X.Opens) : Scheme.{u}))
      (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal e C seed j a b)
      (X.homOfLE (leOfHom
        (SerreExtensionRankTwoAffineCover.overlapToRight e C i j)))).subscheme := by
  exact congrArg AlgebraicGeometry.Scheme.IdealSheafData.subscheme
    (SerreExtensionRankTwoAffineCover.localPencilZeroIdeal_comap_overlap_canonical
      e C seed i j a b)


/-- The closed subschemes cut out from the two rank-two charts agree after
both are restricted to their affine overlap. -/
theorem SerreExtensionRankTwoAffineCover.localPencilZeroSubscheme_overlap
    (C : SerreExtensionRankTwoAffineCover e) (seed : SerreExtensionPencilSeed e)
    (i j : C.ι)
    (a b : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver e seed
      (C.U i ⊓ C.U j) (ULift.{u} (Fin 2))
      (BundleSectionZeroLocus.restrictFreeIsoOver
        (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j)
        (ULift.{u} (Fin 2)) (C.trivialization i)) a b =
    SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver e seed
      (C.U i ⊓ C.U j) (ULift.{u} (Fin 2))
      (BundleSectionZeroLocus.restrictFreeIsoOver
        (SerreExtensionRankTwoAffineCover.overlapToRight e C i j)
        (ULift.{u} (Fin 2)) (C.trivialization j)) a b := by
  haveI : AlgebraicGeometry.IsAffine ((C.U i ⊓ C.U j : X.Opens) : Scheme.{u}) :=
    C.overlapAffine i j
  exact
    SerreExtensionPencilSeed.linearCombinationLocalZeroSubschemeOfOver_restrictFreeIsoOver_eq
      e seed (SerreExtensionRankTwoAffineCover.overlapToLeft e C i j)
      (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) (C.trivialization i)
      (BundleSectionZeroLocus.restrictFreeIsoOver
        (SerreExtensionRankTwoAffineCover.overlapToRight e C i j)
        (ULift.{u} (Fin 2)) (C.trivialization j)) a b

end SerreExtensionData


namespace SerreExtensionSequenceData

variable {X : Scheme.{u}} {M : SheafOfModules.{u} X.ringCatSheaf}
  (e : SerreExtensionSequenceData X M)

/-- Once the Galois bad locus is empty and the local calculation gives free
neighborhoods away from it, the extension sequence becomes the locally free
Serre datum used for the rank-two pencil. -/
noncomputable def toSerreExtensionData_of_badLocus_eq_empty
    (B : Set X) (hB : B = ∅)
    (U : ∀ x : X, x ∉ B → X.Opens)
    (hU : ∀ (x : X) (hx : x ∉ B), x ∈ U x hx)
    (I : ∀ (x : X) (hx : x ∉ B), Type u)
    (hfree : ∀ (x : X) (hx : x ∉ B),
      SheafOfModules.free (R := X.ringCatSheaf.over (U x hx)) (I x hx) ≅
        e.E.over (U x hx)) :
    SerreExtensionData X M :=
  SerreExtensionData.ofSequence e
    (sheaf_isLocallyFree_of_badLocus_eq_empty X e.E B hB U hU I hfree)

/-- When the only possible nonfree locus is empty and the local calculation
provides affine rank-two trivializations, those trivializations assemble into
the cover on which the Serre-pencil zero schemes have compatible overlaps. -/
noncomputable def toSerreExtensionRankTwoAffineCover_of_badLocus_eq_empty
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (B : Set X) (hB : B = ∅)
    (U : ∀ x : X, x ∉ B → X.Opens)
    (hU : ∀ (x : X) (hx : x ∉ B), x ∈ U x hx)
    (haffine : ∀ (x : X) (hx : x ∉ B),
      AlgebraicGeometry.IsAffine (U x hx : Scheme.{u}))
    (t : ∀ (x : X) (hx : x ∉ B),
      SheafOfModules.free (R := X.ringCatSheaf.over (U x hx))
        (ULift.{u} (Fin 2)) ≅ e.E.over (U x hx)) :
    SerreExtensionData.SerreExtensionRankTwoAffineCover
      (e.toSerreExtensionData_of_badLocus_eq_empty B hB U hU
        (fun _ _ => ULift.{u} (Fin 2)) t) := by
  exact SerreExtensionData.SerreExtensionRankTwoAffineCover.ofPointwise
    (e.toSerreExtensionData_of_badLocus_eq_empty B hB U hU
      (fun _ _ => ULift.{u} (Fin 2)) t)
    (fun x => U x (by simp [hB]))
    (fun x => hU x (by simp [hB]))
    (fun x => haffine x (by simp [hB]))
    (fun x => t x (by simp [hB]))

/-- A bad locus may be indexed by geometric points of a finite subscheme
rather than by points of the ambient scheme.  If that orbit-indexed locus is
empty, its image in the ambient scheme is empty as well, so pointwise free
neighborhoods outside the image give a locally free Serre extension.  This
is the form needed after Voisin's Galois-orbit argument. -/
noncomputable def toSerreExtensionData_of_badOrbit_eq_empty
    {Q : Type u} (B : Set Q) (point : Q → X) (hB : B = ∅)
    (U : ∀ x : X, x ∉ point '' B → X.Opens)
    (hU : ∀ (x : X) (hx : x ∉ point '' B), x ∈ U x hx)
    (I : ∀ (x : X) (hx : x ∉ point '' B), Type u)
    (hfree : ∀ (x : X) (hx : x ∉ point '' B),
      SheafOfModules.free (R := X.ringCatSheaf.over (U x hx)) (I x hx) ≅
        e.E.over (U x hx)) :
    SerreExtensionData X M :=
  e.toSerreExtensionData_of_badLocus_eq_empty (point '' B)
    (by simpa [hB]) U hU I hfree

/-- The rank-two affine cover used by the Serre pencil can likewise be
assembled directly from an orbit-indexed bad locus once its image is empty.
The local calculation only has to provide the displayed rank-two
trivializations away from that image. -/
noncomputable def toSerreExtensionRankTwoAffineCover_of_badOrbit_eq_empty
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {Q : Type u} (B : Set Q) (point : Q → X) (hB : B = ∅)
    (U : ∀ x : X, x ∉ point '' B → X.Opens)
    (hU : ∀ (x : X) (hx : x ∉ point '' B), x ∈ U x hx)
    (haffine : ∀ (x : X) (hx : x ∉ point '' B),
      AlgebraicGeometry.IsAffine (U x hx : Scheme.{u}))
    (t : ∀ (x : X) (hx : x ∉ point '' B),
      SheafOfModules.free (R := X.ringCatSheaf.over (U x hx))
        (ULift.{u} (Fin 2)) ≅ e.E.over (U x hx)) :
    SerreExtensionData.SerreExtensionRankTwoAffineCover
      (e.toSerreExtensionData_of_badOrbit_eq_empty B point hB U hU
        (fun _ _ => ULift.{u} (Fin 2)) t) := by
  exact e.toSerreExtensionRankTwoAffineCover_of_badLocus_eq_empty (point '' B)
    (by simpa [hB]) U hU haffine t

/-- Voisin's Galois-orbit criterion can be used directly to turn a Serre
extension sequence into a locally free Serre datum.  The local calculation
supplies the free neighborhoods away from the bad locus; pretransitivity,
injectivity of the local restriction map, and nonvanishing of the class force
that locus to be empty. -/
noncomputable def toSerreExtensionData_of_pretransitive_badLocus
    {G V W : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
    [AddCommMonoid V] [AddCommMonoid W]
    (B : Set X) (hstable : ∀ (g : G) (x : X), x ∈ B → g • x ∈ B)
    (extensionClass : V) (restriction : V →+ W)
    (hinjective : Function.Injective restriction) (hne : extensionClass ≠ 0)
    (hvanishes : B = Set.univ → restriction extensionClass = 0)
    (U : ∀ x : X, x ∉ B → X.Opens)
    (hU : ∀ (x : X) (hx : x ∉ B), x ∈ U x hx)
    (I : ∀ (x : X) (hx : x ∉ B), Type u)
    (hfree : ∀ (x : X) (hx : x ∉ B),
      SheafOfModules.free (R := X.ringCatSheaf.over (U x hx)) (I x hx) ≅
        e.E.over (U x hx)) :
    SerreExtensionData X M :=
  e.toSerreExtensionData_of_badLocus_eq_empty B
    (invariant_badLocus_eq_empty_of_pretransitive B hstable extensionClass restriction
      hinjective hne hvanishes)
    U hU I hfree

/-- The Galois-orbit local-freeness argument directly supplies the affine
rank-two cover needed for the compatible local zero schemes of the Serre
pencil, once its local calculation provides rank-two trivializations. -/
noncomputable def toSerreExtensionRankTwoAffineCover_of_pretransitive_badLocus
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {G V W : Type*} [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
    [AddCommMonoid V] [AddCommMonoid W]
    (B : Set X) (hstable : ∀ (g : G) (x : X), x ∈ B → g • x ∈ B)
    (extensionClass : V) (restriction : V →+ W)
    (hinjective : Function.Injective restriction) (hne : extensionClass ≠ 0)
    (hvanishes : B = Set.univ → restriction extensionClass = 0)
    (U : ∀ x : X, x ∉ B → X.Opens)
    (hU : ∀ (x : X) (hx : x ∉ B), x ∈ U x hx)
    (haffine : ∀ (x : X) (hx : x ∉ B),
      AlgebraicGeometry.IsAffine (U x hx : Scheme.{u}))
    (t : ∀ (x : X) (hx : x ∉ B),
      SheafOfModules.free (R := X.ringCatSheaf.over (U x hx))
        (ULift.{u} (Fin 2)) ≅ e.E.over (U x hx)) :
    SerreExtensionData.SerreExtensionRankTwoAffineCover
      (e.toSerreExtensionData_of_pretransitive_badLocus B hstable extensionClass restriction
        hinjective hne hvanishes U hU (fun _ _ => ULift.{u} (Fin 2)) t) :=
  e.toSerreExtensionRankTwoAffineCover_of_badLocus_eq_empty B
    (invariant_badLocus_eq_empty_of_pretransitive B hstable extensionClass restriction
      hinjective hne hvanishes)
    U hU haffine t


end SerreExtensionSequenceData
end PfaffianDescent
