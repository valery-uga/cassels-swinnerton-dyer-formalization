import PfaffianDescent.ExtMapFixedSource

/-! # Transport of actual nonzero Ext kernels through exact equivalences

An exact equivalence preserves a nonzero class and its actual vanishing
under precomposition. The object identifications retain the original map.
-/

noncomputable section
open CategoryTheory CategoryTheory.Abelian

namespace PfaffianDescent
universe u v u' v' w w'

/-- Changing the quotient presentation by its actual source isomorphism
preserves a nonzero augmentation kernel. -/
theorem exists_nonzero_ext_kernel_of_sourceIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {M Q Q' Y : C} (g : M ⟶ Q') (e : Q ≅ Q') (n : ℕ)
    (z : Ext.{w} Q Y n) (hz : z ≠ 0)
    (hkernel : (Ext.mk₀.{w} (g ≫ e.inv)).comp z (zero_add n) = 0) :
    ∃ z' : Ext.{w} Q' Y n, z' ≠ 0 ∧
      (Ext.mk₀.{w} g).comp z' (zero_add n) = 0 := by
  let t := extPrecompIsoOfIso e (Y := Y) (n := n)
  refine ⟨t z, ?_, ?_⟩
  · intro h
    apply hz
    apply t.injective
    simpa only [map_zero] using h
  · change (Ext.mk₀.{w} g).comp ((Ext.mk₀.{w} e.inv).comp z
      (zero_add n)) (zero_add n) = 0
    rw [Ext.mk₀_comp_mk₀_assoc]
    exact hkernel

/-- A nonzero kernel in concrete transported objects gives a nonzero kernel
for the original map. -/
theorem exists_nonzero_ext_kernel_of_exactEquivalenceOfIsos
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    [EnoughInjectives C]
    (E : C ≌ D) [E.functor.Additive]
    {M Q Y : C} {M' Q' Y' : D}
    (g : M ⟶ Q) (g' : M' ⟶ Q')
    (eM : E.functor.obj M ≅ M') (eQ : E.functor.obj Q ≅ Q')
    (eY : E.functor.obj Y ≅ Y')
    (hsquare : E.functor.map g ≫ eQ.hom = eM.hom ≫ g')
    (n : ℕ) (z' : Ext.{w'} Q' Y' n) (hz' : z' ≠ 0)
    (hkernel : (Ext.mk₀.{w'} g').comp z' (zero_add n) = 0) :
    ∃ z : Ext.{w} Q Y n, z ≠ 0 ∧
      (Ext.mk₀.{w} g).comp z (zero_add n) = 0 := by
  let e := extAddEquivOfExactEquivalenceOfIsos E Q Y Q' Y' eQ eY n
  refine ⟨e.symm z', ?_, ?_⟩
  · intro hz
    apply hz'
    have h := congrArg e hz
    simpa only [AddEquiv.apply_symm_apply, map_zero] using h
  · apply (extAddEquivOfExactEquivalenceOfIsos E M Y M' Y' eM eY n).injective
    rw [extAddEquivOfExactEquivalenceOfIsos_precomp E g g' eM eQ eY hsquare]
    change (Ext.mk₀.{w'} g').comp (e (e.symm z')) (zero_add n) = _
    rw [AddEquiv.apply_symm_apply, hkernel, map_zero]

end PfaffianDescent
