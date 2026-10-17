import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! A pair over actual local rings is proper from its literal parameter
images. The independent Ext lemma only reflects a nonzero endpoint pullback. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
universe u u' v v' w w'

/-- Both original generators belong to the source maximal ideal. No proper
ideal assumption is needed: the literal images are zero and a nonunit. -/
lemma localParameterPair_mem_maximal220
    {R B : Type u} [CommRing R] [CommRing B] [IsLocalRing R] [IsLocalRing B]
    (phi : R →+* B) [IsLocalHom phi] (f g : R) (t : B)
    (hf : phi f = 0) (ht : t ∈ maximalIdeal B) (hg : phi g = t) :
    f ∈ maximalIdeal R ∧ g ∈ maximalIdeal R ∧
      (1 : R) ∉ Ideal.span ({f, g} : Set R) := by
  have hfm : f ∈ maximalIdeal R := by
    rw [← maximalIdeal_comap phi]
    change phi f ∈ maximalIdeal B
    rw [hf]
    exact Ideal.zero_mem _
  have hgm : g ∈ maximalIdeal R := by
    rw [← maximalIdeal_comap phi]
    change phi g ∈ maximalIdeal B
    rw [hg]
    exact ht
  have hle : Ideal.span ({f, g} : Set R) ≤ maximalIdeal R := by
    apply Ideal.span_le.mpr
    intro r hr
    rcases Set.mem_insert_iff.mp hr with rfl | hr
    · exact hfm
    · exact Set.mem_singleton_iff.mp hr ▸ hgm
  refine ⟨hfm, hgm, ?_⟩
  intro h1
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr (hle h1))

/-- A nonzero native endpoint pullback forces the original class nonzero;
this does not assert injectivity of any global-unit or trace map. -/
lemma ext_ne_zero_of_nativeEndpointPullback220
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {M N : C} {P O : D} (z : Ext.{w} M N 2)
    (lambda : P ⟶ F.obj M) (b : F.obj N ⟶ O)
    (h : (Ext.mk₀ lambda).comp ((z.mapExactFunctor F).comp (Ext.mk₀ b)
      (add_zero 2)) (zero_add 2) ≠ 0) : z ≠ 0 := by
  intro hz
  apply h
  rw [hz, Ext.mapExactFunctor_zero, Ext.zero_comp, Ext.comp_zero]

end PfaffianDescent
