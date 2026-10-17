import PfaffianDescent.ExactRightAdjointExtOneInjection

/-! SOURCE ONLY / UNVERIFIED160. Degree-one surjectivity of the SAME
right-adjoint Ext map from a single injective presentation whose image is
acyclic for the fixed source. The native geometric caller derives acyclicity
from injective flasqueness. No left-adjoint exactness is asserted. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe w w' v v' u u' r
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Dimension shifting and the genuine ordinary adjunction recover every
target Ext¹ class. Only this one chosen image needs to be acyclic. -/
theorem rightAdjointExtAddHom_one_surjective_of_presentation
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [HasExt.{w} C] [HasExt.{w'} D]
    (X : C) (Y : D) (I : InjectivePresentation Y)
    (hAcyclic : Subsingleton (Ext.{w} X (G.obj I.J) 1)) :
    Function.Surjective (rightAdjointExtAddHom F G adj X Y 1) := by
  let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
  have hSG : (S.map G).ShortExact := hS.map_of_exact G
  letI : Subsingleton (Ext.{w} X (S.map G).X₂ 1) := by
    change Subsingleton (Ext.{w} X (G.obj I.J) 1)
    exact hAcyclic
  intro z
  have hz : z.comp (Ext.mk₀ (S.map G).f) (add_zero 1) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨q, hq⟩ := Ext.covariant_sequence_exact₁ X hSG z hz rfl
  let fq : X ⟶ G.obj S.X₃ := Ext.addEquiv₀ q
  let qD : F.obj X ⟶ S.X₃ := (adj.homEquiv X S.X₃).symm fq
  have hqMap : rightAdjointExtAddHom F G adj X S.X₃ 0 (Ext.mk₀ qD) = q := by
    rw [rightAdjointExtAddHom_mk₀]
    change Ext.mk₀ ((adj.homEquiv X S.X₃)
      ((adj.homEquiv X S.X₃).symm fq)) = q
    rw [Equiv.apply_symm_apply]
    exact Ext.mk₀_addEquiv₀_apply q
  refine ⟨(Ext.mk₀ qD).comp hS.extClass rfl, ?_⟩
  change rightAdjointExtAddHom F G adj X S.X₁ (0 + 1)
    ((Ext.mk₀ qD).comp hS.extClass rfl) = z
  calc
    _ = (rightAdjointExtAddHom F G adj X S.X₃ 0 (Ext.mk₀ qD)).comp
        hSG.extClass rfl :=
      rightAdjointExtAddHom_boundary F G adj X S hS 0 (Ext.mk₀ qD)
    _ = z := by
      rw [hqMap]
      exact hq

/-- The linear map has the SAME underlying additive map, so its
surjectivity needs no new scalar action or linear-adjunction premise. -/
theorem rightAdjointExtLinearMap_one_surjective_of_presentation
    (R : Type r) [Ring R] [Linear R C] [Linear R D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.Linear R]
    [HasExt.{w} C] [HasExt.{w'} D]
    (X : C) (Y : D) (I : InjectivePresentation Y)
    (hAcyclic : Subsingleton (Ext.{w} X (G.obj I.J) 1)) :
    Function.Surjective (rightAdjointExtLinearMap R F G adj X Y 1) :=
  rightAdjointExtAddHom_one_surjective_of_presentation F G adj X Y I hAcyclic

end PfaffianDescent
