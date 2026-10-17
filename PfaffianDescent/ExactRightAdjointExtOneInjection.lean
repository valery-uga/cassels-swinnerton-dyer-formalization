import PfaffianDescent.ExtMapFixedSource
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! SOURCE ONLY / UNVERIFIED. The right-adjoint degree-one map is injective
when the right adjoint is exact. No exactness/linearity of the left adjoint,
and no preservation of injectives by either functor, is assumed. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe w w' v v' u u' r
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Apply the actual exact right adjoint and then precompose with the actual
adjunction unit. This is a map of the original Ext groups. -/
def rightAdjointExtAddHom
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [HasExt.{w} C] [HasExt.{w'} D]
    (X : C) (Y : D) (n : ℕ) :
    Ext.{w'} (F.obj X) Y n →+ Ext.{w} X (G.obj Y) n :=
  ((Ext.mk₀ (adj.unit.app X)).precomp (G.obj Y) (zero_add n)).comp
    (G.mapExtAddHom (F.obj X) Y n)

/-- In degree zero this is precisely the ordinary Hom adjunction. -/
theorem rightAdjointExtAddHom_mk₀
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [HasExt.{w} C] [HasExt.{w'} D]
    (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    rightAdjointExtAddHom F G adj X Y 0 (Ext.mk₀ f) =
      Ext.mk₀ (adj.homEquiv X Y f) := by
  change (Ext.mk₀ (adj.unit.app X)).comp
    ((Ext.mk₀ f).mapExactFunctor G) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Adjunction.homEquiv_unit]

/-- The same map commutes with the genuine connecting Ext class of every
short exact sequence. Only the right adjoint maps the sequence. -/
theorem rightAdjointExtAddHom_boundary
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [HasExt.{w} C] [HasExt.{w'} D]
    (X : C) (S : ShortComplex D) (hS : S.ShortExact)
    (n : ℕ) (z : Ext.{w'} (F.obj X) S.X₃ n) :
    rightAdjointExtAddHom F G adj X S.X₁ (n + 1)
        (z.comp hS.extClass rfl) =
      (rightAdjointExtAddHom F G adj X S.X₃ n z).comp
        (hS.map_of_exact G).extClass rfl := by
  change (Ext.mk₀ (adj.unit.app X)).comp
      ((z.comp hS.extClass rfl).mapExactFunctor G) (zero_add (n + 1)) =
    ((Ext.mk₀ (adj.unit.app X)).comp (z.mapExactFunctor G) (zero_add n)).comp
      (hS.map_of_exact G).extClass rfl
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

attribute [local instance] Ext.subsingleton_of_injective in
set_option backward.isDefEq.respectTransparency false in
/-- Genuine degree-one injectivity. An injective presentation is chosen in
D. Its connecting map is surjective; a mapped boundary in the kernel lifts
through G of the middle term. The ordinary adjunction transports that lift
back to D, so the original boundary is zero. G of the injective need not
be injective, and F need not preserve any exact sequence. -/
theorem rightAdjointExtAddHom_one_injective
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives D]
    (X : C) (Y : D) :
    Function.Injective (rightAdjointExtAddHom F G adj X Y 1) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro z hz
  let I : InjectivePresentation Y := Classical.arbitrary _
  let S := ShortComplex.mk _ _ (cokernel.condition I.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
  have hSG : (S.map G).ShortExact := hS.map_of_exact G
  have hzI : z.comp (Ext.mk₀ S.f) (add_zero 1) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨q, hq⟩ := Ext.covariant_sequence_exact₁ (F.obj X) hS z hzI rfl
  let fq : F.obj X ⟶ S.X₃ := Ext.addEquiv₀ q
  let qC : X ⟶ (S.map G).X₃ := adj.homEquiv X S.X₃ fq
  have hqC : (Ext.mk₀ qC).comp hSG.extClass rfl = 0 := by
    calc
      (Ext.mk₀ qC).comp hSG.extClass rfl =
          (rightAdjointExtAddHom F G adj X S.X₃ 0 q).comp hSG.extClass rfl := by
        change (Ext.mk₀ (adj.homEquiv X S.X₃ fq)).comp hSG.extClass rfl = _
        rw [← rightAdjointExtAddHom_mk₀ F G adj X S.X₃ fq]
        dsimp only [fq]
        rw [Ext.mk₀_addEquiv₀_apply]
      _ = rightAdjointExtAddHom F G adj X S.X₁ 1 (q.comp hS.extClass rfl) :=
        (rightAdjointExtAddHom_boundary F G adj X S hS 0 q).symm
      _ = 0 := by rw [hq]; exact hz
  obtain ⟨pCext, hp⟩ := Ext.covariant_sequence_exact₃ X hSG (Ext.mk₀ qC) rfl hqC
  let pC : X ⟶ (S.map G).X₂ := Ext.addEquiv₀ pCext
  let pD : F.obj X ⟶ S.X₂ := (adj.homEquiv X S.X₂).symm pC
  have hLift : pD ≫ S.g = fq := by
    apply (adj.homEquiv X S.X₃).injective
    rw [adj.homEquiv_naturality_right]
    have hpD : adj.homEquiv X S.X₂ pD = pC :=
      Equiv.apply_symm_apply (adj.homEquiv X S.X₂) pC
    rw [hpD]
    change pC ≫ (S.map G).g = qC
    apply (Ext.mk₀_bijective X (S.map G).X₃).injective
    calc
      Ext.mk₀ (pC ≫ (S.map G).g) =
          (Ext.mk₀ pC).comp (Ext.mk₀ (S.map G).g) (add_zero 0) := by
        rw [Ext.mk₀_comp_mk₀]
      _ = pCext.comp (Ext.mk₀ (S.map G).g) (add_zero 0) := by
        rw [Ext.mk₀_addEquiv₀_apply]
      _ = Ext.mk₀ qC := hp
  rw [← hq, ← Ext.mk₀_addEquiv₀_apply q]
  change (Ext.mk₀ fq).comp hS.extClass rfl = 0
  rw [← hLift, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    hS.comp_extClass, Ext.comp_zero]

/-- Linearity uses only G.Linear for the independently specified original
R-linear categories. No linear left adjoint or linear adjunction is assumed. -/
def rightAdjointExtLinearMap
    (R : Type r) [Ring R] [Linear R C] [Linear R D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.Linear R]
    [HasExt.{w} C] [HasExt.{w'} D]
    (X : C) (Y : D) (n : ℕ) :
    Ext.{w'} (F.obj X) Y n →ₗ[R] Ext.{w} X (G.obj Y) n where
  __ := rightAdjointExtAddHom F G adj X Y n
  map_smul' r z := by
    change (Ext.mk₀ (adj.unit.app X)).comp ((r • z).mapExactFunctor G) (zero_add n) =
      r • (Ext.mk₀ (adj.unit.app X)).comp (z.mapExactFunctor G) (zero_add n)
    rw [Functor.mapExactFunctor_smul, Ext.comp_smul]

theorem rightAdjointExtLinearMap_one_injective
    (R : Type r) [Ring R] [Linear R C] [Linear R D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.Linear R]
    [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives D]
    (X : C) (Y : D) :
    Function.Injective (rightAdjointExtLinearMap R F G adj X Y 1) :=
  rightAdjointExtAddHom_one_injective F G adj X Y

end PfaffianDescent
