import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

namespace PfaffianDescent

open CategoryTheory Abelian

universe u v w w'

section

variable {𝒞 : Type u} [Category.{v} 𝒞] [Abelian 𝒞] [HasExt.{w} 𝒞]

/-- The universe-change equivalence for Ext groups preserves addition. -/
noncomputable def extChgUnivAddEquiv [HasExt.{w'} 𝒞]
    {X Y : 𝒞} {n : ℕ} : Ext.{w} X Y n ≃+ Ext.{w'} X Y n where
  toEquiv := Ext.chgUniv
  map_add' x y := by
    let := HasDerivedCategory.standard 𝒞
    apply Ext.homEquiv.injective
    change Ext.homEquiv (Ext.chgUniv.{w'} (x + y)) =
      Ext.homEquiv (Ext.chgUniv.{w'} x + Ext.chgUniv.{w'} y)
    calc
      Ext.homEquiv (Ext.chgUniv.{w'} (x + y)) = Ext.homEquiv (x + y) :=
        Ext.homEquiv_chgUniv.{max u v, w', w} (x + y)
      _ = Ext.homEquiv x + Ext.homEquiv y := Ext.add_hom x y
      _ = Ext.homEquiv (Ext.chgUniv.{w'} x) +
          Ext.homEquiv (Ext.chgUniv.{w'} y) := by
        rw [Ext.homEquiv_chgUniv.{max u v, w', w} x,
          Ext.homEquiv_chgUniv.{max u v, w', w} y]
      _ = Ext.homEquiv
          (Ext.chgUniv.{w'} x + Ext.chgUniv.{w'} y) :=
        (Ext.add_hom (Ext.chgUniv.{w'} x) (Ext.chgUniv.{w'} y)).symm

/-- The degree-zero Ext/Hom additive equivalence turns contravariant
precomposition in Ext into ordinary composition of morphisms. -/
lemma ext_addEquiv₀_precomp {X Y Z : 𝒞} (f : X ⟶ Y) (x : Ext Y Z 0) :
    Ext.addEquiv₀ ((Ext.mk₀ f).precomp Z (zero_add 0) x) =
      f ≫ Ext.addEquiv₀ x := by
  apply (Ext.mk₀_bijective _ _).injective
  rw [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
  rfl

/-- In a short exact sequence, degree-`n` Ext against the quotient vanishes
when degrees `n` and `n+1` vanish against the middle and left terms. -/
lemma ext_subsingleton_X3_of_shortExact
    {X : 𝒞} {S : ShortComplex 𝒞} (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext X S.X₂ n)] [Subsingleton (Ext X S.X₁ (n + 1))] :
    Subsingleton (Ext X S.X₃ n) := by
  apply subsingleton_of_forall_eq 0
  intro x
  have hx : x.comp hS.extClass (by omega : n + 1 = n + 1) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ X hS x (by omega) hx
  rw [show y = 0 by exact Subsingleton.elim _ _, Ext.zero_comp] at hy
  exact hy.symm

/-- If the middle object in a short exact sequence is projective, its
connecting map identifies degree-one Ext from the left object with degree-two
Ext from the quotient. -/
lemma extBoundary_one_two_bijective_of_projective_middle
    {S : ShortComplex 𝒞} (hS : S.ShortExact) (Y : 𝒞) [Projective S.X₂] :
    Function.Bijective (hS.extClass.precomp Y (show 1 + 1 = 2 by omega)) := by
  constructor
  · intro x y hxy
    have hzero : hS.extClass.comp (x - y) (show 1 + 1 = 2 by omega) = 0 := by
      change (hS.extClass.precomp Y (show 1 + 1 = 2 by omega)) (x - y) = 0
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₁ hS Y (x - y)
      (show 1 + 1 = 2 by omega) hzero
    have hz0 : z = 0 := Ext.eq_zero_of_projective z
    rw [hz0, Ext.comp_zero] at hz
    exact sub_eq_zero.mp hz.symm
  · intro z
    have hzero : (Ext.mk₀ S.g).comp z (zero_add 2) = 0 :=
      Ext.eq_zero_of_projective ((Ext.mk₀ S.g).comp z (zero_add 2))
    obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₃ hS Y z hzero
      (show 1 + 1 = 2 by omega)
    exact ⟨x, hx⟩

/-- Three short exact sequences shift Ext-vanishing down three places.  This
is the homological calculation used to exclude an irrelevant socle from a
length-three free resolution over a polynomial ring. -/
lemma ext_subsingleton_X3_of_three_shortExact
    {X A B C₀ D E F G : 𝒞}
    {f₀ : A ⟶ B} {g₀ : B ⟶ C₀} (hfg₀ : f₀ ≫ g₀ = 0)
    (h₀ : (ShortComplex.mk f₀ g₀ hfg₀).ShortExact)
    {f₁ : C₀ ⟶ D} {g₁ : D ⟶ E} (hfg₁ : f₁ ≫ g₁ = 0)
    (h₁ : (ShortComplex.mk f₁ g₁ hfg₁).ShortExact)
    {f₂ : E ⟶ F} {g₂ : F ⟶ G} (hfg₂ : f₂ ≫ g₂ = 0)
    (h₂ : (ShortComplex.mk f₂ g₂ hfg₂).ShortExact)
    [Subsingleton (Ext X F 0)] [Subsingleton (Ext X D 1)]
    [Subsingleton (Ext X B 2)] [Subsingleton (Ext X A 3)] :
    Subsingleton (Ext X G 0) := by
  have hC : Subsingleton (Ext X C₀ 2) :=
    ext_subsingleton_X3_of_shortExact h₀ 2
  have hE : Subsingleton (Ext X E 1) :=
    ext_subsingleton_X3_of_shortExact h₁ 1
  exact ext_subsingleton_X3_of_shortExact h₂ 0

end

end PfaffianDescent
