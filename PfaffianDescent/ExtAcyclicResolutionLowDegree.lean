import PfaffianDescent.SheafModuleOverExtComparison

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace PfaffianDescent

universe u v w

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- Generic contravariant four-term Ext consequence: surjectivity at degree
`n` and vanishing on the middle term in degree `n+1` force vanishing on the
quotient. -/
theorem ext_succ_subsingleton_of_precomp_surjective
    (Y : A) (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ)
    (hsurj : Function.Surjective
      ((Ext.mk₀ S.f).precomp Y (zero_add n)))
    [Subsingleton (Ext S.X₂ Y (n + 1))] :
    Subsingleton (Ext S.X₃ Y (n + 1)) := by
  constructor
  intro x y
  suffices hzero : ∀ z : Ext S.X₃ Y (n + 1), z = 0 by
    exact (hzero x).trans (hzero y).symm
  intro z
  have hz : (Ext.mk₀ S.g).comp z (zero_add (n + 1)) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨z₀, hz₀⟩ := Ext.contravariant_sequence_exact₃
    hS Y z hz (show 1 + n = n + 1 by omega)
  obtain ⟨z₂, hz₂⟩ := hsurj z₀
  rw [← hz₀, ← hz₂]
  change hS.extClass.comp
    ((Ext.mk₀ S.f).comp z₂ (zero_add n))
    (show 1 + n = n + 1 by omega) = 0
  exact hS.extClass_comp_assoc z₂

/-- Ordinary Hom surjectivity is the degree-zero Ext surjectivity used by
`ext_succ_subsingleton_of_precomp_surjective`. -/
theorem ext_zero_precomp_surjective_of_hom
    (Y : A) (S : ShortComplex A)
    (hsurj : Function.Surjective (fun f : S.X₂ ⟶ Y => S.f ≫ f)) :
    Function.Surjective ((Ext.mk₀ S.f).precomp Y (zero_add 0)) := by
  intro q
  let fq : S.X₁ ⟶ Y := Ext.addEquiv₀ q
  obtain ⟨p, hp⟩ := hsurj fq
  change S.f ≫ p = fq at hp
  refine ⟨Ext.mk₀ p, ?_⟩
  change (Ext.mk₀ S.f).comp (Ext.mk₀ p) (zero_add 0) = q
  rw [Ext.mk₀_comp_mk₀, hp, ← Ext.mk₀_addEquiv₀_apply q]

/-- For a short exact sequence, surjectivity of restriction on ordinary Hom
and vanishing of `Ext¹` from the middle term kill `Ext¹` from the quotient. -/
theorem ext_one_subsingleton_of_hom_precomp_surjective
    (Y : A) (S : ShortComplex A) (hS : S.ShortExact)
    [Subsingleton (Ext S.X₂ Y 1)]
    (hsurj : Function.Surjective (fun f : S.X₂ ⟶ Y => S.f ≫ f)) :
    Subsingleton (Ext S.X₃ Y 1) := by
  exact ext_succ_subsingleton_of_precomp_surjective Y S hS 0
    (ext_zero_precomp_surjective_of_hom Y S hsurj)

/-- The dimension-shifting step on the contravariant side: vanishing in
previous degree on the kernel and in the current degree on the middle term
forces vanishing in the current degree on the quotient. -/
theorem ext_succ_subsingleton_X3_of_left_and_middle
    (Y : A) (S : ShortComplex A) (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext S.X₁ Y n)]
    [Subsingleton (Ext S.X₂ Y (n + 1))] :
    Subsingleton (Ext S.X₃ Y (n + 1)) := by
  apply subsingleton_of_forall_eq 0
  intro z
  have hz : (Ext.mk₀ S.g).comp z (zero_add (n + 1)) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₃
    hS Y z hz (show 1 + n = n + 1 by omega)
  rw [show x = 0 by exact Subsingleton.elim _ _, Ext.comp_zero] at hx
  exact hx.symm

omit [HasExt A] in
/-- Exactness of a three-term Hom complex supplies the Hom-lifting
condition against the image object, once the preceding map onto that image
is an epimorphism. -/
theorem hom_precomp_surjective_of_exact_and_epi
    {K C₀ C₁ C₂ : A} (Y : A)
    (f : K ⟶ C₀) (g : C₁ ⟶ K) [Epi g] (d : C₂ ⟶ C₁)
    (hd : d ≫ g = 0)
    (hexact : Function.Exact
      (fun h : C₀ ⟶ Y => (g ≫ f) ≫ h)
      (fun h : C₁ ⟶ Y => d ≫ h)) :
    Function.Surjective (fun h : C₀ ⟶ Y => f ≫ h) := by
  intro t
  have hcocycle : d ≫ (g ≫ t) = 0 := by
    rw [← Category.assoc, hd, Limits.zero_comp]
  obtain ⟨h, hh⟩ := (hexact (g ≫ t)).mp hcocycle
  refine ⟨h, ?_⟩
  apply (cancel_epi g).1
  simpa only [Category.assoc] using hh

/-- A two-step resolution whose first two terms are acyclic in the needed
ranges computes vanishing in degrees one and two from the two Hom-lifting
conditions.  These are precisely exactness of the Hom complex in Cech
degrees one and two after the resolution kernels are introduced. -/
theorem ext_one_and_two_subsingleton_of_two_step_acyclic_resolution
    (Y : A) (S₀ S₁ : ShortComplex A)
    (hS₀ : S₀.ShortExact) (hS₁ : S₁.ShortExact)
    (hmatch : S₁.X₃ = S₀.X₁)
    [Subsingleton (Ext S₀.X₂ Y 1)]
    [Subsingleton (Ext S₀.X₂ Y 2)]
    [Subsingleton (Ext S₁.X₂ Y 1)]
    (hsurj₀ : Function.Surjective
      (fun f : S₀.X₂ ⟶ Y => S₀.f ≫ f))
    (hsurj₁ : Function.Surjective
      (fun f : S₁.X₂ ⟶ Y => S₁.f ≫ f)) :
    Subsingleton (Ext S₀.X₃ Y 1) ∧
      Subsingleton (Ext S₀.X₃ Y 2) := by
  have h₁ : Subsingleton (Ext S₀.X₃ Y 1) :=
    ext_one_subsingleton_of_hom_precomp_surjective Y S₀ hS₀ hsurj₀
  have hK₁ : Subsingleton (Ext S₁.X₃ Y 1) :=
    ext_one_subsingleton_of_hom_precomp_surjective Y S₁ hS₁ hsurj₁
  have hK₀ : Subsingleton (Ext S₀.X₁ Y 1) := by
    rw [← hmatch]
    exact hK₁
  let _ : Subsingleton (Ext S₀.X₁ Y 1) := hK₀
  have h₂ : Subsingleton (Ext S₀.X₃ Y 2) :=
    ext_succ_subsingleton_X3_of_left_and_middle Y S₀ hS₀ 1
  exact ⟨h₁, h₂⟩

end PfaffianDescent
