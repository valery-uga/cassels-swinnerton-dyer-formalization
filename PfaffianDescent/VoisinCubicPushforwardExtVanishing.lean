import PfaffianDescent.VoisinHypersurfaceTwist
import PfaffianDescent.VoisinStandardOpenExtVanishing
import PfaffianDescent.VoisinP3TopCechExtComparison

/-!
# Local Ext vanishing for a pushed-forward cubic twist

On every ordered coordinate intersection in projective three-space, the
degree-one and degree-two Ext groups from the section representer into
`i_* O_S(-m)` vanish.  This follows from the cubic restriction sequence and
the already proved affine acyclicity of its two ambient twists.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent.ProjectiveNegativeTwist

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The pushed-forward intrinsic cubic twist is Ext-acyclic in degrees one
and two on every ordered intersection of standard ambient coordinate opens. -/
theorem cubicPushforwardNegativeTwistCechInter_ext_one_and_two_subsingleton
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    (m n : ℕ) (f : Fin (n + 1) → Fin 4) :
    let U : Scheme.Opens (Proj PS) :=
      ⨅ i, p3StandardOpen K (f i)
    let P : (Proj PS).Modules :=
      sectionRepresenter (Proj PS).ringCatSheaf U
    let M : (Proj PS).Modules :=
      (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (sheafOfModules (grading (equationIdeal p hp)) m)
    Subsingleton (Ext.{u} P M 1) ∧ Subsingleton (Ext.{u} P M 2) := by
  dsimp only
  let U : Scheme.Opens (Proj PS) := ⨅ i, p3StandardOpen K (f i)
  let P : (Proj PS).Modules := sectionRepresenter (Proj PS).ringCatSheaf U
  let S := hypersurfaceTwistRestrictionSequence p hp m
  have hS : S.ShortExact :=
    hypersurfaceTwistRestrictionSequence_shortExact p hp hp0 m
  have hmid :=
    p3NegativeTwistCechInter_sectionRepresenter_ext_one_two_three_subsingleton
      K m n f
  have hleft :=
    p3NegativeTwistCechInter_sectionRepresenter_ext_one_two_three_subsingleton
      K (m + 3) n f
  letI hmid1 : Subsingleton (Ext.{u} P S.X₂ 1) := by
    change Subsingleton (Ext.{u} P (sheafOfModules PS m) 1)
    exact hmid.1
  letI hmid2 : Subsingleton (Ext.{u} P S.X₂ 2) := by
    change Subsingleton (Ext.{u} P (sheafOfModules PS m) 2)
    exact hmid.2.1
  letI hleft2 : Subsingleton (Ext.{u} P S.X₁ 2) := by
    change Subsingleton (Ext.{u} P (sheafOfModules PS (m + 3)) 2)
    exact hleft.2.1
  letI hleft3 : Subsingleton (Ext.{u} P S.X₁ 3) := by
    change Subsingleton (Ext.{u} P (sheafOfModules PS (m + 3)) 3)
    exact hleft.2.2
  have h1 : Subsingleton (Ext.{u} P S.X₃ 1) :=
    ext_subsingleton_of_middle_and_next_left P S hS 1
  have h2 : Subsingleton (Ext.{u} P S.X₃ 2) :=
    ext_subsingleton_of_middle_and_next_left P S hS 2
  exact ⟨h1, h2⟩

/-- Every term of the ambient standard-cover section-representer chain is
Ext-acyclic in degrees one and two against the pushed-forward cubic twist. -/
theorem cubicPushforward_sectionRepresenterCechChain_ext_one_and_two_subsingleton
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    (m n : ℕ) :
    let M : (Proj PS).Modules :=
      (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (sheafOfModules (grading (equationIdeal p hp)) m)
    Subsingleton (Ext.{u} ((p3SectionRepresenterCechChain K).X n) M 1) ∧
      Subsingleton (Ext.{u} ((p3SectionRepresenterCechChain K).X n) M 2) := by
  dsimp only
  let M : (Proj PS).Modules :=
    (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
      (sheafOfModules (grading (equationIdeal p hp)) m)
  let V : ULift.{u} (Fin 4) → Scheme.Opens (Proj PS) :=
    fun i => p3StandardOpen K i.down
  let X : (Fin (n + 1) → ULift.{u} (Fin 4)) → (Proj PS).Modules :=
    fun f => sectionRepresenter (Proj PS).ringCatSheaf
      (∏ᶜ fun i => V (f i))
  have hlocal (f : Fin (n + 1) → ULift.{u} (Fin 4)) :
      Subsingleton (Ext.{u} (X f) M 1) ∧
        Subsingleton (Ext.{u} (X f) M 2) := by
    let g : Fin (n + 1) → Fin 4 := fun i => (f i).down
    let W : Scheme.Opens (Proj PS) := ⨅ i, p3StandardOpen K (g i)
    have hW := cubicPushforwardNegativeTwistCechInter_ext_one_and_two_subsingleton
      K p hp hp0 m n g
    have e : W = ∏ᶜ fun i => V (f i) :=
      (p3CechProduct_eq_inf K n g).symm
    simpa only [X, M, ← e] using hW
  letI h₁ : ∀ f, Subsingleton (Ext.{u} (X f) M 1) :=
    fun f => (hlocal f).1
  letI h₂ : ∀ f, Subsingleton (Ext.{u} (X f) M 2) :=
    fun f => (hlocal f).2
  dsimp only [p3SectionRepresenterCechChain]
  rw [sectionRepresenterCechChain_obj]
  change Subsingleton (Ext.{u} (∐ X) M 1) ∧
    Subsingleton (Ext.{u} (∐ X) M 2)
  exact ⟨ext_finite_coproduct_subsingleton X M 1,
    ext_finite_coproduct_subsingleton X M 2⟩

end PfaffianDescent.ProjectiveNegativeTwist
