import PfaffianDescent.SectionRepresenterCech
import PfaffianDescent.SectionRepresenterScalar
import PfaffianDescent.SmallCoverSectionRepresenterCechDifferential

/-!
# Coefficient morphisms in section-representer Cech coordinates

Postcomposition of an abstract Hom cochain is literally application of the
coefficient morphism on each intersection section. Together with resolution
naturality, this identifies coefficient multiplication before and after the
Cech-to-Ext comparison.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace PfaffianDescent
universe u
variable {C : Type u} [SmallCategory C] [HasFiniteProducts C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.isDefEq.respectTransparency false in
/-- Coefficient postcomposition acts on each raw intersection section. -/
theorem sectionRepresenterCechHomEquivPi_postcomp
    {ι : Type u} (U : ι → C) {M N : SheafOfModules.{u} R} (n : ℕ)
    (k : (sectionRepresenterCechChain R U).X n ⟶ M) (h : M ⟶ N)
    (f : Fin (n + 1) → ι) :
    sectionRepresenterCechHomEquivPi R U N n (k ≫ h) f =
      h.val.app (op (∏ᶜ fun i : Fin (n + 1) => U (f i)))
        (sectionRepresenterCechHomEquivPi R U M n k f) := by
  let B := fun g : Fin (n + 1) → ι =>
    sectionRepresenter R (∏ᶜ fun i : Fin (n + 1) => U (g i))
  change sectionRepresenterHomEquiv R
    (∏ᶜ fun i : Fin (n + 1) => U (f i)) N (Sigma.ι B f ≫ (k ≫ h)) =
      h.val.app (op (∏ᶜ fun i : Fin (n + 1) => U (f i)))
        (sectionRepresenterHomEquiv R
          (∏ᶜ fun i : Fin (n + 1) => U (f i)) M (Sigma.ι B f ≫ k))
  rw [← Category.assoc, sectionRepresenterHomEquiv_postcomp]

set_option backward.isDefEq.respectTransparency false in
/-- In the small-cover complex used for cubic surfaces, coefficient
postcomposition acts on the same ordered intersection sections. -/
theorem smallCoverSectionHomEquiv_postcomp_apply
    {ι : Type} (U : ι → C) {M N : SheafOfModules.{u} R} (n : ℕ)
    (k : (sectionRepresenterCechChain R
      (fun j : ULift.{u} ι => U j.down)).X n ⟶ M) (h : M ⟶ N)
    (f : Fin (n + 1) → ι) :
    smallCoverCechTermEquivPi R U N n
      (smallCoverSectionHomEquiv R U N n (k ≫ h)) f =
      h.val.app (op (∏ᶜ fun i : Fin (n + 1) => U (f i)))
        (smallCoverCechTermEquivPi R U M n
          (smallCoverSectionHomEquiv R U M n k) f) := by
  rw [smallCoverSectionHomEquiv_apply, smallCoverSectionHomEquiv_apply]
  exact sectionRepresenterCechHomEquivPi_postcomp R
    (fun j : ULift.{u} ι => U j.down) n k h (fun j => ULift.up (f j))
end PfaffianDescent
