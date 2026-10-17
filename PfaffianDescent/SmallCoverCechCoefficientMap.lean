import PfaffianDescent.SectionRepresenterCechCoefficientNaturality

/-! # Actual coefficient morphisms on small-cover Cech complexes -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace PfaffianDescent
universe u
variable {C : Type u} [SmallCategory C] [HasFiniteProducts C]
variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {ι : Type} (U : ι → C)

def smallCoverCechCoefficientMap {M N : SheafOfModules.{u} R} (h : M ⟶ N) :
    smallCoverCechComplex R U M ⟶ smallCoverCechComplex R U N :=
  (CategoryTheory.cechComplexFunctor U).map ((PresheafOfModules.toPresheaf R.obj).map h.val)

set_option backward.isDefEq.respectTransparency false in
theorem smallCoverCechCoefficientMap_projection {M N : SheafOfModules.{u} R}
    (h : M ⟶ N) (n : ℕ) (f : Fin (n + 1) → ι) :
    (smallCoverCechCoefficientMap R U h).f n ≫ Pi.π (smallCoverCechTermFamily R U N n) f =
      Pi.π (smallCoverCechTermFamily R U M n) f ≫
        ((PresheafOfModules.toPresheaf R.obj).map h.val).app
          (op (∏ᶜ fun a : Fin (n + 1) => U (f a))) := by
  change (CategoryTheory.Limits.Pi.map
    (f := smallCoverCechTermFamily R U M n) (g := smallCoverCechTermFamily R U N n)
    fun f : Fin (n + 1) → ι =>
    ((PresheafOfModules.toPresheaf R.obj).map h.val).app
      (op (∏ᶜ fun a : Fin (n + 1) => U (f a)))) ≫ _ = _
  exact CategoryTheory.Limits.Pi.map_π _ f

set_option backward.isDefEq.respectTransparency false in
theorem smallCoverCechCoefficientMap_apply {M N : SheafOfModules.{u} R}
    (h : M ⟶ N) (n : ℕ) (x : (smallCoverCechComplex R U M).X n)
    (f : Fin (n + 1) → ι) :
    smallCoverCechTermEquivPi R U N n ((smallCoverCechCoefficientMap R U h).f n x) f =
      h.val.app (op (∏ᶜ fun a : Fin (n + 1) => U (f a)))
        (smallCoverCechTermEquivPi R U M n x f) := by
  exact CategoryTheory.congr_fun (smallCoverCechCoefficientMap_projection R U h n f) x

set_option backward.isDefEq.respectTransparency false in
theorem smallCoverSectionHomEquiv_postcomp {M N : SheafOfModules.{u} R}
    (h : M ⟶ N) (n : ℕ)
    (k : (sectionRepresenterCechChain R (fun j : ULift.{u} ι => U j.down)).X n ⟶ M) :
    smallCoverSectionHomEquiv R U N n (k ≫ h) =
      (smallCoverCechCoefficientMap R U h).f n (smallCoverSectionHomEquiv R U M n k) := by
  apply (smallCoverCechTermEquivPi R U N n).injective
  funext f
  exact (smallCoverSectionHomEquiv_postcomp_apply R U n k h f).trans
    (smallCoverCechCoefficientMap_apply R U h n _ f).symm

theorem smallCoverSectionHomEquiv_symm_coefficientMap {M N : SheafOfModules.{u} R}
    (h : M ⟶ N) (n : ℕ) (x : (smallCoverCechComplex R U M).X n) :
    (smallCoverSectionHomEquiv R U N n).symm
        ((smallCoverCechCoefficientMap R U h).f n x) =
      (smallCoverSectionHomEquiv R U M n).symm x ≫ h := by
  apply (smallCoverSectionHomEquiv R U N n).injective
  rw [Equiv.apply_symm_apply, smallCoverSectionHomEquiv_postcomp R U h n,
    Equiv.apply_symm_apply]

end PfaffianDescent
