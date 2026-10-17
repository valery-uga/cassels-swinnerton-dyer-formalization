import PfaffianDescent.PositiveThreeNativePowerFrame

/-! SOURCE ONLY. Literal homogeneous cubic fraction equals the CUBE of
its original normalized degree-one fraction. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open HomogeneousLocalization
universe u
variable {A ρ : Type u} [CommRing A] [SetLike ρ A] [AddSubgroupClass ρ A]
variable (G : ℕ → ρ) [GradedRing G]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem nativeAway_degreeOnePower_cubicRatio (ell eta : G 1) :
    Away.mk G ell.property 3 ((degreeOnePower G eta 3 : G 3) : A)
      (by simpa only [smul_eq_mul, mul_one] using (degreeOnePower G eta 3).property) =
    (Away.mk G ell.property 1 (eta : A)
      (by simpa only [smul_eq_mul, mul_one, one_mul] using eta.property)) ^ 3 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_pow, Away.val_mk, degreeOnePower,
    Localization.mk_pow, pow_one]
  apply congrArg (fun d : Submonoid.powers (ell : A) =>
    Localization.mk ((eta : A) ^ 3) d)
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow, Subtype.coe_mk]

end PfaffianDescent.ProjectiveNegativeTwist
