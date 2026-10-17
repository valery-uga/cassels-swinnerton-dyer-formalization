import PfaffianDescent.QuadraticSkewHomogeneousChartUnitEvaluation
/-! SOURCE ONLY / UNVERIFIED. Naturality and injectivity for the actual
unit-valued homogeneous chart evaluation. These are ring identities; no
scheme-map equality or rationality certificate is supplied. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.UnitChart005
open HomogeneousLocalization
universe u v w w'
variable {R : Type u} {A : Type v} {B : Type w} {C : Type w'}
variable [CommRing R] [CommRing A] [CommRing B] [CommRing C] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜] (z : A)

theorem liftUnit_comp (e : A →+* B) (he : IsUnit (e z)) (f : B →+* C) :
    f.comp (UnitChart004.liftUnit 𝒜 z e he) =
      UnitChart004.liftUnit 𝒜 z (f.comp e) (he.map f) := by
  let L := Localization (.powers z)
  have h : f.comp (IsLocalization.Away.lift z he : L →+* B) =
      (IsLocalization.Away.lift z (g := f.comp e) (he.map f) : L →+* C) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers z)
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq]
  apply RingHom.ext
  intro a
  exact RingHom.congr_fun h (algebraMap (Away 𝒜 z) L a)

/-- An injective coordinate-ring evaluation gives an injective evaluation
of its actual homogeneous chart. No domain or field extension certificate
is needed here; injectivity is transferred through localization itself. -/
theorem liftUnit_injective (e : A →+* B) (he : IsUnit (e z))
    (heinj : Function.Injective e) :
    Function.Injective (UnitChart004.liftUnit 𝒜 z e he) := by
  let L := Localization (.powers z)
  let l : L →+* B := IsLocalization.Away.lift z he
  have hlinj : Function.Injective l := by
    apply (IsLocalization.lift_injective_iff
      (show ∀ a : Submonoid.powers z, IsUnit (e a) from by
        rintro ⟨a, n, rfl⟩
        simpa only [map_pow] using he.pow n)).mpr
    intro a b
    constructor
    · intro h
      have h' := congrArg l h
      simpa only [l, IsLocalization.Away.lift_eq] using h'
    · intro h
      exact congrArg (algebraMap A L) (heinj h)
  exact hlinj.comp (HomogeneousLocalization.val_injective (.powers z))

end PfaffianDescent.QuadraticSkewRationality.UnitChart005
