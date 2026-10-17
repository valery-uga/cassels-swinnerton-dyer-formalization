import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A field-valued injective chart map stays injective after localization
at an actual element with nonzero image. No birationality is assumed. -/
theorem localizationAway_fieldLift_injective_of_injective001
    {R F : Type u} [CommRing R] [Field F]
    (g : R →+* F) (hg : Function.Injective g) (r : R) (hr : g r ≠ 0) :
    Function.Injective (IsLocalization.Away.lift r (isUnit_iff_ne_zero.mpr hr) :
      Localization.Away r →+* F) := by
  let ell : Localization.Away r →+* F :=
    IsLocalization.Away.lift r (isUnit_iff_ne_zero.mpr hr)
  have hEll : ell.comp (algebraMap R (Localization.Away r)) = g :=
    IsLocalization.Away.lift_comp _ _
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers r) ell).mpr
  intro x y
  constructor
  · exact fun h => congrArg ell h
  · intro h
    have hxy : g x = g y := by
      exact (RingHom.congr_fun hEll x).symm.trans
        (h.trans (RingHom.congr_fun hEll y))
    exact congrArg (algebraMap R (Localization.Away r)) (hg hxy)

/-- Injection into a field gives an actual schematic-dominant Spec map.
Its precomposition leaves the full ideal sheaf kernel unchanged. -/
theorem injective_fieldSpec_precomposition_ker_eq001
    {R F : Type u} [CommRing R] [Field F] (g : R →+* F)
    (hg : Function.Injective g) {Y : Scheme.{u}} (f : Spec (.of R) ⟶ Y) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom g)) ∧
      (Spec.map (CommRingCat.ofHom g) ≫ f).ker = f.ker := by
  let tau := Spec.map (CommRingCat.ofHom g)
  letI : IsReduced R := isReduced_of_injective g hg
  letI : IsDominant tau := by
    constructor
    change DenseRange (PrimeSpectrum.comap g)
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g).mpr
    rw [(RingHom.injective_iff_ker_eq_bot g).mp hg]
    exact bot_le
  letI : IsSchemeTheoreticallyDominant tau := IsSchemeTheoreticallyDominant.of_isDominant tau
  refine ⟨inferInstance, ?_⟩
  rw [Scheme.Hom.ker_comp, tau.ker_eq_bot, Scheme.IdealSheafData.map_bot]

end PfaffianDescent.Coray
