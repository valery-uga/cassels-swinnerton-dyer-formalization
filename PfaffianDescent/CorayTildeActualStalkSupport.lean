import PfaffianDescent.CorayFractionFieldFiniteDefect
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! Actual sheaf support, detected by actual stalks, on the literal tilde model.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual support of an actual module sheaf: the actual nonzero stalk locus. -/
def schemeModuleStalkSupport {X : Scheme.{u}} (M : X.Modules) : Set X :=
  {x | Nontrivial (M.presheaf.stalk x)}

/-- The ACTUAL stalk of M-tilde is nonzero exactly at the ACTUAL module
support. This is the installed actual localization toStalk, not a certificate. -/
theorem tilde_actualStalkSupport_eq {A : CommRingCat.{u}} (M : ModuleCat A) :
    schemeModuleStalkSupport (tilde M) = Module.support A M := by
  ext x
  letI : x.asIdeal.IsPrime := x.isPrime
  change Nontrivial ((tilde M).presheaf.stalk x) ↔
    Nontrivial (LocalizedModule x.asIdeal.primeCompl M)
  exact (IsLocalizedModule.iso x.asIdeal.primeCompl (tilde.toStalk M x).hom).toEquiv.nontrivial_congr.symm

/-- The ACTUAL tilde normalization quotient in the ACTUAL fraction field is
supported at finitely many actual scheme points, with finiteness derived. -/
theorem tilde_normalizationDefect_actualStalkSupport_finite
    (K A F : Type u) [Field K] [CharZero K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] [Ring.DimensionLEOne A]
    [Field F] [Algebra A F] [IsFractionRing A F] :
    (schemeModuleStalkSupport
      (tilde (R := CommRingCat.of A) (ModuleCat.of A (localNormalizationDefect A F)))).Finite := by
  rw [tilde_actualStalkSupport_eq]
  exact finiteTypeCurve_normalizationDefect_support_finite_in_fractionField K A F

end PfaffianDescent.Coray
