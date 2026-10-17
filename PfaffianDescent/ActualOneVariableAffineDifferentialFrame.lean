import PfaffianDescent.ActualAffineDifferentialGenuineToTildeIso
import PfaffianDescent.AffineQuotientPushforwardTilde
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.Finsupp.Pi

/- SOURCE ONLY / UNVERIFIED. Genuine one-variable affine differential frames;
not a supplied locally-free or canonical-bundle certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [CommRing K] {σ : Type} [Subsingleton σ]

/-- The actual polynomial differential module, with the named coordinate a. -/
def oneVariablePolynomialKaehlerFrame (a : σ) :
    KaehlerDifferential K (MvPolynomial σ K) ≃ₗ[MvPolynomial σ K] MvPolynomial σ K :=
  (KaehlerDifferential.mvPolynomialBasis K σ).repr.trans
    (Finsupp.uniqueLinearEquiv (MvPolynomial σ K) (MvPolynomial σ K) a)

lemma oneVariablePolynomialKaehlerFrame_D (a : σ) :
    oneVariablePolynomialKaehlerFrame (K := K) a
      (KaehlerDifferential.D K (MvPolynomial σ K) (MvPolynomial.X a)) = 1 := by
  classical
  change (Finsupp.uniqueLinearEquiv (MvPolynomial σ K) (MvPolynomial σ K) a)
    ((KaehlerDifferential.mvPolynomialBasis K σ).repr
      (KaehlerDifferential.D K (MvPolynomial σ K) (MvPolynomial.X a))) = 1
  rw [KaehlerDifferential.mvPolynomialBasis_repr_D_X]
  simp

/-- A frame for the GENUINELY sheafified relative Omega on the SAME affine
polynomial spectrum over its ORIGINAL coefficient map. No Iso premise. -/
def actualOneVariableAffineDifferentialFrameIso (a : σ) :
    schemeRelativeDifferentials
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K)))) ≅
      SheafOfModules.unit (Spec (.of (MvPolynomial σ K))).ringCatSheaf :=
  actualAffineDifferentialGenuineToTildeIso (k := K) (R := MvPolynomial σ K) ≪≫
    (tilde.functor (.of (MvPolynomial σ K))).mapIso
      (oneVariablePolynomialKaehlerFrame (K := K) a).toModuleIso ≪≫
    (tildeSelf (R := CommRingCat.of (MvPolynomial σ K)))

end PfaffianDescent
end
