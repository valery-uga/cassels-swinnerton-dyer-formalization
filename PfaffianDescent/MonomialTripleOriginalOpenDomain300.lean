import PfaffianDescent.MonomialTripleSchemeRotation300
import Mathlib.AlgebraicGeometry.Gluing

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

private lemma nativeOriginalOpenInclusion300 {X : Scheme.{u}} (U : X.Opens) :
    IsOpenImmersion (Scheme.Opens.ι (X := X) U) := by infer_instance

variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B C D : Fin n → (Fin m →₀ ℕ)) (kB : Fin n) (hkB : B kB = 0)

/-- SAME literal inclusion of the original determinant open into its original coefficient chart. -/
def monomialOverlapOriginalOpenInclusion300 :
    monomialOverlapPrincipalScheme298 R m n B C kB hkB ⟶
      Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n B kB)) :=
  Scheme.Opens.ι (X := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n B kB)))
    (PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n B C kB hkB))

lemma monomialOverlapOriginalOpenInclusion_isOpenImmersion300 :
    IsOpenImmersion (monomialOverlapOriginalOpenInclusion300 R m n B C kB hkB) :=
  nativeOriginalOpenInclusion300
    (X := Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n B kB)))
    (PrimeSpectrum.basicOpen (universalMonomialOverlapDet292 R m n B C kB hkB) :
      (Spec (.of (UniversalCyclicCoefficientAlgebra282 R m n B kB))).Opens)

/-- Actual first projection of the genuine triple domain to the original B/C open. -/
def monomialTripleOriginalFirstMap300 :
    monomialTripleOverlapScheme300 R m n B C D kB hkB ⟶
      monomialOverlapPrincipalScheme298 R m n B C kB hkB :=
  monomialTripleOverlapFirstSchemeMap300 R m n B C D kB hkB ≫
    (monomialOverlapPrincipalOpenIso294 R m n B C kB hkB).hom

/-- Actual second projection to the original B/D open, internally constructed via292. -/
def monomialTripleOriginalSecondMap300 :
    monomialTripleOverlapScheme300 R m n B C D kB hkB ⟶
      monomialOverlapPrincipalScheme298 R m n B D kB hkB :=
  monomialTripleOverlapFirstLastSchemeMap300 R m n B C D kB hkB ≫
    (monomialOverlapPrincipalOpenIso294 R m n B D kB hkB).hom

/-- Genuine domain identification for the EXACT original open-inclusion maps. -/
lemma monomialTripleOriginalOpen_isPullback300 :
    IsPullback
      (monomialTripleOriginalFirstMap300 R m n B C D kB hkB)
      (monomialTripleOriginalSecondMap300 R m n B C D kB hkB)
      (monomialOverlapOriginalOpenInclusion300 R m n B C kB hkB)
      (monomialOverlapOriginalOpenInclusion300 R m n B D kB hkB) :=
  nativePullbackSidesTransport300
    (monomialTripleOverlapFirstSchemeMap300 R m n B C D kB hkB)
    (monomialTripleOverlapFirstLastSchemeMap300 R m n B C D kB hkB)
    (monomialOverlapPrincipalOpenMap294 R m n B C kB hkB)
    (monomialOverlapPrincipalOpenMap294 R m n B D kB hkB)
    (monomialTripleOverlap_isPullback300 R m n B C D kB hkB)
    (monomialOverlapPrincipalOpenIso294 R m n B C kB hkB)
    (monomialOverlapPrincipalOpenIso294 R m n B D kB hkB)
    (monomialOverlapOriginalOpenInclusion300 R m n B C kB hkB)
    (monomialOverlapOriginalOpenInclusion300 R m n B D kB hkB)
    (monomialOverlapPrincipalOpenIso_hom_fac294 R m n B C kB hkB)
    (monomialOverlapPrincipalOpenIso_hom_fac294 R m n B D kB hkB)

/-- The original triple pullback object is isomorphic to the actual double localization. -/
def monomialTripleOriginalPullbackIso300 :
    monomialTripleOverlapScheme300 R m n B C D kB hkB ≅
      pullback
        (monomialOverlapOriginalOpenInclusion300 R m n B C kB hkB)
        (monomialOverlapOriginalOpenInclusion300 R m n B D kB hkB) :=
  (monomialTripleOriginalOpen_isPullback300 R m n B C D kB hkB).isoPullback

lemma monomialTripleOriginalPullbackIso_hom_fst300 :
    (monomialTripleOriginalPullbackIso300 R m n B C D kB hkB).hom ≫ pullback.fst _ _ =
      monomialTripleOriginalFirstMap300 R m n B C D kB hkB :=
  (monomialTripleOriginalOpen_isPullback300 R m n B C D kB hkB).isoPullback_hom_fst

lemma monomialTripleOriginalPullbackIso_hom_snd300 :
    (monomialTripleOriginalPullbackIso300 R m n B C D kB hkB).hom ≫ pullback.snd _ _ =
      monomialTripleOriginalSecondMap300 R m n B C D kB hkB :=
  (monomialTripleOriginalOpen_isPullback300 R m n B C D kB hkB).isoPullback_hom_snd

end PfaffianDescent
