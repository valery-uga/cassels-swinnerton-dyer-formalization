import PfaffianDescent.MonomialTripleOriginalOpenDomain300

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B C D : Fin n → (Fin m →₀ ℕ)) (kB kC : Fin n)
variable (hkB : B kB = 0) (hkC : C kC = 0)

/-- Exact presentation square of the SAME298 pairwise principal-open Iso. -/
lemma monomialOverlapPrincipalSchemeIso_transport300 :
    (monomialOverlapPrincipalOpenIso294 R m n B C kB hkB).hom ≫
        (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).hom =
      (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC).hom ≫
        (monomialOverlapPrincipalOpenIso294 R m n C B kC hkC).hom :=
  nativePrincipalPairTransition_fac300
    (monomialOverlapPrincipalOpenIso294 R m n B C kB hkB)
    (monomialOverlapPrincipalOpenIso294 R m n C B kC hkC)
    (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC)

/-- Actual triple map square for the ORIGINAL298 principal-open transition. -/
lemma monomialTripleSchemeRotate_originalPairFac300 :
    monomialTripleSchemeRotate300 R m n B C D kB kC hkB hkC ≫
        monomialTripleOriginalSecondMap300 R m n C D B kC hkC =
      monomialTripleOriginalFirstMap300 R m n B C D kB hkB ≫
        (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).hom := by
  calc
    _ = monomialTripleOverlapFirstSchemeMap300 R m n B C D kB hkB ≫
        (monomialOverlapAffineSchemeIso298 R m n B C kB kC hkB hkC).hom ≫
        (monomialOverlapPrincipalOpenIso294 R m n C B kC hkC).hom := by
      have h := congrArg
        (fun f => f ≫ (monomialOverlapPrincipalOpenIso294 R m n C B kC hkC).hom)
        (monomialTripleSchemeRotate_pairFac300 R m n B C D kB kC hkB hkC)
      simpa only [monomialTripleOriginalSecondMap300, Category.assoc] using h
    _ = _ := by
      have h := congrArg
        (fun f => monomialTripleOverlapFirstSchemeMap300 R m n B C D kB hkB ≫ f)
        (monomialOverlapPrincipalSchemeIso_transport300
          (R := R) (m := m) (n := n) (B := B) (C := C)
          (kB := kB) (kC := kC) (hkB := hkB) (hkC := hkC)).symm
      simpa only [monomialTripleOriginalFirstMap300, Category.assoc] using h

/-- Actual t' between the two pullbacks of original determinant-open inclusions.
Both domain identifications and the intermediate triple map are constructed internally. -/
def monomialTripleOriginalPullbackTransition300 :
    pullback
        (monomialOverlapOriginalOpenInclusion300 R m n B C kB hkB)
        (monomialOverlapOriginalOpenInclusion300 R m n B D kB hkB) ⟶
      pullback
        (monomialOverlapOriginalOpenInclusion300 R m n C D kC hkC)
        (monomialOverlapOriginalOpenInclusion300 R m n C B kC hkC) :=
  (monomialTripleOriginalPullbackIso300 R m n B C D kB hkB).inv ≫
    monomialTripleSchemeRotate300 R m n B C D kB kC hkB hkC ≫
    (monomialTripleOriginalPullbackIso300 R m n C D B kC hkC).hom

/-- EXACT Scheme.GlueData.t_fac for the SAME original298 transition, with
no domain/cocycle certificate hypothesis. -/
lemma monomialTripleOriginalPullbackTransition_fac300 :
    monomialTripleOriginalPullbackTransition300 R m n B C D kB kC hkB hkC ≫
        pullback.snd _ _ =
      pullback.fst _ _ ≫
        (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).hom := by
  apply nativeTripleConjugate_fac300
    (monomialTripleOriginalPullbackIso300 R m n B C D kB hkB)
    (monomialTripleOriginalPullbackIso300 R m n C D B kC hkC)
    (monomialTripleSchemeRotate300 R m n B C D kB kC hkB hkC)
    (pullback.snd _ _) (pullback.fst _ _)
    (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).hom
  calc
    _ = monomialTripleSchemeRotate300 R m n B C D kB kC hkB hkC ≫
        monomialTripleOriginalSecondMap300 R m n C D B kC hkC :=
      congrArg (fun f => monomialTripleSchemeRotate300 R m n B C D kB kC hkB hkC ≫ f)
        (monomialTripleOriginalPullbackIso_hom_snd300 R m n C D B kC hkC)
    _ = monomialTripleOriginalFirstMap300 R m n B C D kB hkB ≫
        (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).hom :=
      monomialTripleSchemeRotate_originalPairFac300 R m n B C D kB kC hkB hkC
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ (monomialOverlapPrincipalSchemeIso298 R m n B C kB kC hkB hkC).hom)
        (monomialTripleOriginalPullbackIso_hom_fst300 R m n B C D kB hkB).symm

variable (kD : Fin n) (hkD : D kD = 0)

/-- EXACT threefold Scheme.GlueData.cocycle on actual original pullback domains.
It is derived from original coefficient/whole-ideal rotations and true Cartesian domain Isos. -/
lemma monomialTripleOriginalPullbackTransition_cycle300 :
    monomialTripleOriginalPullbackTransition300 R m n B C D kB kC hkB hkC ≫
        monomialTripleOriginalPullbackTransition300 R m n C D B kC kD hkC hkD ≫
        monomialTripleOriginalPullbackTransition300 R m n D B C kD kB hkD hkB =
      𝟙 (pullback
        (monomialOverlapOriginalOpenInclusion300 R m n B C kB hkB)
        (monomialOverlapOriginalOpenInclusion300 R m n B D kB hkB)) :=
  nativeTripleConjugate_cycle300
    (monomialTripleOriginalPullbackIso300 R m n B C D kB hkB)
    (monomialTripleOriginalPullbackIso300 R m n C D B kC hkC)
    (monomialTripleOriginalPullbackIso300 R m n D B C kD hkD)
    (monomialTripleSchemeRotate300 R m n B C D kB kC hkB hkC)
    (monomialTripleSchemeRotate300 R m n C D B kC kD hkC hkD)
    (monomialTripleSchemeRotate300 R m n D B C kD kB hkD hkB)
    (monomialTripleSchemeRotate_cycle300 R m n B C D kB kC hkB hkC kD hkD)

end PfaffianDescent
