import PfaffianDescent.ActualAffineGenuineDifferentialForwardPointMap

/- SOURCE ONLY / UNVERIFIED. A genuine sheaf morphism constructed by
adjunction from the derived actual top universal differential. Its being
an Iso is a separate obligation, not a certificate premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]

/-- Actual tilde-adjoint of the actual canonical top differential map. -/
def actualAffineDifferentialTildeToGenuineSheaf :
    (tilde.functor (CommRingCat.of R)).obj
        (ModuleCat.of R (KaehlerDifferential k R)) ⟶
      schemeRelativeDifferentials
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  let M := ModuleCat.of R (KaehlerDifferential k R)
  let O := schemeRelativeDifferentials
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  let v : M ⟶ (moduleSpecΓFunctor (R := .of R)).obj O :=
    ModuleCat.ofHom (X := M) (Y := (moduleSpecΓFunctor (R := .of R)).obj O)
      (actualAffineDifferentialTopToGenuineSheaf (k := k) (R := R))
  exact ((tilde.adjunction (R := CommRingCat.of R)).homEquiv M O).symm v

lemma actualAffineDifferentialTildeToGenuineSheaf_adjunct :
    (tilde.adjunction (R := CommRingCat.of R)).homEquiv
      (ModuleCat.of R (KaehlerDifferential k R))
      (schemeRelativeDifferentials
        (Spec.map (CommRingCat.ofHom (algebraMap k R))))
      (actualAffineDifferentialTildeToGenuineSheaf (k := k) (R := R)) =
    ModuleCat.ofHom
      (X := ModuleCat.of R (KaehlerDifferential k R))
      (Y := (moduleSpecΓFunctor (R := .of R)).obj
        (schemeRelativeDifferentials
          (Spec.map (CommRingCat.ofHom (algebraMap k R)))))
      (actualAffineDifferentialTopToGenuineSheaf (k := k) (R := R)) :=
  Equiv.apply_symm_apply _ _

/-- The actual top action of the tilde adjoint, on every native differential. -/
lemma actualAffineDifferentialTildeToGenuineSheaf_unit (x : KaehlerDifferential k R) :
    (moduleSpecΓFunctor (R := .of R)).map
      (actualAffineDifferentialTildeToGenuineSheaf (k := k) (R := R))
      ((((tilde.toTildeΓNatIso (R := .of R)).app
        (ModuleCat.of R (KaehlerDifferential k R))).hom) x) =
    actualAffineDifferentialTopToGenuineSheaf (k := k) (R := R) x := by
  have h := actualAffineDifferentialTildeToGenuineSheaf_adjunct (k := k) (R := R)
  rw [Adjunction.homEquiv_unit] at h
  exact ConcreteCategory.congr_hom h x

/-- In particular, the true adjoint sends the canonical tilde top D to
    the genuine universal differential section. -/
lemma actualAffineDifferentialTildeToGenuineSheaf_D (r : R) :
    (moduleSpecΓFunctor (R := .of R)).map
      (actualAffineDifferentialTildeToGenuineSheaf (k := k) (R := R))
      ((((tilde.toTildeΓNatIso (R := .of R)).app
        (ModuleCat.of R (KaehlerDifferential k R))).hom)
          (KaehlerDifferential.D k R r)) =
    actualRelativeDifferentialSection
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤
      ((Scheme.ΓSpecIso (.of R)).inv.hom r) :=
  (actualAffineDifferentialTildeToGenuineSheaf_unit
    (k := k) (R := R) (KaehlerDifferential.D k R r)).trans
      (actualAffineDifferentialTopToGenuineSheaf_D (k := k) (R := R) r)

/-- Actual pullback of the sheaf morphism acts on the canonical tilde point
    class by the genuine D section class; this uses actual unit naturality. -/
lemma actualAffineDifferentialTildeToGenuineSheaf_point_D
    {S : Type u} [CommRing S] (rho : R →+* S) (r : R) :
    (moduleSpecΓFunctor (R := .of S)).map
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).map
        (actualAffineDifferentialTildeToGenuineSheaf (k := k) (R := R)))
      (affineTildeActualPointClass (CommRingCat.ofHom rho)
        (ModuleCat.of R (KaehlerDifferential k R))
          (KaehlerDifferential.D k R r)) =
    actualAffineSheafPointClass (CommRingCat.ofHom rho)
      (schemeRelativeDifferentials
        (Spec.map (CommRingCat.ofHom (algebraMap k R))))
      (actualRelativeDifferentialSection
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤
        ((Scheme.ΓSpecIso (.of R)).inv.hom r)) := by
  let phi := CommRingCat.ofHom rho
  let M := ModuleCat.of R (KaehlerDifferential k R)
  let O := schemeRelativeDifferentials
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  let A := actualAffineDifferentialTildeToGenuineSheaf (k := k) (R := R)
  let x := KaehlerDifferential.D k R r
  let u := ((tilde.toTildeΓNatIso (R := .of R)).app M).hom x
  let G := moduleSpecΓFunctor (R := .of R)
  let P := Scheme.Modules.pullback (Spec.map phi)
  let H := moduleSpecΓFunctor (R := .of S)
  have hT := affineTildeActualPointClass_eq_actualSheafPointClass phi M x
  have hN := actualAffineSheafPointClass_natural phi A u
  have hD := actualAffineDifferentialTildeToGenuineSheaf_D (k := k) (R := R) r
  change H.map (P.map A) (affineTildeActualPointClass phi M x) = _
  calc
    _ = H.map (P.map A)
        (actualAffineSheafPointClass phi ((tilde.functor (.of R)).obj M) u) :=
      congrArg (fun z => H.map (P.map A) z) hT
    _ = actualAffineSheafPointClass phi O (G.map A u) := hN.symm
    _ = actualAffineSheafPointClass phi O
        (actualRelativeDifferentialSection
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤
          ((Scheme.ΓSpecIso (.of R)).inv.hom r)) :=
      congrArg (fun z => actualAffineSheafPointClass phi O z) hD

end PfaffianDescent
