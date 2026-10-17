import PfaffianDescent.ActualAffineDifferentialTildeToGenuineSheaf

/- Source-only: compare the actual forward map with actual tilde pullback.
No sheaf invertibility or differential-fiber dimension is presumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable {k R L : Type u} [CommRing k] [CommRing R] [Field L] [Algebra k R]

private lemma actualDifferentialTensorLinearMap_ext_D
    [Algebra R L] {N : Type u} [AddCommGroup N] [Module L N]
    (F G : L ⊗[R] KaehlerDifferential k R →ₗ[L] N)
    (h : ∀ r : R, F ((1 : L) ⊗ₜ[R] KaehlerDifferential.D k R r) =
      G ((1 : L) ⊗ₜ[R] KaehlerDifferential.D k R r)) : F = G := by
  letI : Module R N := Module.compHom N (algebraMap R L)
  letI : IsScalarTower R L N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let u : KaehlerDifferential k R →ₗ[R] L ⊗[R] KaehlerDifferential k R :=
    TensorProduct.mk R L (KaehlerDifferential k R) (1 : L)
  have heq : (F.restrictScalars R).comp u = (G.restrictScalars R).comp u :=
    LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation (R := k) (S := R)) h
  have hOne (x : KaehlerDifferential k R) :
      F ((1 : L) ⊗ₜ[R] x) = G ((1 : L) ⊗ₜ[R] x) :=
    LinearMap.congr_fun heq x
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul a x =>
    have ht : a ⊗ₜ[R] x = a • ((1 : L) ⊗ₜ[R] x) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, F.map_smul, G.map_smul, hOne]

/-- Full comparison of the actual forward map with the pullback of the
actual tilde-adjoint differential sheaf morphism. No IsIso premise. -/
lemma actualAffineGenuineDifferentialForwardPointMap_eq_tildePullback
    (rho : R →+* L) :
    letI : Algebra R L := rho.toAlgebra
    actualAffineGenuineDifferentialForwardPointMap (k := k) rho =
      (((moduleSpecΓFunctor (R := .of L)).map
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).map
          (actualAffineDifferentialTildeToGenuineSheaf (k := k) (R := R)))).hom).comp
        (affineTildeActualPointFiberEquiv (CommRingCat.ofHom rho)
          (ModuleCat.of R (KaehlerDifferential k R))).symm.toLinearMap := by
  dsimp only
  letI : Algebra R L := rho.toAlgebra
  let phi := CommRingCat.ofHom rho
  let M := ModuleCat.of R (KaehlerDifferential k R)
  let O : (Spec (.of R)).Modules := schemeRelativeDifferentials
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  let A := actualAffineDifferentialTildeToGenuineSheaf (k := k) (R := R)
  let P := Scheme.Modules.pullback (Spec.map phi)
  let H := moduleSpecΓFunctor (R := .of L)
  let B : ModuleCat L := H.obj (P.obj ((tilde.functor (.of R)).obj M))
  let N : ModuleCat L := H.obj (P.obj O)
  let E : B ≃ₗ[L] L ⊗[R] KaehlerDifferential k R := affineTildeActualPointFiberEquiv phi M
  let U : B →ₗ[L] N := (H.map (P.map A)).hom
  change actualAffineGenuineDifferentialForwardPointMap (k := k) rho = U.comp E.symm.toLinearMap
  apply actualDifferentialTensorLinearMap_ext_D
  intro r
  let x := KaehlerDifferential.D k R r
  have hE : E.symm ((1 : L) ⊗ₜ[R] x) = affineTildeActualPointClass phi M x := by
    apply E.injective
    exact (E.apply_symm_apply _).trans (affineTildeActualPointFiberEquiv_pointClass phi M x).symm
  have hU : U (affineTildeActualPointClass phi M x) =
      actualAffineSheafPointClass phi O
        (actualRelativeDifferentialSection
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤
          ((Scheme.ΓSpecIso (.of R)).inv.hom r)) :=
    actualAffineDifferentialTildeToGenuineSheaf_point_D rho r
  have hF := actualAffineGenuineDifferentialForwardPointMap_one_tmul_D (k := k) rho r
  change actualAffineGenuineDifferentialForwardPointMap (k := k) rho ((1 : L) ⊗ₜ[R] x) =
    U (E.symm ((1 : L) ⊗ₜ[R] x))
  exact hF.trans ((congrArg (fun z => U z) hE).trans hU).symm

end PfaffianDescent
